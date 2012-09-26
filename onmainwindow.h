
/***************************************************************************
 *   Copyright (C) 2005-2012 by Oleksandr Shneyder                         *
 *   oleksandr.shneyder@obviously-nice.de                                  *
 *                                                                         *
 *   This program is free software; you can redistribute it and/or modify  *
 *   it under the terms of the GNU General Public License as published by  *
 *   the Free Software Foundation; either version 2 of the License, or     *
 *   (at your option) any later version.                                   *
 *                                                                         *
 *   This program is distributed in the hope that it will be useful,       *
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of        *
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *
 *   GNU General Public License for more details.                          *
 *                                                                         *
 *   You should have received a copy of the GNU General Public License     *
 *   along with this program; if not, write to the                         *
 *   Free Software Foundation, Inc.,                                       *
 *   59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.             *
 ***************************************************************************/
#ifndef ONMAINWINDOW_H
#define ONMAINWINDOW_H

#ifdef CFGPLUGIN
#include <QMetaClassInfo>
#include <qtbrowserplugin.h>

#ifdef QAXSERVER
#include <ActiveQt/QAxBindable>
#include <ActiveQt/QAxFactory>
#include <qt_windows.h>
#endif

#endif

#include "x2goclientconfig.h"
//#include "CallbackInterface.h"
#include <QMainWindow>
#include <QList>
#include <QPushButton>
#include <QPixmap>
#include <QProcess>
#include "LDAPSession.h"
#include <QToolBar>
#include <QSystemTrayIcon>


#ifdef Q_OS_WIN
#include <windows.h>
#endif
/**
@author Oleksandr Shneyder
*/

#if defined(CFGPLUGIN) && defined(Q_OS_LINUX)
class QX11EmbedContainer;
#endif
class QToolButton;
class QTemporaryFile;
class QLineEdit;
class QFrame;
class QVBoxLayout;
class QHBoxLayout;
class QScrollArea;
class UserButton;
class QTextEdit;
class SessionButton;
class QLabel;
class QProcess;
class QFile;
class SVGFrame;
class SessionButton;
class QAction;
class QCheckBox;
class QTreeView;
class QModelIndex;
class SshProcess;
class SshMasterConnection;
class IMGFrame;
class QStandardItemModel;
class HttpBrokerClient;
class QMenu;
class QComboBox;
struct user
{
    int uin;
    QString uid;
    QString name;
    QPixmap foto;
    static bool lessThen ( user u1,user u2 )
    {
        return u1.uid < u2.uid;
    }
};

struct directory
{
    QString key;
    QString dstKey;
    QString dirList;
    bool isRemovable;
    SshProcess* proc;
};

struct serv
{
    QString name;
    float factor;
    float sess;
    bool connOk;
    bool operator < ( const struct serv it )
    {
        return ( it.sess < sess );
    }
    static bool lt ( const struct serv it, const struct serv it1 )
    {
        return it.sess<it1.sess;
    }
    QString sshPort;
};

struct Application
{
    QString name;
    QString comment;
    QString exec;
    QPixmap icon;
    enum {MULTIMEDIA, DEVELOPMENT, EDUCATION, GAME,
          GRAPHICS, NETWORK, OFFICE,
          SETTINGS, SYSTEM, UTILITY, OTHER, TOP
         } category;
    static bool lessThen(Application t1, Application t2)
    {
        return (t1.name.compare(t2.name,Qt::CaseInsensitive)<0);
    }
};

struct x2goSession
{
    QString agentPid;
    QString sessionId;
    QString display;
    QString server;
    QString status;
    QString crTime;
    QString cookie;
    QString clientIp;
    QString grPort;
    QString sndPort;
    QString fsPort;
    bool published;
    int colorDepth;
    bool fullscreen;
    enum {DESKTOP,ROOTLESS,SHADOW} sessionType;
    QString command;
    void operator = ( const x2goSession& s );
};

struct ConfigFile
{
    QString session;
    QString user;
    QString brokerUser;
    QString brokerPass;
    QString brokerUserId;
    QString brokerName;
    bool brokerAuthenticated;
    QString iniFile;
    QString server;
    QString sshport;
    QString proxy;
    QString proxyport;
    QString command;
    QString key;
    bool rootless;
    QString cookie;
    QString connectionts;
    QString brokerurl;
    QString sessiondata;
    bool checkexitstatus;
    bool showtermbutton;
    bool showexpbutton;
    bool showextconfig;
    bool showconfig;
    bool showstatusbar;
    bool showtoolbar;

    //if true - use cfg values, else default or client settings
    bool confSnd;
    bool confFS;
    bool confConSpd;
    bool confCompMet;
    bool confImageQ;
    bool confDPI;
    bool confKbd;
    //
    bool useSnd;
    bool useFs;
    int conSpeed;
    QString compMet;
    int imageQ;
    int dpi;
    QString kbdLay;
    QString kbdType;
    //
};


//wrapper to send mouse events under windows in embedded mode
#ifdef Q_OS_WIN
class WWrapper : public QPushButton
{
    friend class ONMainWindow;
};
#include <QThread>
#include <QMutex>
class ONMainWindow;
class WinServerStarter: public QThread
{
public:
    enum daemon {X,SSH,PULSE};
    WinServerStarter ( daemon server, ONMainWindow * par );
    void run();
private:
    daemon mode;
    ONMainWindow* parent;
};
#endif
class ClickLineEdit;
class ONMainWindow : public QMainWindow
#ifdef CFGPLUGIN
    , public QtNPBindable

#ifdef QAXSERVER
    , public QAxBindable
#endif
#endif
{
    friend class HttpBrokerClient;
    friend class SessionButton;
#ifdef CFGPLUGIN
    Q_PROPERTY ( QString x2goconfig READ x2goconfig WRITE setX2goconfig )
    Q_CLASSINFO ( "ClassID", "{5a20006d-118f-4185-9653-9f98958a0008}" )
    Q_CLASSINFO ( "InterfaceID", "{2df000ba-da4f-4fb7-8f35-b8dfbf80009a}" )
    Q_CLASSINFO ( "EventsID", "{44900013-f8bd-4d2e-a2cf-eab407c03005}" )
    Q_CLASSINFO ( "MIME",
                  "application/x2go:x2go:Configuration File "
                  "for X2Go Session" )
    Q_CLASSINFO ( "ToSuperClass", "ONMainWindow" )
    Q_CLASSINFO ( "DefaultProperty","x2goconfig" )
#endif
    Q_OBJECT
public:
    enum
    {
        S_DISPLAY,
        S_STATUS,
        S_COMMAND,
        S_TYPE,
        S_SERVER,
        S_CRTIME,
        S_IP,
        S_ID
    };
    enum
    {
        MODEM,
        ISDN,
        ADSL,
        WAN,
        LAN
    };
    enum
    {
        D_USER,
        D_DISPLAY
    };
    enum
    {
        SHADOW_VIEWONLY,
        SHADOW_FULL
    };
    enum
    {
        PULSE,
        ARTS,
        ESD
    };
    static bool portable;
    ONMainWindow ( QWidget *parent = 0 );
    ~ONMainWindow();
    QString iconsPath ( QString fname );
    const QList<SessionButton*> * getSessionsList()
    {
        return &sessions;
    }
    static bool isServerRunning ( int port );
    void startNewSession();
    void suspendSession ( QString sessId );
    bool termSession ( QString sessId,
                       bool warn=true );
    void setStatStatus ( QString status=QString::null );
    x2goSession getNewSessionFromString ( const QString& string );
    void runCommand();
    long findWindow ( QString text );
    bool retUseLdap()
    {
        return useLdap;
    }
    bool retMiniMode()
    {
        return miniMode;
    }
    QString retLdapServer()
    {
        return ldapServer;
    }
    int retLdapPort()
    {
        return ldapPort;
    }
    QString retLdapDn()
    {
        return ldapDn;
    }
    QString retLdapServer1()
    {
        return ldapServer1;
    }
    int retLdapPort1()
    {
        return ldapPort1;
    }
    QString retLdapServer2()
    {
        return ldapServer2;
    }
    int retLdapPort2()
    {
        return ldapPort2;
    }
    QHBoxLayout* mainLayout()
    {
        return mainL;
    }
    QWidget* mainWidget()
    {
        return ( QWidget* ) fr;
    }

    static bool getPortable()
    {
        return portable;
    }
    static QString getHomeDirectory()
    {
        return homeDir;
    }
    bool getShowAdvOption()
    {
        return config.showextconfig;
    }
    QString getDefaultCmd()
    {
        return defaultCmd;
    }
    QString getDefaultSshPort()
    {
        return defaultSshPort;
    }
    QString getDefaultKbdType()
    {
        return defaultKbdType;
    }
    QStringList getDefaultLayout()
    {
        return defaultLayout;
    }
    QString getDefaultPack()
    {
        return defaultPack;
    }
    int getDefaultQuality()
    {
        return defaultQuality;
    }

    uint getDefaultDPI()
    {
        return defaultDPI;
    }

    bool getDefaultSetDPI()
    {
        return defaultSetDPI;
    }

    bool getEmbedMode()
    {
        return embedMode;
    }

    int getDefaultLink()
    {
        return defaultLink;
    }
    int getDefaultWidth()
    {
        return defaultWidth;
    }
    int getDefaultHeight()
    {
        return defaultHeight;
    }
    bool getDefaultSetKbd()
    {
        return defaultSetKbd;
    }
    bool getDefaultUseSound()
    {
        return defaultUseSound;
    }
    bool getDefaultFullscreen()
    {
        return defaultFullscreen;
    }
    bool sessionEditEnabled()
    {
        return !noSessionEdit;
    }
    const QList<Application>& getApplications()
    {
        return applications;
    }
    static QString getSessionConf()
    {
        return sessionCfg;
    }

    void runApplication(QString exec);


    SshMasterConnection* findServerSshConnection(QString host);

    void showHelp();
    void showHelpPack();
    void exportDirs ( QString exports,bool removable=false );
    void reloadUsers();
    void setWidgetStyle ( QWidget* widget );
    QStringList internApplicationsNames()
    {
        return _internApplicationsNames;
    }
    QStringList transApplicationsNames()
    {
        return _transApplicationsNames;
    }
    QString transAppName ( const QString& internAppName,
                           bool* found=0l );
    QString internAppName ( const QString& transAppName,
                            bool* found=0l );
    void setEmbedSessionActionsEnabled ( bool enable );
    void startSshd();
    QSize getEmbedAreaSize();
#ifdef Q_OS_WIN
    static QString cygwinPath ( const QString& winPath );
    void startXOrg();
    void startPulsed();
    static bool haveCySolEntry();
    static bool haveCygwinEntry();
    static void removeCySolEntry();
    static void removeCygwinEntry();
    static QString U3DevicePath()
    {
        return u3Device;
    }
#endif

private:
    QString m_x2goconfig;
    QStringList _internApplicationsNames;
    QStringList _transApplicationsNames;
    QString portableDataPath;
    bool proxyRunning;
    bool drawMenu;
    bool extStarted;
    bool startMaximized;
    bool startHidden;
    bool defaultUseSound;
    bool defaultXinerama;
    bool cardStarted;
    bool defaultSetKbd;
    bool showExport;
    bool usePGPCard;
    bool miniMode;
    bool managedMode;
    bool brokerMode;
    bool changeBrokerPass;
    bool connTest;
    bool embedMode;
    bool thinMode;
    QString statusString;
    QString autostartApp;
    bool cmdAutologin;
    QString cmdSshKey;
    int defaultLink;
    int defaultQuality;
    int defaultWidth;
    int defaultHeight;
    bool defaultFullscreen;
    bool acceptRsa;
    bool startEmbedded;
    bool extLogin;
    bool printSupport;
    bool showTbTooltip;
    bool noSessionEdit;
    bool cleanAllFiles;
    bool PGPInited;
    bool resumeAfterSuspending;
    QString sshPort;
    QString clientSshPort;
    QString defaultSshPort;
    QVBoxLayout* selectSesDlgLayout;
    SshMasterConnection* sshConnection;
    QList<SshMasterConnection*> serverSshConnections;
    bool closeEventSent;
    int shadowMode;
    QString shadowUser;
    QString shadowDisplay;
    QString defaultPack;
    QStringList defaultLayout;
    QString selectedLayout;
    QString defaultKbdType;
    QString defaultCmd;
    bool defaultSetDPI;
    uint defaultDPI;
    QStringList listedSessions;
    QString appDir;
    QString localGraphicPort;
    static QString homeDir;
    int retSessions;
    QList<serv> x2goServers;
    QList<Application> applications;

    QPushButton* bSusp;
    QPushButton* bTerm;
    QPushButton* bNew;
    QPushButton* bShadow;
    QPushButton* bShadowView;
    QPushButton* bCancel;


    QLabel* selectSessionLabel;
    QTreeView* sessTv;

    QLineEdit* desktopFilter;
    QCheckBox* desktopFilterCb;

    IMGFrame* fr;
    SVGFrame *bgFrame;
    QLineEdit* uname;
    ClickLineEdit* pass;
    ClickLineEdit* login;
    QFrame* uframe;
    SVGFrame *passForm;
    QSize mwSize;
    bool mwMax;
    QPoint mwPos;
    SVGFrame *selectSessionDlg;
    SVGFrame *sessionStatusDlg;
    QLabel* u;
    QLabel* fotoLabel;
    QLabel* nameLabel;
    QLabel* passPrompt;
    QLabel* loginPrompt;
    QLabel* layoutPrompt;
    QLabel* slName;
    QLabel* slVal;
    QComboBox* cbLayout;
    QPushButton* ok;
    QPushButton* cancel;
    QString readExportsFrom;
    QString readLoginsFrom;
    QPushButton* sOk;
    QToolButton* sbSusp;
    QToolButton* sbExp;
    QToolButton* sbTerm;
    QToolButton* sbApps;
    QCheckBox* sbAdv;
    QPushButton* sCancel;
    QString resolution;
    QString kdeIconsPath;
    QScrollArea* users;
    QVBoxLayout* userl;
    QHBoxLayout* mainL;
    QHBoxLayout* bgLay;
    QList<UserButton*> names;
    QList<SessionButton*> sessions;
    UserButton* lastUser;
    SessionButton* lastSession;
    QString prevText;
    QString onserver;
    QString id;
    QString selectedCommand;
    QString currentKey;
    QTimer *exportTimer;
    QTimer *extTimer;
    QTimer *agentCheckTimer;
    QTimer *spoolTimer;
    QTimer *proxyWinTimer;
    QTimer *xineramaTimer;
    short xinSizeInc;
    QRect lastDisplayGeometry;
    QList <QRect> xineramaScreens;
    QStyle* widgetExtraStyle;
    bool isPassShown;
    bool xmodExecuted;
    long proxyWinId;
    bool embedControlChanged;
    bool embedTbVisible;
    QLabel* statusLabel;
    ConfigFile config;
    QStandardItemModel* model;
    QStandardItemModel* modelDesktop;

    QAction *act_set;
    QAction *act_abclient;
    QAction *act_support;
    QAction *act_shareFolder;
    QAction *act_suspend;
    QAction *act_terminate;
    QAction *act_reconnect;
    QAction *act_embedContol;
    QAction *act_embedToolBar;
    QAction *act_changeBrokerPass;
    QAction *act_testCon;
    QList <QAction*> topActions;

    QToolBar *stb;

    QString sessionStatus;
    QString spoolDir;
    QString sessionRes;
    QHBoxLayout* username;
    QList <user> userList;
    QList <directory> exportDir;
    QString nick;
    QString nfsPort;
    QString mntPort;
    static QString sessionCfg;
    QProcess* ssh;
    QProcess* soundServer;
    QProcess* scDaemon;
    QProcess* gpgAgent;
    QProcess* gpg;
    LDAPSession* ld;
    long embedParent;
    long embedChild;
    bool proxyWinEmbedded;
    bool useLdap;
    bool showToolBar;
    bool showHaltBtn;
    bool newSession;
    bool runStartApp;
    bool ldapOnly;
    bool isScDaemonOk;
    bool parecTunnelOk;
#ifdef Q_OS_LINUX
    bool directRDP;
#endif

    bool startSessSound;
    int startSessSndSystem;

    bool fsInTun;
    bool fsTunReady;

    QString fsExportKey;
    bool fsExportKeyReady;

    QString ldapServer;
    int ldapPort;
    QString ldapServer1;
    int ldapPort1;
    QString ldapServer2;
    int ldapPort2;
    QString ldapDn;
    QString sessionCmd;

    QString supportMenuFile;
    QString BGFile;
    QString SPixFile;

    QString LDAPSndSys;
    QString LDAPSndPort;
    bool LDAPSndStartServer;

    bool  LDAPPrintSupport;

    QAction *act_edit;
    QAction *act_new;
    QAction *act_sessicon;
    QProcess *nxproxy;
#ifndef Q_OS_WIN
    QProcess *sshd;
    bool userSshd;
#else
    QProcess *xorg;
    PROCESS_INFORMATION sshd;
    bool winSshdStarted;
    static QString u3Device;

    QProcess* pulseServer;
    QStringList pulseArgs;
    QTimer* pulseTimer;
    int xDisplay;
    int sshdPort;
    bool winServersReady;
    QString oldEtcDir;
    QString oldBinDir;
    QString oldTmpDir;

    bool cySolEntry;
    bool cyEntry;

    QString pulseDir;
    int pulsePort;
    int esdPort;
    bool maximizeProxyWin;
    int proxyWinWidth;
    int proxyWinHeight;
    QTimer* xorgLogTimer;
    QString xorgLogFile;
    QMutex xorgLogMutex;
#endif
    QString lastFreeServer;
    QString cardLogin;
    QTextEdit* stInfo;

    SVGFrame* ln;
    SshProcess* tunnel;
    SshProcess* sndTunnel;
    SshProcess* fsTunnel;
    QList<x2goSession> selectedSessions;
    QStringList selectedDesktops;
    x2goSession resumingSession;
    bool startSound;
    bool restartResume;
    bool runRemoteCommand;
    bool shadowSession;
    int firstUid;
    int lastUid;
    QStringList sshEnv;
    QString agentPid;
    bool cardReady;
    HttpBrokerClient* broker;


#if defined ( Q_OS_WIN) //&& defined (CFGCLIENT )
    void xorgSettings();
    bool startXorgOnStart;
    bool useInternalX;
    enum {VCXSRV, XMING} internalX;
    QString xorgExe;
    QString xorgOptions;
    QString xorgWinOptions;
    QString xorgFSOptions;
    QString xorgSAppOptions;
    enum {WIN,FS,SAPP} xorgMode;
    QString xorgWidth;
    QString xorgHeight;
    int waitingForX;
    QRect dispGeometry;
#endif

#ifdef Q_OS_LINUX
    long image, shape;
#endif

    // Tray icon stuff based on patch from Joachim Langenbach <joachim@falaba.de>
    QSystemTrayIcon *trayIcon;
    QMenu *trayIconMenu;
    QMenu *trayIconActiveConnectionMenu;

    QAction* appSeparator;
    QMenu* appMenu[Application::OTHER+1];

    bool trayEnabled;
    bool trayMinToTray;
    bool trayNoclose;
    bool trayMinCon;
    bool trayMaxDiscon;
    bool trayAutoHidden;

    void installTranslator();
    void loadSettings();
    void showPass ( UserButton* user );
    void clean();
    bool defaultSession;
    QString defaultSessionName;
    QString defaultSessionId;
    QString defaultUserName;
    bool defaultUser;
    SessionButton* createBut ( const QString& id );
    void placeButtons();
    QString getKdeIconsPath();
    QString findTheme ( QString theme );
    bool initLdapSession ( bool showBox=true );
    bool startSession ( const QString& id );
    x2goSession getSessionFromString ( const QString& string );
    void resumeSession ( const x2goSession& s );
    void selectSession ( QStringList& sessions );
    x2goSession getSelectedSession();
    bool parseParameter ( QString param );
    bool linkParameter ( QString value );
    bool geometry_par ( QString value );
    bool setKbd_par ( QString value );
    bool ldapParameter ( QString value );
    bool ldap1Parameter ( QString value );
    bool ldap2Parameter ( QString value );
    bool packParameter ( QString value );
    bool soundParameter ( QString val );
    void printError ( QString param );
    void exportDefaultDirs();
    QString createRSAKey();
    directory* getExpDir ( QString key );
    bool findInList ( const QString& uid );
    void setUsersEnabled ( bool enable );
    void externalLogout ( const QString& logoutDir );
    void externalLogin ( const QString& loginDir );
    void startGPGAgent ( const QString& login,
                         const QString& appId );
    void closeClient();
    void continueNormalSession();
    void continueLDAPSession();
    SshMasterConnection* startSshConnection ( QString host, QString port,
            bool acceptUnknownHosts, QString login,
            QString password, bool autologin, bool krbLogin, bool getSrv=false);
    void setProxyWinTitle();
    QRect proxyWinGeometry();
    void readApplications();
    void removeAppsFromTray();
    void plugAppsInTray();
    QMenu* initTrayAppMenu(QString text, QPixmap icon);


protected:
    virtual void closeEvent ( QCloseEvent* event );
    virtual void hideEvent ( QHideEvent* event);

#ifndef Q_OS_WIN
    virtual void mouseReleaseEvent ( QMouseEvent * event );
#else
private slots:
    void slotSetWinServersReady();
    void startWinServers();
    void slotCheckXOrgLog();
    void slotCheckXOrgConnection();
    void slotCheckPulse();
#endif
private slots:
    void slotAppDialog();
    void slotShowPassForm();
    void displayUsers();
    void slotAppMenuTriggered ( QAction * action );
    void slotPassChanged(const QString& result);
    void slotResize ( const QSize sz );
    void slotUnameChanged ( const QString& text );
    void slotPassEnter();
    void slotChangeBrokerPass();
    void slotTestConnection();
    void slotCheckPortableDir();
    void readUsers();
    void slotSelectedFromList ( UserButton* user );
    void slotUnameEntered();
    void slotClosePass();
    void slotReadSessions();
    void slotManage();
    void displayToolBar ( bool );
    void showSessionStatus();
    void slotSshConnectionError ( QString message, QString lastSessionError );
    void slotSshServerAuthError ( int error, QString sshMessage, SshMasterConnection* connection );
    void slotSshServerAuthPassphrase ( SshMasterConnection* connection );
    void slotSshUserAuthError ( QString error );
    void slotSshConnectionOk();
    void slotServSshConnectionOk(QString server);
    void slotChangeKbdLayout(const QString& layout);
    void slotSyncX();
    void slotShutdownThinClient();
    void slotReadApplications(bool result, QString output, SshProcess* proc );

public slots:
    void slotConfig();
    void slotNewSession();
    void slotDeleteButton ( SessionButton * bt );
    void slotEdit ( SessionButton* );
    void slotCreateDesktopIcon ( SessionButton* bt );
    void exportsEdit ( SessionButton* bt );
    void slotEmbedControlAction();
    void slotDetachProxyWindow();
    void slotActivateWindow();

private slots:
    void slotSnameChanged ( const QString& );
    void slotSelectedFromList ( SessionButton* session );
    void slotSessEnter();
    void slotCloseSelectDlg();
    void slotActivated ( const QModelIndex& index );
    void slotResumeSess();
    void slotSuspendSess();
    void slotTermSessFromSt();
    void slotSuspendSessFromSt();
    void slotTermSess();
    void slotNewSess();
    void slotGetBrokerAuth();
    void slotGetBrokerSession(const QString& sinfo);
    void slotCmdMessage ( bool result,QString output,
                          SshProcess* );
    void slotListSessions ( bool result,QString output,
                            SshProcess* );
    void slotRetSuspSess ( bool value,QString message,
                           SshProcess* );
    void slotRetTermSess ( bool result,QString output,
                           SshProcess* );
    void slotRetResumeSess ( bool result,QString output,
                             SshProcess* );
    void slotTunnelFailed ( bool result,QString output,
                            SshProcess* );
    void slotFsTunnelFailed ( bool result,QString output,
                              SshProcess* );
    void slotSndTunnelFailed ( bool result,QString output,
                               SshProcess* );
    void slotCopyKey ( bool result,QString output,SshProcess* );
    void slotTunnelOk();
    void slotFsTunnelOk();
    void slotProxyError ( QProcess::ProcessError err );
    void slotProxyFinished ( int result,QProcess::ExitStatus st );
    void slotProxyStderr();
    void slotProxyStdout();
    void slotResumeDoubleClick ( const QModelIndex& );
    void slotShowAdvancedStat();
    void slotRestartProxy();
    void slotTestSessionStatus();
    void slotRetRunCommand ( bool result, QString output,
                             SshProcess* );
    void slotGetServers ( bool result, QString output,
                          SshProcess* );
    void slotListAllSessions ( bool result,QString output,
                               SshProcess* );
    void slotRetExportDir ( bool result,QString output,
                            SshProcess* );
    void slotResize();
    void slotExportDirectory();
    void slotExportTimer();
    void slotAboutQt();
    void slotAbout();
    void slotSupport();

    //trayIcon stuff
    void trayIconActivated(QSystemTrayIcon::ActivationReason reason);
    void trayMessageClicked();
    void trayQuit();
    void trayIconInit();


private slots:
    void slotSetProxyWinFullscreen();
    void slotCheckPrintSpool();
    void slotRereadUsers();
    void slotExtTimer();
    void slotStartPGPAuth();
    void slotScDaemonOut();
    void slotScDaemonError();
    void slotGpgFinished ( int exitCode,
                           QProcess::ExitStatus exitStatus );
    void slotScDaemonFinished ( int exitCode,
                                QProcess::ExitStatus exitStatus );
    void slotGpgError();
    void slotCheckScDaemon();
    void slotGpgAgentFinished ( int exitCode,
                                QProcess::ExitStatus exitStatus );
    void slotCheckAgentProcess();
    void slotExecXmodmap();
    void slotCreateSessionIcon();
    void slotFindProxyWin();
    void slotConfigXinerama();
    void slotXineramaConfigured();
    void slotAttachProxyWindow();
    void slotEmbedIntoParentWindow();
    void slotEmbedWindow();
    void slotStartParec ();
    void slotSndTunOk();
    void slotPCookieReady (	bool result,QString output,
                            SshProcess* proc );
    void slotEmbedToolBar();
    void slotEmbedToolBarToolTip();
    void slotHideEmbedToolBarToolTip();
    void slotDesktopFilterChanged ( const QString& text ) ;
    void slotDesktopFilterCb ( int state ) ;
    void slotShadowViewSess();
    void slotShadowSess();
    void slotReconnectSession();
    void slotStartBroker();
    void slotStartNewBrokerSession ();

private:
    void resizeProxyWinOnDisplay(int display);
#ifdef Q_OS_LINUX
    long X11FindWindow ( QString text, long rootWin=0 );
#endif
    void addToAppNames ( QString intName, QString transName );
    bool checkAgentProcess();
    bool isColorDepthOk ( int disp, int sess );
    void check_cmd_status();
    int startSshFsTunnel();
    void startX2goMount();
    void cleanPrintSpool();
    void cleanAskPass();
    void initWidgetsEmbed();
    void initWidgetsNormal();
    QString getCurrentUname();
    QString getCurrentPass();
    void processSessionConfig();
    void processCfgLine ( QString line );
    void initSelectSessDlg();
    void initStatusDlg();
    void initPassDlg();
    void printSshDError();
    void loadPulseModuleNativeProtocol();
    void initEmbedToolBar();
#ifdef Q_OS_LINUX
    void startDirectRDP();
#endif
    void filterDesktops ( const QString& filter,
                          bool strict=false );
    void generateHostDsaKey();
    void generateEtcFiles();
    QString u3DataPath();
    void cleanPortable();
    void removeDir ( QString path );
#ifdef Q_OS_WIN
    void saveCygnusSettings();
    void restoreCygnusSettings();
#endif
#if defined  (Q_OS_WIN) || defined (Q_OS_DARWIN)
    QString getXDisplay();
#endif

////////////////plugin stuff////////////////////
#ifdef CFGPLUGIN
public slots:
    void setX2goconfig ( const QString& text );
public:
    QString x2goconfig() const
    {
        return m_x2goconfig;
    }

#ifndef Q_OS_DARWIN
public:
    void embedWindow ( long wndId );
    void detachClient();
private:
    long parentId;
    long childId;
    QSize oldParentSize;

#ifdef Q_OS_LINUX
    QX11EmbedContainer* embedContainer;
#endif
#ifdef Q_OS_WIN
    QWidget* embedContainer;
    QPoint oldParentPos;
    QPoint oldChildPos;
    QSize oldContainerSize;
    QTimer *updateTimer;
    int gcor;
    long winFlags;
#endif
private:
    QSize getWindowSize ( long winId );
    void doPluginInit();

#ifdef Q_OS_WIN
private slots:
    void slotUpdateEmbedWindow();
#endif

#endif //(Q_OS_DARWIN)
#endif
////////////////end of plugin stuff////////////////////
};

#endif
