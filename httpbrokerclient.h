//
// C++ Interface: httpbrokerclient
//
// Description:
//
//
// Author: Oleksandr Shneyder <oleksandr.shneyder@obviously-nice.de>, (C) 2010
//
// Copyright: See COPYING file that comes with this distribution
//
//
#ifndef HTTPBROKERCLIENT_H
#define HTTPBROKERCLIENT_H
#include "x2goclientconfig.h"
#include <QSslError>
#include <QBuffer>
#include <QObject>
/**
	@author Oleksandr Shneyder <oleksandr.shneyder@obviously-nice.de>
*/
class QHttp;
struct ConfigFile;
class ONMainWindow;

class HttpBrokerClient: public QObject
{
    Q_OBJECT
public:
    HttpBrokerClient ( ONMainWindow* wnd, ConfigFile* cfg );
    ~HttpBrokerClient();
    QString getSInfoFromBroker ( bool getKey=false );
    void selectUserSession(const QString& session );
    void changePassword(QString newPass);
private:
    QBuffer httpSIAnswer;
    QBuffer httpCmdAnswer;
    QBuffer httpSessionAnswer;
    QHttp* http;
    int sinfoRequest;
    int sinfoKeyRequest;
    int sessionsRequest;
    int selSessRequest;
    int cmdRequest;
    int chPassRequest;
    QString newBrokerPass;
    ConfigFile* config;
    ONMainWindow* mainWindow;
    void createIniFile(const QString& content);

private slots:
    void slotRequestFinished ( int id, bool error );
    void slotSslErrors ( const QList<QSslError> & errors ) ;
    QString getHexVal ( const QByteArray& ba );
    void slotGetConnectionCmd();
public slots:
    void getUserSessions();

signals:
    void haveSshKey ( QString );
    void fatalHttpError();
    void haveAgentInfo ();
    void cmdReconnect ();
    void authFailed();
    void sessionsLoaded();
    void getSession( QString );
    void passwordChanged( QString );
};

#endif
