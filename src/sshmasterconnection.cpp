/**************************************************************************
*   Copyright (C) 2005-2016 by Oleksandr Shneyder                         *
*   o.shneyder@phoca-gmbh.de                                              *
*                                                                         *
*   This program is free software; you can redistribute it and/or modify  *
*   it under the terms of the GNU General Public License as published by  *
*   the Free Software Foundation; either version 2 of the License, or     *
*   (at your option) any later version.                                   *
*   This program is distributed in the hope that it will be useful,       *
*   but WITHOUT ANY WARRANTY; without even the implied warranty of        *
*   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *
*   GNU General Public License for more details.                          *
*                                                                         *
*   You should have received a copy of the GNU General Public License     *
*   along with this program.  If not, see <http://www.gnu.org/licenses/>. *
***************************************************************************/

#include "x2goclientconfig.h"
#include "x2gologdebug.h"
#include "sshmasterconnection.h"
#include <stdlib.h>
#include <stdio.h>
#include "sshprocess.h"


#include <QStringList>
#include <QFile>
#include <QDir>
#include <QTemporaryFile>
#ifndef Q_OS_WIN
#include <arpa/inet.h>
#endif
#include <math.h>

#include <QUuid>

#ifndef Q_OS_WIN
#include <sys/socket.h> /* for socket(), connect(), send(), and recv() */
#include <arpa/inet.h>  /* for sockaddr_in and inet_addr() */
#include <arpa/inet.h>
#include <netinet/tcp.h>
#include <QtNetwork/qabstractsocket.h>
#endif


#include "onmainwindow.h"


#define PROXYTUNNELPORT 44444

#define DEBUG

#undef SSH_DEBUG
// #define SSH_DEBUG

static bool isLibSshInited=false;

const QString SshMasterConnection::challenge_auth_code_prompts_[] = {
  "Verification code:",
  "One-time password (OATH) for"
};


#ifdef Q_OS_WIN
#include <QSettings>
// parse known_hosts file from libssh and export keys in registry to use with plink.exe
void SshMasterConnection::parseKnownHosts()
{
    QFile fl(mainWnd->getHomeDirectory()+"/ssh/known_hosts");
    if (!fl.open(QFile::ReadOnly))
        return;
    QSettings settings("HKEY_CURRENT_USER\\Software\\SimonTatham\\PuTTY\\SshHostKeys",
                       QSettings::NativeFormat);
    while (!fl.atEnd())
    {
        QString line=fl.readLine();
        QStringList parts=line.split(' ',QString::SkipEmptyParts);
        if (parts.count()!=3)
            continue;

        //lines in known_hosts have format:
        //[host]:port <ssh-rsa|ssh-dss> <key>
        //we proceeding only lines from libssh - no hashed hostnames
        //or patterns are allowed

        QString type="unknown";
        QString port="22";
        if (parts[1]=="ssh-dss")
            type="dss";
        if (parts[1]=="ssh-rsa")
            type="rsa2";


        QStringList hostParts=parts[0].split(":",QString::SkipEmptyParts);
        if (hostParts.count()>1)
            port=hostParts[1];
        hostParts[0].replace("[","");
        hostParts[0].replace("]","");

        QString keyName=type+"@"+port+":"+hostParts[0];

        QByteArray bytes=QByteArray::fromBase64(parts[2].toAscii());
        QStringList fields;

        //key is a set of data fields:
        //[size][data][size][data].....[size][data]

        for (int i=0; i<bytes.count();)
        {
            int size=0;
            //first 4 bytes are for size of data field (big-endian)
            for (int j=0; j<4; ++j)
            {
                size+=((uchar)(bytes[i])) * pow((float)256,3-j);
                i++;
            }
            QByteArray data;
            data=bytes.mid(i,size);
            QString hex;

            for (int j=0; j<data.count(); ++j)
            {
                QString byte;
                byte.sprintf("%02x",(uchar)(data[j]));
                hex+=byte;
            }
            //remove leading '0'
            for (;;)
            {
                if (hex.length()==0)
                    break;
                if (hex[0]=='0')
                    hex.remove(0,1);
                else
                    break;
            }
            hex="0x"+hex;
            fields<<hex;
            i+=size;
        }
        //first element is a type of key, we don't need it
        fields.removeFirst();
        settings.setValue(keyName,fields.join(","));
#ifdef DEBUG
        x2goDebug<<"Writing key to registry: HKEY_CURRENT_USER\\Software\\SimonTatham\\PuTTY\\SshHostKeys"<<endl;
        x2goDebug<<keyName<<"="<<fields.join(",")<<endl;
#endif
    }
    settings.sync();
}
#endif


SshMasterConnection::SshMasterConnection (QObject* parent, QString host, int port, bool acceptUnknownServers, QString user,
        QString pass, QString key, bool autologin, bool krblogin,
        bool useproxy, ProxyType type, QString proxyserver, quint16 proxyport,
        QString proxylogin, QString proxypassword, QString proxykey,
        bool proxyautologin, bool proxyKrbLogin ) : QThread ( parent )
{
#if defined ( Q_OS_DARWIN )
    // Mac OS X provides only 512KB stack space for secondary threads.
    // As we put a 512KB buffer on the stack later on, we need a bigger stack space.
    setStackSize (sizeof (char) * 1024 * 1024 * 2);
#endif
    tcpProxySocket = NULL;
    tcpNetworkProxy = NULL;
    sshProxy= NULL;
    sshProxyReady=false;
    nextPid=0;

    breakLoop=false;
    kerberosDelegation=false;
    x2goDebug << "SshMasterConnection, host " << host << "port " << port << "user " << user
              << "useproxy " << useproxy << "proxyserver " << proxyserver
              << "proxyport " << proxyport;
    this->host=host;
    this->port=port;
    this->user=user;
    this->pass=pass;
    this->key=key;
    this->autologin=autologin;
    this->acceptUnknownServers=acceptUnknownServers;
    this->useproxy=useproxy;
    this->proxytype=type;
    this->proxyautologin=proxyautologin;
    this->proxykey=proxykey;
    this->proxyserver=proxyserver;
    this->proxyport=proxyport;
    this->proxylogin=proxylogin;
    this->proxypassword=proxypassword;
    this->proxyKrbLogin=proxyKrbLogin;
    mainWnd=(ONMainWindow*) parent;
    kerberos=krblogin;
    challengeAuthVerificationCode=QString::null;
    if(this->user==QString::null||this->user.length()<=0)
    {
#ifdef Q_OS_WIN
        this->user=getenv("USERNAME");
#else
        this->user=getenv("USER");
#endif
    }
#ifdef DEBUG
    if (kerberos)
    {
        x2goDebug<<"Starting SSH connection with Kerberos authentication.";
    }
    else
    {
        x2goDebug<<"Starting SSH connection without Kerberos authentication.";
    }
#endif
#ifdef DEBUG
    x2goDebug<<"SshMasterConnection, instance "<<this<<" created.";
#endif
}


void SshMasterConnection::slotSshProxyConnectionOk()
{
#ifdef DEBUG
    x2goDebug<<"SSH proxy connected.";
#endif


    localProxyPort=PROXYTUNNELPORT;
    while ( ONMainWindow::isServerRunning ( localProxyPort ) )
        ++localProxyPort;

    sshProxy->startTunnel ( host, port, "127.0.0.1",localProxyPort,false,this, SLOT ( slotSshProxyTunnelOk(int)),
                            SLOT ( slotSshProxyTunnelFailed(bool,QString,int)));

}


int SshMasterConnection::copyFile(const QString& src, const QString dst, QObject* receiver, const char* slotFinished)
{
    SshProcess* proc=new SshProcess(this, nextPid++);
    if(receiver && slotFinished)
    {
        connect(proc, SIGNAL(sshFinished(bool,QString,int)), receiver, slotFinished);
    }
    proc->start_cp(src,dst);
    processes<<proc;
    return proc->pid;
}

int SshMasterConnection::executeCommand(const QString& command, QObject* receiver, const char* slotFinished)
{
    SshProcess* proc=new SshProcess(this, nextPid++);
    if(receiver && slotFinished)
    {
        connect(proc, SIGNAL(sshFinished(bool,QString,int)), receiver, slotFinished);
    }
    proc->startNormal(command);
    processes<<proc;
    return proc->pid;

}

QString SshMasterConnection::getSourceFile(int pid)
{
    foreach (SshProcess* proc, processes)
    {
        if(proc->pid==pid)
            return proc->getSource();
    }
    return QString ::null;
}


void SshMasterConnection::addReverseTunnelConnections()
{
    reverseTunnelRequestMutex.lock();
    for(int i=0; i<reverseTunnelRequest.count(); ++i)
    {
        if(!reverseTunnelRequest[i].listen)
        {
            reverseTunnelRequest[i].listen=true;
            int rc=ssh_forward_listen(my_ssh_session, NULL, reverseTunnelRequest[i].forwardPort, NULL);
            if(rc==SSH_OK)
            {
                emit reverseTunnelOk(reverseTunnelRequest[i].creator);
#ifdef DEBUG
                x2goDebug<<"Listening for TCP/IP connections on "<<reverseTunnelRequest[i].forwardPort;
#endif
            }
            if(rc==SSH_ERROR)
            {
                QString err=ssh_get_error(my_ssh_session);
#ifdef DEBUG
                x2goDebug<<"Forward port "<<reverseTunnelRequest[i].forwardPort<<" failed:"<<err;
#endif
                emit reverseTunnelFailed(reverseTunnelRequest[i].creator, err);
            }
        }
    }
    reverseTunnelRequestMutex.unlock();
}

void SshMasterConnection::checkReverseTunnelConnections()
{
    int port;
    ssh_channel chan=ssh_channel_accept_forward(my_ssh_session, 0, &port);
    if(chan)
    {
#ifdef DEBUG
        x2goDebug<<"New reverse connection on port "<<port;
#endif

        reverseTunnelRequestMutex.lock();
        for(int i=0; i<reverseTunnelRequest.count(); ++i)
        {
            ReverseTunnelRequest req=reverseTunnelRequest[i];
            if (static_cast<int> (req.forwardPort) == port)
            {
#ifdef DEBUG
                x2goDebug<<"Creating new channel for reverse tunnel "<<port;
#endif
                int sock=socket ( AF_INET, SOCK_STREAM,0 );
#ifndef Q_OS_WIN
                const int y=1;
#else
                const char y=1;
#endif
                setsockopt(sock, IPPROTO_TCP, TCP_NODELAY,&y, sizeof(int));

                struct sockaddr_in address;
                address.sin_family=AF_INET;
                address.sin_port=htons ( req.localPort );
#ifdef DEBUG
                x2goDebug<<"Connecting to "<<req.localHost<<":"<<req.localPort<<endl;
#endif
#ifndef Q_OS_WIN
                inet_aton ( req.localHost.toAscii(), &address.sin_addr );
#else
                address.sin_addr.s_addr=inet_addr (
                                            req.localHost.toAscii() );
#endif

                if ( ::connect ( sock, ( struct sockaddr * ) &address,sizeof ( address ) ) !=0 )
                {
                    QString errMsg=tr ( "Cannot connect to " ) +
                                   req.localHost+":"+QString::number ( req.localPort );
#ifdef DEBUG
                    x2goDebug<<errMsg<<endl;
#endif
                    emit ioErr ( req.creator, errMsg, "" );
                    break;
                }

                ChannelConnection con;
                con.channel=chan;
                con.sock=sock;
                con.creator=req.creator;
                channelConnectionsMutex.lock();
                channelConnections<<con;
                channelConnectionsMutex.unlock();
#ifdef DEBUG
                x2goDebug<<"New channel created";
#endif
                break;
            }
        }
        reverseTunnelRequestMutex.unlock();


    }
}


int SshMasterConnection::startTunnel(const QString& forwardHost, uint forwardPort, const QString& localHost, uint localPort, bool reverse,
                                     QObject* receiver, const char* slotTunnelOk, const char* slotFinished)
{
    SshProcess* proc=new SshProcess(this, nextPid++);
    if(receiver && slotFinished)
    {
        connect(proc, SIGNAL(sshFinished(bool,QString,int)), receiver, slotFinished);
    }
    if(receiver && slotTunnelOk)
    {
        connect(proc, SIGNAL(sshTunnelOk(int)), receiver, slotTunnelOk);
    }
    proc->startTunnel(forwardHost, forwardPort, localHost, localPort, reverse);
    if(reverse && !kerberos)
    {
        connect(this, SIGNAL(reverseTunnelOk(SshProcess*)), proc, SLOT(slotReverseTunnelOk(SshProcess*)));
        connect(this, SIGNAL(reverseTunnelFailed(SshProcess*,QString)), proc, SLOT(slotReverseTunnelFailed(SshProcess*,QString)));
        ReverseTunnelRequest req;
        req.creator=proc;
        req.localPort=localPort;
        req.localHost=localHost;
        req.forwardPort=forwardPort;
        req.listen=false;
#ifdef DEBUG
        x2goDebug<<"Requesting reverse tunnel from port "<<forwardPort<< " to "<<localPort;
#endif
        reverseTunnelRequestMutex.lock();
        reverseTunnelRequest<<req;
        reverseTunnelRequestMutex.unlock();
    }
    processes<<proc;
    return proc->pid;
}


void SshMasterConnection::slotSshProxyConnectionError(QString err1, QString err2)
{
    breakLoop=true;
    emit connectionError(tr("SSH proxy connection error."),err1+" "+err2);
}

void SshMasterConnection::slotSshProxyServerAuthError(int errCode, QString err, SshMasterConnection* con)
{
    emit serverAuthError(errCode, tr("SSH proxy connection error: ")+err, con);
}

void SshMasterConnection::slotSshProxyUserAuthError(QString err)
{
    breakLoop=true;
    emit userAuthError(tr("SSH proxy connection error: ")+err);
}


void SshMasterConnection::slotSshProxyTunnelOk(int)
{
#ifdef DEBUG
    x2goDebug<<"SSH proxy tunnel established.";
#endif
    sshProxyReady=true;
}

void SshMasterConnection::slotSshProxyTunnelFailed(bool ,  QString output,
        int)
{
    breakLoop=true;
    emit connectionError(tr("Failed to create SSH proxy tunnel."), output);
}



void SshMasterConnection::slotSshProxyServerAuthAborted()
{
    breakLoop=true;
}

void SshMasterConnection::run()
{
#ifdef DEBUG
    x2goDebug<<"SshMasterConnection, instance "<<this<<" entering thread.";
#endif
    if(useproxy && proxytype==PROXYSSH)
    {
        x2goDebug << "proxyserver: " << proxyserver << "proxyport: " << proxyport << "proxylogin: " << proxylogin;
        sshProxy=new SshMasterConnection (0, proxyserver, proxyport,acceptUnknownServers,
                                          proxylogin, proxypassword, proxykey, proxyautologin, proxyKrbLogin, false);
        connect ( sshProxy, SIGNAL ( connectionOk(QString) ), this, SLOT ( slotSshProxyConnectionOk() ) );

        connect ( sshProxy, SIGNAL ( serverAuthError ( int,QString,SshMasterConnection* ) ),this,
                  SLOT ( slotSshProxyServerAuthError ( int,QString, SshMasterConnection* ) ) );
        connect ( sshProxy, SIGNAL ( needPassPhrase(SshMasterConnection*, bool)),this,
                  SIGNAL ( needPassPhrase(SshMasterConnection*, bool)) );
        connect ( sshProxy, SIGNAL ( serverAuthAborted()),this,
                  SLOT ( slotSshProxyServerAuthAborted()) );
        connect ( sshProxy, SIGNAL ( userAuthError ( QString ) ),this,SLOT ( slotSshProxyUserAuthError ( QString ) ) );
        connect ( sshProxy, SIGNAL ( connectionError ( QString,QString ) ), this,
                  SLOT ( slotSshProxyConnectionError ( QString,QString ) ) );

        sshProxyReady=false;
        sshProxy->start();

        while(! sshProxyReady)
        {
            if(breakLoop)
            {
                quit();
                return;
            }
            this->usleep(200);
        }
    }
    disconnectSessionFlag=false;
    if ( !isLibSshInited )
    {
#ifdef DEBUG
        x2goDebug<<"libssh not initialized yet. Initializing.";
#endif
        if ( ssh_init() !=0 )
        {
            QString err=tr ( "Cannot initialize libssh." );
#ifdef DEBUG
            x2goDebug<<err<<endl;
#endif
            emit connectionError ( err,"" );
            quit();
            return;
        }
        isLibSshInited=true;
    }
#ifdef DEBUG
    else
    {
        x2goDebug<<"libssh already initialized.";
    }
#endif

#ifdef SSH_DEBUG
    int verbosity=SSH_LOG_PACKET;
#else
    int verbosity=SSH_LOG_NOLOG;
#endif

    long timeout = 60;

    my_ssh_session = ssh_new();
    if ( my_ssh_session == NULL )
    {
        QString err=tr ( "Cannot create SSH session." );
#ifdef DEBUG
        x2goDebug<<err<<endl;
#endif
        emit connectionError ( err,"" );
        quit();
        return;
    }

#ifdef Q_OS_WIN
    ssh_options_set ( my_ssh_session, SSH_OPTIONS_SSH_DIR, (mainWnd->getHomeDirectory()+"/ssh").toLocal8Bit());
#ifdef DEBUG
    x2goDebug<<"Setting SSH directory to "<<(mainWnd->getHomeDirectory()+"/ssh").toLocal8Bit();
#endif
    if (kerberos)
    {
        parseKnownHosts();
    }

#endif
    ssh_options_set(my_ssh_session, SSH_OPTIONS_LOG_VERBOSITY, &verbosity);

    ssh_options_set(my_ssh_session, SSH_OPTIONS_TIMEOUT, &timeout);

    if (useproxy && proxytype == PROXYHTTP)
    {
        socket_t proxysocket = SSH_INVALID_SOCKET;

        tcpNetworkProxy = new QNetworkProxy( QNetworkProxy::HttpProxy,
                                             proxyserver, proxyport, proxylogin, proxypassword);
        tcpProxySocket = new QTcpSocket();
        tcpProxySocket->setProxy( *tcpNetworkProxy );
        tcpProxySocket->connectToHost(host, port);
        if (!tcpProxySocket->waitForConnected(30000))
        {
            QString message=tr ( "Cannot connect to proxy server." );
#ifdef DEBUG
            x2goDebug<<message<<endl;
#endif
            emit connectionError ( "Proxy", message );
            ssh_free ( my_ssh_session );
            quit();
            return;
        }
        proxysocket = tcpProxySocket->socketDescriptor();
#ifdef DEBUG
        x2goDebug << "Created HTTP proxy socket: " << proxysocket << endl;
#endif
        ssh_options_set( my_ssh_session, SSH_OPTIONS_FD, &proxysocket);
        ssh_set_fd_toread( my_ssh_session);
#ifdef DEBUG
        x2goDebug<<"Connected to HTTP proxy server: " << proxyserver << ":"
                 << proxyport <<endl;
#endif
    }

    if ( !sshConnect() )
    {
        if(disconnectSessionFlag)
        {
#ifdef DEBUG
            x2goDebug<<"Session is already disconnected, exiting."<<endl;
#endif
            return;
        }
        QString err=ssh_get_error ( my_ssh_session );
        QString message=tr ( "Cannot connect to " ) +host+":"+QString::number ( port );
#ifdef DEBUG
        x2goDebug<<message<<" - "<<err;
#endif
        emit connectionError ( message, err );
        ssh_free ( my_ssh_session );
        quit();
        return;
    }
    if(disconnectSessionFlag)
    {
#ifdef DEBUG
        x2goDebug<<"Session is already disconnected, exiting."<<endl;
#endif
        return;
    }
    QString errMsg;
    int state=serverAuth ( errMsg );
    if ( state != SSH_SERVER_KNOWN_OK )
    {
        if(disconnectSessionFlag)
        {
#ifdef DEBUG
            x2goDebug<<"Session is already disconnected, exiting."<<endl;
#endif
            return;
        }
        writeHostKey=writeHostKeyReady=false;
        emit serverAuthError ( state,errMsg, this );
        for(;;)
        {
            this->usleep(100);
            writeHostKeyMutex.lock();
            if(writeHostKeyReady)
            {
                if(writeHostKey)
                    ssh_write_knownhost(my_ssh_session);
                writeHostKeyMutex.unlock();
                break;
            }
            writeHostKeyMutex.unlock();
        }
        ssh_disconnect ( my_ssh_session );
        ssh_free ( my_ssh_session );
        return;
    }

    if(disconnectSessionFlag)
    {
#ifdef DEBUG
        x2goDebug<<"Session is already disconnected, exiting."<<endl;
#endif
        return;
    }

#ifdef Q_OS_WIN
    ssh_options_set ( my_ssh_session, SSH_OPTIONS_USER, user.toLocal8Bit() );
#else
    ssh_options_set ( my_ssh_session, SSH_OPTIONS_USER, user.toAscii() );
#endif

#ifdef Q_OS_WIN
    ssh_options_set ( my_ssh_session, SSH_OPTIONS_SSH_DIR, (mainWnd->getHomeDirectory()+"/ssh").toLocal8Bit());
#ifdef DEBUG
    x2goDebug<<"Setting SSH directory to "<<(mainWnd->getHomeDirectory()+"/ssh").toLocal8Bit();
#endif
#endif

    if ( userAuth() )
    {
        if(disconnectSessionFlag)
        {
#ifdef DEBUG
            x2goDebug<<"Session is already disconnected, exiting."<<endl;
#endif
            return;
        }
#ifdef DEBUG
        x2goDebug<<"User authentication OK.";
#endif
        emit connectionOk(host);
    }
    else
    {
        if(disconnectSessionFlag)
        {
#ifdef DEBUG
            x2goDebug<<"Session is already disconnected, exiting."<<endl;
#endif
            return;
        }
        QString err;
        if (!kerberos)
        {
            err=ssh_get_error ( my_ssh_session );
        }
        else
        {
            err=sshProcErrString;
        }
        QString message=tr ( "Authentication failed." );
#ifdef DEBUG
        x2goDebug<<message<<" - "<<err;
#endif
        emit userAuthError ( authErrors.join ( "\n" ) );
        ssh_disconnect ( my_ssh_session );
        ssh_free ( my_ssh_session );
        quit();
        return;
    }


#ifndef Q_OS_WIN
    const int y=1;
#else
    const char y=1;
#endif
    socket_t session_sock=ssh_get_fd(my_ssh_session);
    setsockopt(session_sock, IPPROTO_TCP, TCP_NODELAY,&y, sizeof(int));


    channelLoop();
}


SshMasterConnection::~SshMasterConnection()
{

    disconnectFlagMutex.lock();
    disconnectSessionFlag=true;
    disconnectFlagMutex.unlock();
#ifdef DEBUG
    x2goDebug<<"SshMasterConnection, instance "<<this<<" waiting for thread to finish.";
#endif
    wait(15000);
#ifdef DEBUG
    x2goDebug<<"SshMasterConnection, instance "<<this<<" thread finished.";
#endif
    for(int i=processes.count()-1; i>=0; --i)
    {
        delete processes[i];
    }
#ifdef DEBUG
    x2goDebug<<"SshMasterConnection, instance "<<this<<" finished destructor.";
#endif
}


void SshMasterConnection::finalizeLibSsh()
{
    if ( !isLibSshInited )
    {
#ifdef DEBUG
        x2goDebug<<"libssh not initialized yet.";
#endif
        return;
    }

    ssh_finalize();
#ifdef DEBUG
    x2goDebug<<"libssh finalized.";
#endif
}

bool SshMasterConnection::sshConnect()
{
    int rc;
    QByteArray tmpBA = host.toLocal8Bit();
    if(useproxy && proxytype==PROXYSSH)
    {
        ssh_options_set ( my_ssh_session, SSH_OPTIONS_HOST, "127.0.0.1" );
        ssh_options_set ( my_ssh_session, SSH_OPTIONS_PORT, &localProxyPort );

    }
    else
    {
        ssh_options_set ( my_ssh_session, SSH_OPTIONS_HOST, tmpBA.data() );
        ssh_options_set ( my_ssh_session, SSH_OPTIONS_PORT, &port );
    }
    rc = ssh_connect ( my_ssh_session );
    if ( rc != SSH_OK )
    {
        return false;
    }
//set values for remote host for proper server authentication
    if(useproxy && proxytype==PROXYSSH)
    {
        ssh_options_set ( my_ssh_session, SSH_OPTIONS_HOST, tmpBA.data() );
        ssh_options_set ( my_ssh_session, SSH_OPTIONS_PORT, &port );

    }
    return true;
}


void SshMasterConnection::writeKnownHosts(bool write)
{
    writeHostKeyMutex.lock();
    writeHostKeyReady=true;
    writeHostKey=write;
    if(!write)
    {
        breakLoop=true;
        emit serverAuthAborted();
    }
    writeHostKeyMutex.unlock();

}


int SshMasterConnection::serverAuth ( QString& errorMsg )
{
#ifdef DEBUG
    x2goDebug<<"cserverAuth";
#endif

    int state, hlen;
    unsigned char *hash = NULL;
    char *hexa;

    state = ssh_is_server_known ( my_ssh_session );
    hlen = ssh_get_pubkey_hash ( my_ssh_session, &hash );


    if ( hlen < 0 )
        return SSH_SERVER_ERROR;

#ifdef DEBUG
    x2goDebug<<"state: "<<state<<endl;
#endif


    switch ( state )
    {
    case SSH_SERVER_KNOWN_OK:
        break; /* ok */

    case SSH_SERVER_KNOWN_CHANGED:
        hexa = ssh_get_hexa ( hash, hlen );
        errorMsg=host+":"+QString::number(port)+" - "+hexa;
        free ( hexa );
        break;
    case SSH_SERVER_FOUND_OTHER:
        break;
    case SSH_SERVER_FILE_NOT_FOUND:
    case SSH_SERVER_NOT_KNOWN:
        if ( !acceptUnknownServers )
        {
            hexa = ssh_get_hexa ( hash, hlen );
            errorMsg=host+":"+QString::number(port)+" - "+hexa;
            free ( hexa );
            break;
        }
        ssh_write_knownhost ( my_ssh_session );
        state=SSH_SERVER_KNOWN_OK;
        break;

    case SSH_SERVER_ERROR:
        errorMsg=host+":"+QString::number(port)+" - "+ssh_get_error ( my_ssh_session );
        break;
    }
    ssh_clean_pubkey_hash ( &hash );
    return state;
}

void SshMasterConnection::setVerficationCode(QString code)
{
    challengeAuthVerificationCode=code;
}


bool SshMasterConnection::userChallengeAuth()
{
    int rez=ssh_userauth_kbdint(my_ssh_session, NULL, NULL);
    int prompts;

    switch( rez)
    {
    case SSH_AUTH_INFO:
        prompts=ssh_userauth_kbdint_getnprompts(my_ssh_session);
#ifdef DEBUG
        x2goDebug<<"Have prompts: "<<prompts<<endl;
#endif
        if(prompts)
        {
            const char *prompt= ssh_userauth_kbdint_getprompt(my_ssh_session,0,NULL);
#ifdef DEBUG
            x2goDebug<<"Prompt[0]: |"<<prompt<<"|"<<endl;
#endif
            QString pr=prompt;
            if(pr.startsWith ("Password:"))
            {
#ifdef DEBUG
                x2goDebug<<"Password request"<<endl;
#endif
                ssh_userauth_kbdint_setanswer(my_ssh_session,0,pass.toAscii());
                return userChallengeAuth();
            }

            bool has_challenge_auth_code_prompt = false;
            const std::size_t challenge_auth_code_prompts_size = (sizeof (challenge_auth_code_prompts_)/sizeof (*challenge_auth_code_prompts_));

            for (std::size_t i = 0; i < challenge_auth_code_prompts_size; ++i) {
                x2goDebug << "Checking against known prompt #" << i << ": " << challenge_auth_code_prompts_[i] << endl;

                if (pr.startsWith (challenge_auth_code_prompts_[i])) {
                    has_challenge_auth_code_prompt = true;
                    break;
                }
            }

            if (has_challenge_auth_code_prompt) {
#ifdef DEBUG
                x2goDebug<<"Verification code request"<<endl;
#endif

                challengeAuthPasswordAccepted=true;
                if(challengeAuthVerificationCode == QString::null)
                {
                    keyPhraseReady=false;
                    emit needPassPhrase(this, true);
                    for(;;)
                    {
                        bool ready=false;
                        this->usleep(200);
                        keyPhraseMutex.lock();
                        if(keyPhraseReady)
                            ready=true;
                        keyPhraseMutex.unlock();
                        if(ready)
                            break;
                    }
                    challengeAuthVerificationCode=keyPhrase;
                    if(challengeAuthVerificationCode==QString::null)
                    {
                        authErrors<<tr("Authentication failed.");
                        return false;
                    }
                }
                ssh_userauth_kbdint_setanswer(my_ssh_session,0,challengeAuthVerificationCode.toAscii());
                return userChallengeAuth();
            }
            QString err=ssh_get_error ( my_ssh_session );
            authErrors<<err;

            return false;
        }
        else
        {
            return userChallengeAuth();
        }
    case SSH_AUTH_SUCCESS:
#ifdef DEBUG
        x2goDebug<<"Challenge authentication OK."<<endl;
#endif
        return true;
    case SSH_AUTH_DENIED:
        if(!challengeAuthPasswordAccepted )
        {
            QString err=ssh_get_error ( my_ssh_session );
            authErrors<<err;
            return false;
        }
        else
        {
            challengeAuthVerificationCode=QString::null;
            //try with another verification code
            return userChallengeAuth();
        }
    default:
        QString err=ssh_get_error ( my_ssh_session );
        authErrors<<err;

        return false;
    }
    return false;

}


bool SshMasterConnection::userAuthWithPass()
{
    bool ret = false;

    // Populate the userauth_list
    ssh_userauth_none(my_ssh_session, NULL);

    int method = ssh_userauth_list(my_ssh_session, NULL);

    if (method& SSH_AUTH_METHOD_INTERACTIVE)
    {
#ifdef DEBUG
        x2goDebug<<"Challenge authentication requested."<<endl;
#endif
        challengeAuthPasswordAccepted=false;
        ret = userChallengeAuth();
    }

    if (!ret) {
        x2goDebug << "Challenge authentication failed. Trying password mechanism if available." << endl;
    }

    if ((!ret) && (method & SSH_AUTH_METHOD_PASSWORD))
    {
        if (!ret) {
            x2goDebug << "Password mechanism available. Continuing." << endl;
        }

#ifdef DEBUG
        x2goDebug<<"Password authentication requested."<<endl;
#endif
        int rc = ssh_userauth_password ( my_ssh_session, NULL, pass.toAscii() );
        if ( rc != SSH_AUTH_SUCCESS )
        {
            QString err=ssh_get_error ( my_ssh_session );
            authErrors<<err;
#ifdef DEBUG
            x2goDebug<<"userAuthWithPass failed:" <<err<<endl;
#endif
        }
        else {
            ret = true;
        }
    }

    return (ret);
}


bool SshMasterConnection::userAuthAuto()
{
    int rc = ssh_userauth_autopubkey ( my_ssh_session, "" );
    int i=0;
    while(rc != SSH_AUTH_SUCCESS)
    {
        keyPhraseReady=false;
        emit needPassPhrase(this, false);
        for(;;)
        {
            bool ready=false;
            this->usleep(200);
            keyPhraseMutex.lock();
            if(keyPhraseReady)
                ready=true;
            keyPhraseMutex.unlock();
            if(ready)
                break;
        }
        if(keyPhrase==QString::null)
            break;
        rc = ssh_userauth_autopubkey ( my_ssh_session, keyPhrase.toAscii() );
        if(i++==2)
        {
            break;
        }
    }

    if ( rc != SSH_AUTH_SUCCESS )
    {
        QString err=ssh_get_error ( my_ssh_session );
        authErrors<<err;
#ifdef DEBUG
        x2goDebug<<"userAuthAuto failed:" <<err<<endl;
#endif
        return false;
    }
    return true;
}

void SshMasterConnection::setKeyPhrase(QString phrase)
{
    keyPhraseMutex.lock();
    keyPhrase=phrase;
    keyPhraseReady=true;
    keyPhraseMutex.unlock();
}


bool SshMasterConnection::userAuthWithKey()
{
#ifdef DEBUG
    x2goDebug<<"Trying to authenticate user with private key." <<endl;
#endif
    QString keyName=key;
    bool autoRemove=false;
    if ( key.indexOf ( "PRIVATE KEY" ) !=-1 )
    {
        QDir dr;
        QString keyPath=mainWnd->getHomeDirectory() +"/.x2go/ssh/gen";
        dr.mkpath ( keyPath );
        QTemporaryFile fl ( keyPath+"/key" );
        fl.open();
        keyName=fl.fileName();
        fl.setAutoRemove ( false );
        QTextStream out ( &fl );
        out<<key;
        fl.close();
        autoRemove=true;
#ifdef DEBUG
        x2goDebug<<"Temporarily saved key in "<<keyName<<endl;
#endif
    }

    ssh_private_key prkey=privatekey_from_file(my_ssh_session, keyName.toAscii(), 0,"");
    int i=0;
    while(!prkey)
    {
        keyPhraseReady=false;
        emit needPassPhrase(this, false);
        for(;;)
        {
            bool ready=false;
            this->usleep(200);
            keyPhraseMutex.lock();
            if(keyPhraseReady)
                ready=true;
            keyPhraseMutex.unlock();
            if(ready)
                break;
        }
        if(keyPhrase==QString::null)
            break;
        prkey=privatekey_from_file(my_ssh_session, keyName.toAscii(), 0,keyPhrase.toAscii());
        if(i++==2)
        {
            break;
        }
    }
    if (!prkey)
    {
#ifdef DEBUG
        x2goDebug<<"Failed to get private key from "<<keyName<<endl;
#endif
        if ( autoRemove )
            QFile::remove ( keyName );
        return false;
    }
    ssh_public_key pubkey=publickey_from_privatekey(prkey);
    if (!pubkey)
    {
#ifdef DEBUG
        x2goDebug<<"Failed to get public key from private key."<<endl;
#endif
        privatekey_free(prkey);
        if ( autoRemove )
            QFile::remove ( keyName );
        return false;
    }

    ssh_string pubkeyStr=publickey_to_string(pubkey);
    publickey_free(pubkey);

    //not implemented before libssh 0.5
    /*	int rc = ssh_userauth_privatekey_file ( my_ssh_session,NULL,
    	                                        keyName.toAscii(),
    	                                        pass.toAscii() );*/

    int rc=ssh_userauth_pubkey(my_ssh_session, NULL, pubkeyStr, prkey);
    privatekey_free(prkey);
    string_free(pubkeyStr);

#ifdef DEBUG
    x2goDebug<<"Authenticating with key: "<<rc<<endl;
#endif

    if ( autoRemove )
        QFile::remove ( keyName );
    if ( rc != SSH_AUTH_SUCCESS )
    {
        QString err=ssh_get_error ( my_ssh_session );
        authErrors<<err;

#ifdef DEBUG
        x2goDebug<<"userAuthWithKey failed:" <<err<<endl;
#endif

        return false;
    }
    return true;
}

bool SshMasterConnection::userAuthKrb()
{
    QProcess ssh;

    QUuid uuid = QUuid::createUuid();
    QString uuidStr = uuid.toString().mid(1, 36).toLower();

    /* On Windows, arguments are automatically wrapped in double quotes.
     * Additionally, QProcess automatically doubles escape characters before
     * double quotes and inserts an escape character before any non-escaped
     * double quotes.
     * Thus, we don't escape double quotes here and let Qt handle this stuff.
     *
     * On UNIX-like platforms, likewise, we MUST NOT escape double quotes,
     * as there is no preceding "outer double quote" the whole argument
     * is wrapped in.
     */
    QString shcmd = "bash -l -c 'echo \"X2GODATABEGIN:" + uuidStr + "\"; export TERM=\"dumb\"; whoami; echo \"X2GODATAEND:" + uuidStr + "\";'";

    QString local_cmd = "";
    QStringList local_args;

#ifdef Q_OS_WIN
    local_cmd = "plink";

    /* General options. */
    local_args << "-batch";

    /* Port option. Must be the last one added! */
    local_args << "-P";
#else
    local_cmd = "ssh";

    /* Kerberos options. */
    local_args << "-o" << "GSSApiAuthentication=yes"
               << "-o" << "PasswordAuthentication=no"
               << "-o" << "PubkeyAuthentication=no";

    /* Port option. Must be the last one added! */
    local_args << "-p";
#endif
    local_args << QString::number (port)
               << "-l" << user
               << host;

    /* On Windows, arguments are automatically wrapped in double quotes.
     * This means we do not have to wrap shcmd ourselves.
     *
     * On UNIX-like platforms, we likewise MUST NOT wrap the command in
     * double quotes, as each entry in the arguments list is passed as
     * one entry in argv.
     */
    local_args << shcmd;

#ifdef DEBUG
    x2goDebug << "Starting ssh:" << local_cmd << " " << local_args.join (" ") << endl;
#endif
    ssh.start (local_cmd, local_args);


    if (!ssh.waitForStarted(5000))
    {
        sshProcErrString=ssh.errorString();
        authErrors<<sshProcErrString;
#ifdef DEBUG
        x2goDebug<<"SSH start failed:" <<sshProcErrString<<endl;
#endif
        return false;
    }
    if (!ssh.waitForFinished(20000))
    {
        sshProcErrString=ssh.errorString();
        authErrors<<tr("Failed to start SSH client. Please check your installation and GSSApi configuration.");
        authErrors<<sshProcErrString;
#ifdef DEBUG
        x2goDebug<<"SSH did not finish:" <<sshProcErrString<<endl;
#endif

        return false;
    }
    QString outp=ssh.readAllStandardOutput();
    QString err=ssh.readAllStandardError();
#ifdef DEBUG
    x2goDebug<<"SSH exited.";
    x2goDebug<<"stdout: "<<outp<<endl;
    x2goDebug<<"stderr: "<<err<<endl;
    x2goDebug<<"Exit code: "<<ssh.exitCode()<<"; status: "<<ssh.exitStatus()<<endl;
#endif

    QString begin_marker = "X2GODATABEGIN:"+uuidStr+"\n";
    QString end_marker = "X2GODATAEND:"+uuidStr+"\n";
    int output_begin=outp.indexOf(begin_marker) + begin_marker.length();
    int output_end=outp.indexOf(end_marker);
    outp = outp.mid(output_begin, output_end-output_begin);
    outp.replace("\n","");

    if (ssh.exitCode() == 0 && ssh.exitStatus() == 0 && outp== user)
        return true;
    authErrors<<tr("Check your GSSApi configuration or choose another authentication method.");
    return false;
}


bool SshMasterConnection::userAuth()
{
    if (kerberos)
        return userAuthKrb();
    if ( autologin && key=="" )
        if ( userAuthAuto() )
            return true;
    if ( key!="" )
    {
        if ( userAuthWithKey() )
            return true;
    }
    return userAuthWithPass();
}


void SshMasterConnection::addChannelConnection ( SshProcess* creator, int sock, QString forwardHost, int forwardPort,
        QString localHost, int localPort, void* channel )
{
    ChannelConnection con;
    con.channel= ( ssh_channel ) channel;
    con.sock=sock;
    con.creator=creator;
    con.forwardHost=forwardHost;
    con.forwardPort=forwardPort;
    con.localHost=localHost;
    con.localPort=localPort;

    channelConnectionsMutex.lock();
    channelConnections<<con;
    channelConnectionsMutex.unlock();
}


void SshMasterConnection::addChannelConnection ( SshProcess* creator, QString uuid, QString cmd )
{

    ChannelConnection con;
    con.channel=NULL;
    con.sock=-1;
    con.creator=creator;
    con.command=cmd;
    con.uuid=uuid;

    x2goDebug << "Locking SSH channel connection MUTEX.";
    channelConnectionsMutex.lock();
    x2goDebug << "Passing new channel conenction object to channelConnections.";
    channelConnections<<con;
    x2goDebug << "Unlocking SSH channel connection MUTEX.";
    channelConnectionsMutex.unlock();
}


void SshMasterConnection::addCopyRequest ( SshProcess* creator, QString src, QString dst )
{
    CopyRequest req;
    req.src=src;
    req.dst=dst;
    req.creator=creator;
    copyRequestMutex.lock();
    copyRequests<<req;
    copyRequestMutex.unlock();
}


void SshMasterConnection::copy()
{

    for ( int i=copyRequests.size()-1; i>=0; --i )
    {
        QStringList lst=copyRequests[i].dst.split ( "/" );
        QString dstFile=lst.last();
        lst.removeLast();
        QString dstPath=lst.join ( "/" );
#ifdef DEBUG
        x2goDebug<<"SSH Master Connection copy - dst path:"<<dstPath<<" file:"<<dstFile<<endl;
#endif
        ssh_scp scp=ssh_scp_new ( my_ssh_session, SSH_SCP_WRITE|SSH_SCP_RECURSIVE, dstPath.toAscii() );
        if ( scp == NULL )
        {
#ifdef DEBUG
            x2goDebug<<"Error allocating SCP session: "<< ssh_get_error ( my_ssh_session ) <<endl;
#endif
            return;
        }
        int rc = ssh_scp_init ( scp );
        if ( rc != SSH_OK )
        {
#ifdef DEBUG
            x2goDebug<<"Error initializing SCP session: "<< ssh_get_error ( my_ssh_session ) <<endl;
#endif
            ssh_scp_free ( scp );
            return;
        }
        QFile file ( copyRequests[i].src );
        if ( !file.open ( QIODevice::ReadOnly ) )
        {
            QString errMsg=tr ( "Cannot open file " ) +copyRequests[i].src;
            emit copyErr ( copyRequests[i].creator, errMsg, "" );
            copyRequests.removeAt ( i );
            ssh_scp_close ( scp );
            ssh_scp_free ( scp );
            continue;
        }
        QByteArray arr=file.readAll();
        file.close();
        rc=ssh_scp_push_file ( scp,dstFile.toAscii(),arr.size(), 0600 );
        if ( rc != SSH_OK )
        {
            QString errMsg=tr ( "Cannot create remote file " ) +copyRequests[i].dst;
            QString serr=ssh_get_error ( my_ssh_session );
#ifdef DEBUG
            x2goDebug<<errMsg<<" - "<<serr<<endl;
#endif
            emit copyErr ( copyRequests[i].creator, errMsg, serr );
            copyRequests.removeAt ( i );
            ssh_scp_close ( scp );
            ssh_scp_free ( scp );
            continue;
        }
        rc=ssh_scp_write ( scp,arr.data(),arr.size() );
        if ( rc != SSH_OK )
        {
            QString serr=ssh_get_error ( my_ssh_session );
            QString errMsg=tr ( "Cannot write to remote file " ) +copyRequests[i].dst;
#ifdef DEBUG
            x2goDebug<<errMsg<<" - "<<serr<<endl;
#endif
            emit copyErr ( copyRequests[i].creator, errMsg, serr );
            copyRequests.removeAt ( i );
            ssh_scp_close ( scp );
            ssh_scp_free ( scp );
            continue;
        }
        emit copyOk ( copyRequests[i].creator );
#ifdef DEBUG
        x2goDebug<<"scp ok: "<<copyRequests[i].src<<" -> "<<user<<"@"<<host<<":"<<copyRequests[i].dst<<endl;
#endif
        copyRequests.removeAt ( i );
        ssh_scp_close ( scp );
        ssh_scp_free ( scp );
    }
}

void SshMasterConnection::channelLoop()
{
    forever
    {
        disconnectFlagMutex.lock();
        bool disconnect=disconnectSessionFlag;
        disconnectFlagMutex.unlock();

        if ( disconnect )
        {
#ifdef DEBUG
            x2goDebug<<"Disconnecting ..."<<endl;
#endif

            if (useproxy && proxytype==PROXYSSH&&sshProxy)
            {
                delete sshProxy;
                sshProxy=0;
            }

            channelConnectionsMutex.lock();
#ifdef DEBUG
            x2goDebug<<"Deleting channel connections."<<endl;
#endif
            for ( int i=0; i<channelConnections.size(); ++i )
            {
                finalize ( i );
            }
            channelConnectionsMutex.unlock();
#ifdef DEBUG
            x2goDebug<<"Disconnecting session."<<endl;
#endif
            ssh_disconnect ( my_ssh_session );
            ssh_free ( my_ssh_session );

#ifdef DEBUG
            x2goDebug<<"Deleting sockets."<<endl;
#endif
            if (tcpProxySocket != NULL)
                delete tcpProxySocket;
            if (tcpNetworkProxy != NULL)
                delete tcpNetworkProxy;
#ifdef DEBUG
            x2goDebug<<"All channels closed and session disconnected. Quiting session loop."<<endl;
#endif
            quit();
            return;
        }
        addReverseTunnelConnections();
        checkReverseTunnelConnections();
        copyRequestMutex.lock();
        if ( copyRequests.size() >0 )
            copy();
        copyRequestMutex.unlock();

        char buffer[1024*512]; //512K buffer
        int nbytes;
        fd_set rfds;

        struct timeval tv;

        tv.tv_sec = 0;
        tv.tv_usec = 500000;

        int retval;
        int maxsock=-1;


        channelConnectionsMutex.lock();
        if ( channelConnections.size() <=0 )
        {
#ifdef DEBUG
            //             x2goDebug<<"no channel connections, waiting\n";
#endif
            channelConnectionsMutex.unlock();
            usleep ( 500 );
            continue;
        }
        ssh_channel* read_chan=new ssh_channel[channelConnections.size() +1];
        ssh_channel* out_chan=new ssh_channel[channelConnections.size() +1];
        read_chan[channelConnections.size() ]=NULL;

        FD_ZERO ( &rfds );

        for ( int i=0; i<channelConnections.size(); ++i )
        {
            int tcpSocket=channelConnections.at ( i ).sock;
            if ( tcpSocket>0 )
                FD_SET ( tcpSocket, &rfds );
            if ( channelConnections.at ( i ).channel==0l )
            {
#ifdef DEBUG
                x2goDebug<<"Creating new channel."<<endl;
#endif
                ssh_channel channel=channel_new ( my_ssh_session );
#ifdef DEBUG
                x2goDebug<<"New channel:"<<channel<<endl;
#endif
                channelConnections[i].channel=channel;
                if ( tcpSocket>0 )
                {
#ifdef DEBUG
                    x2goDebug<<"Forwarding new channel, local port: "<<channelConnections.at ( i ).localPort<<endl;
#endif
                    if ( channel_open_forward ( channel,
                                                channelConnections.at ( i ).forwardHost.toAscii(),
                                                channelConnections.at ( i ).forwardPort,
                                                channelConnections.at ( i ).localHost.toAscii(),
                                                channelConnections.at ( i ).localPort ) != SSH_OK )
                    {
                        QString err=ssh_get_error ( my_ssh_session );
                        QString errorMsg=tr ( "channel_open_forward failed." );
                        emit ioErr ( channelConnections[i].creator, errorMsg, err );
#ifdef DEBUG
                        x2goDebug<<errorMsg<<": "<<err<<endl;
#endif
                    }
#ifdef DEBUG
                    else
                    {
                        x2goDebug<<"New channel forwarded."<<endl;
                    }
#endif
                }
                else
                {
#ifdef DEBUG
                    x2goDebug<<"Executing remote: "<<channelConnections.at ( i ).command<<endl;
#endif
                    if ( channel_open_session ( channel ) !=SSH_OK )
                    {
                        QString err=ssh_get_error ( my_ssh_session );
                        QString errorMsg=tr ( "channel_open_session failed." );
                        emit ioErr ( channelConnections[i].creator, errorMsg, err );
#ifdef DEBUG
                        x2goDebug<<errorMsg<<": "<<err<<endl;
#endif
                    }
                    else if ( channel_request_exec ( channel, channelConnections[i].command.toAscii() ) != SSH_OK )
                    {
                        QString err=ssh_get_error ( my_ssh_session );
                        QString errorMsg=tr ( "channel_request_exec failed" );
                        emit ioErr ( channelConnections[i].creator, errorMsg, err );
#ifdef DEBUG
                        x2goDebug<<errorMsg<<": "<<err<<endl;
#endif
                    }
#ifdef DEBUG
                    else
                    {
                        x2goDebug<<"New exec channel created."<<endl;
                    }
#endif
                }

            }
            read_chan[i]=channelConnections.at ( i ).channel;
            if ( tcpSocket>maxsock )
                maxsock=tcpSocket;
        }
        channelConnectionsMutex.unlock();
        retval=ssh_select ( read_chan,out_chan,maxsock+1,&rfds,&tv );
        delete [] read_chan;
        delete [] out_chan;

        if ( retval == -1 )
        {
#ifdef DEBUG
            x2goDebug<<"select() error.";
#endif
            continue;
        }

#ifdef DEBUG
        //         x2goDebug<<"select exited"<<endl;
#endif

        channelConnectionsMutex.lock();
        for ( int i=channelConnections.size()-1; i>=0; --i )
        {
            int tcpSocket=channelConnections.at ( i ).sock;
            ssh_channel channel=channelConnections.at ( i ).channel;
            if ( channel==0l )
                continue;
            if ( channel_poll ( channel,1 ) >0 )
            {
#ifdef DEBUG
                //              x2goDebug<<"read err data from channel\n";
#endif
                nbytes = channel_read ( channel, buffer, sizeof ( buffer )-1, 1 );
                emit stdErr ( channelConnections[i].creator, QByteArray ( buffer,nbytes ) );
#ifdef DEBUG
                //              x2goDebug<<nbytes<<" err from channel"<<endl;
#endif
            }
            int rez=channel_poll ( channel,0 );
            if ( rez==SSH_EOF )
            {
#ifdef DEBUG
                x2goDebug<<"EOF on channel "<<channel<<"; SshProcess object: "<<channelConnections[i].creator->pid;
#endif
                //////Finished////////
                finalize ( i );
                continue;
            }
            if ( rez>0 )
            {
#ifdef DEBUG
                //                  x2goDebug<<"read data from channel "<<channel<<endl;
#endif
                nbytes = channel_read ( channel, buffer, sizeof ( buffer )-1, 0 );
#ifdef DEBUG
                //                  x2goDebug<<nbytes<<" from channel "<<channel<<endl;
#endif
                if ( nbytes > 0 )
                {
                    if ( tcpSocket>0 )
                    {
                        if ( send ( tcpSocket,buffer, nbytes,0 ) != nbytes )
                        {
                            QString errMsg=tr ( "Error writing to socket." );
#ifdef DEBUG
                            x2goDebug<<"Error writing "<<nbytes<<" to TCP socket"<<tcpSocket<<endl;
#endif
                            emit ioErr ( channelConnections[i].creator,errMsg,"" );
                            finalize ( i );
                            continue;
                        }
#ifdef DEBUG
                        //                      x2goDebug<<"wrote "<<nbytes<<" to tcp socket "<<tcpSocket<<endl;
#endif
                    }
                    else
                    {
                        emit stdOut ( channelConnections[i].creator, QByteArray ( buffer,nbytes ) );
                    }
                }

                if ( nbytes < 0 )
                {
                    //////ERROR!!!!!////////
                    QString err=ssh_get_error ( my_ssh_session );
                    QString errorMsg=tr ( "Error reading channel." );
                    emit ioErr ( channelConnections[i].creator, errorMsg, err );
#ifdef DEBUG
                    x2goDebug<<errorMsg<<" - "<<err<<endl;
#endif
                    finalize ( i );
                    continue;
                }

                if ( channel_is_eof ( channel ) )
                {
#ifdef DEBUG
                    x2goDebug<<"EOF on channel "<<channel<<"; SshProcess object: "<<channelConnections[i].creator->pid;
#endif
                    //////Finished////////
                    finalize ( i );
                    continue;
                }
            }
            if ( tcpSocket<=0 )
            {
                continue;
            }
            if ( FD_ISSET ( tcpSocket,&rfds ) )
            {
                nbytes = recv ( tcpSocket, buffer, sizeof ( buffer )-1,0 );
#ifdef DEBUG
                //                  x2goDebug<<nbytes<<" bytes from tcp socket "<<tcpSocket<<endl;
#endif
                if ( nbytes > 0 )
                {
                    if ( channel_write ( channel, buffer, nbytes ) !=nbytes )
                    {
                        QString err=ssh_get_error ( my_ssh_session );
                        QString errorMsg=tr ( "channel_write failed." );
                        emit ioErr ( channelConnections[i].creator, errorMsg, err );
#ifdef DEBUG
                        x2goDebug<<errorMsg<<" - "<<err<<endl;
#endif
                        finalize ( i );
                        continue;
                    }
#ifdef DEBUG
                    //                      x2goDebug<<nbytes<<" bytes wrote to channel"<<channel<<endl;
#endif
                }
                if ( nbytes < 0 )
                {
                    //////ERROR!!!!!////////
                    QString err="";
                    QString errorMsg=tr ( "Error reading from TCP socket." );
                    emit ioErr ( channelConnections[i].creator, errorMsg, err );
#ifdef DEBUG
                    x2goDebug<<errorMsg<<" - "<<err<<endl;
#endif
                    finalize ( i );
                    continue;
                }
                if ( nbytes==0 )
                {
#ifdef DEBUG
                    x2goDebug<<"Socket "<<tcpSocket<<" closed."<<endl;
#endif
                    finalize ( i );
                    continue;
                }
            }
        }
        channelConnectionsMutex.unlock();
    }
}

void SshMasterConnection::finalize ( int item )
{
    int tcpSocket=channelConnections.at ( item ).sock;
    ssh_channel channel=channelConnections.at ( item ).channel;
    if ( channel )
    {
        channel_send_eof ( channel );
#ifdef DEBUG
        x2goDebug<<"EOF sent.";
#endif
        channel_close ( channel );
#ifdef DEBUG
        x2goDebug<<"Channel closed.";
#endif
        channel_free ( channel );
    }
    if ( tcpSocket>0 )
    {
#ifndef Q_OS_WIN
        shutdown(tcpSocket, SHUT_RDWR);
        close ( tcpSocket );
#else
        shutdown(tcpSocket, SD_BOTH);
        closesocket ( tcpSocket );
#endif
    }
    SshProcess* proc=channelConnections[item].creator;
    QString uuid=channelConnections[item].uuid;
    channelConnections.removeAt ( item );
    emit channelClosed ( proc, uuid );
}

