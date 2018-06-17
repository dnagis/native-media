/**
 * git add app/src/main/cpp/native-media-jni.c
 * 
 * 
 * Hacking de native-media NDK de chez googlesamples, pour obtenir les bytes en provenance d'un socket plutôt que d'une file
 * 
 * de l'autre côté 
 * socat OPEN:output.ts TCP-LISTEN:8080
 * 
 * Conversion ffmpeg pour matcher le format du sample NativeMedia.ts
 * ffmpeg -y -ss 4000 -i ted.m2ts -t 20 -c copy cut.m2ts
 * ffmpeg -y -i cut.m2ts -c:v libx264 -b:v 1300K -profile:v baseline -c:a aac -ar 44100 -b:a 62k output.ts
 * 
 * 
 */

/* This is a JNI example where we use native methods to play video
 * using OpenMAX AL. See the corresponding Java source file located at:
 *
 *   src/com/example/nativemedia/NativeMedia/NativeMedia.java
 *
 * In this example we use assert() for "impossible" error conditions,
 * and explicit handling and recovery for more likely error conditions.
 */

#include <assert.h>
#include <jni.h>
#include <pthread.h>
#include <stdio.h>
#include <string.h>



// for __android_log_print(ANDROID_LOG_INFO, "YourApp", "formatted message");
//*****vincent <--> adb logcat -s "NativeMedia"*****
#include <android/log.h>
#define TAG "NativeMedia"
#define LOGV(...) __android_log_print(ANDROID_LOG_VERBOSE, TAG, __VA_ARGS__)

// for native media
#include <OMXAL/OpenMAXAL.h>
#include <OMXAL/OpenMAXAL_Android.h>

// for native window JNI
#include <android/native_window_jni.h>
#include <android/asset_manager_jni.h>
#include "android_fopen.h"

//Vincent pour les sockets
#include <sys/socket.h>
#include <netinet/in.h>

//Vincent pour sleep()
#include <unistd.h>


// engine interfaces
static XAObjectItf engineObject = NULL;
static XAEngineItf engineEngine = NULL;

// output mix interfaces
static XAObjectItf outputMixObject = NULL;

// streaming media player interfaces
static XAObjectItf             playerObj = NULL;
static XAPlayItf               playerPlayItf = NULL;
static XAAndroidBufferQueueItf playerBQItf = NULL;
static XAStreamInformationItf  playerStreamInfoItf = NULL;
static XAVolumeItf             playerVolItf = NULL;

// number of required interfaces for the MediaPlayer creation
#define NB_MAXAL_INTERFACES 3 // XAAndroidBufferQueueItf, XAStreamInformationItf and XAPlayItf

// video sink for the player
static ANativeWindow* theNativeWindow;

// number of buffers in our buffer queue, an arbitrary number (8)
#define NB_BUFFERS 8

// we're streaming MPEG-2 transport stream data, operate on transport stream block size
#define MPEG2_TS_PACKET_SIZE 188

// number of MPEG-2 transport stream blocks per buffer, an arbitrary number (10)
#define PACKETS_PER_BUFFER 10

// determines how much memory we're dedicating to memory caching
#define BUFFER_SIZE (PACKETS_PER_BUFFER*MPEG2_TS_PACKET_SIZE)

// where we cache in memory the data to play
// note this memory is re-used by the buffer queue callback
static char dataCache[BUFFER_SIZE * NB_BUFFERS];

// handle of the file to play
static FILE *file;

//vincent socket
static int sock;

// has the app reached the end of the file
static jboolean reachedEof = JNI_FALSE;

// constant to identify a buffer context which is the end of the stream to decode
static const int kEosBufferCntxt = 1980; // a magic value we can compare against

// For mutual exclusion between callback thread and application thread(s).
// The mutex protects reachedEof, discontinuity,
// The condition is signalled when a discontinuity is acknowledged.

static pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t cond = PTHREAD_COND_INITIALIZER;

// whether a discontinuity is in progress
static jboolean discontinuity = JNI_FALSE;

static jboolean enqueueInitialBuffers(jboolean discontinuity);

// AndroidBufferQueueItf callback to supply MPEG-2 TS packets to the media player
static XAresult AndroidBufferQueueCallback(
        XAAndroidBufferQueueItf caller,
        void *pCallbackContext,        /* input */
        void *pBufferContext,          /* input */
        void *pBufferData,             /* input */
        XAuint32 dataSize,             /* input */
        XAuint32 dataUsed,             /* input */
        const XAAndroidBufferItem *pItems,/* input */
        XAuint32 itemsLength           /* input */)
{
    XAresult res;
    int ok;

    // pCallbackContext was specified as NULL at RegisterCallback and is unused here
    assert(NULL == pCallbackContext);

    // note there is never any contention on this mutex unless a discontinuity request is active
    ok = pthread_mutex_lock(&mutex);
    assert(0 == ok);

    // was a discontinuity requested?
    if (discontinuity) {
        // Note: can't rewind after EOS, which we send when reaching EOF
        // (don't send EOS if you plan to play more content through the same player)
        if (!reachedEof) {
            // clear the buffer queue
            res = (*playerBQItf)->Clear(playerBQItf);
            assert(XA_RESULT_SUCCESS == res);
            // rewind the data source so we are guaranteed to be at an appropriate point
            rewind(file);
            // Enqueue the initial buffers, with a discontinuity indicator on first buffer
            (void) enqueueInitialBuffers(JNI_TRUE);
        }
        // acknowledge the discontinuity request
        discontinuity = JNI_FALSE;
        ok = pthread_cond_signal(&cond);
        assert(0 == ok);
        goto exit;
    }

    if ((pBufferData == NULL) && (pBufferContext != NULL)) {
        const int processedCommand = *(int *)pBufferContext;
        if (kEosBufferCntxt == processedCommand) {
            LOGV("EOS was processed\n");
            // our buffer with the EOS message has been consumed
            assert(0 == dataSize);
            goto exit;
        }
    }

    // pBufferData is a pointer to a buffer that we previously Enqueued
    assert((dataSize > 0) && ((dataSize % MPEG2_TS_PACKET_SIZE) == 0));
    assert(dataCache <= (char *) pBufferData && (char *) pBufferData <
            &dataCache[BUFFER_SIZE * NB_BUFFERS]);
    assert(0 == (((char *) pBufferData - dataCache) % BUFFER_SIZE));

    // don't bother trying to read more data once we've hit EOF
    if (reachedEof) {
        goto exit;
    }

    // note we do call fread from multiple threads, but never concurrently
    size_t bytesRead;
    /**
     * Vincent read() sur sock au lieu de fread
     * 
     * 
     * */
    //bytesRead = fread(pBufferData, 1, BUFFER_SIZE, file);
    bytesRead = read(sock, pBufferData, 752); //le MTU en wifi est de 1500, on utilise plutôt MPEG2_TS_PACKET_SIZE x 4
    LOGV("bytesRead dans AndroidBufferQueueCallback = %u", bytesRead);
    
    
    
    if (bytesRead > 0) {
        if ((bytesRead % MPEG2_TS_PACKET_SIZE) != 0) {
            LOGV("Dropping last packet because it is not whole");
        }
        size_t packetsRead = bytesRead / MPEG2_TS_PACKET_SIZE;
        size_t bufferSize = packetsRead * MPEG2_TS_PACKET_SIZE;
        res = (*caller)->Enqueue(caller, NULL /*pBufferContext*/,
                pBufferData /*pData*/,
                bufferSize /*dataLength*/,
                NULL /*pMsg*/,
                0 /*msgLength*/);
        assert(XA_RESULT_SUCCESS == res);
    } else {
        // EOF or I/O error, signal EOS
        XAAndroidBufferItem msgEos[1];
        msgEos[0].itemKey = XA_ANDROID_ITEMKEY_EOS;
        msgEos[0].itemSize = 0;
        // EOS message has no parameters, so the total size of the message is the size of the key
        //   plus the size if itemSize, both XAuint32
        res = (*caller)->Enqueue(caller, (void *)&kEosBufferCntxt /*pBufferContext*/,
                NULL /*pData*/, 0 /*dataLength*/,
                msgEos /*pMsg*/,
                sizeof(XAuint32)*2 /*msgLength*/);
        assert(XA_RESULT_SUCCESS == res);
        reachedEof = JNI_TRUE;
    }

exit:
    ok = pthread_mutex_unlock(&mutex);
    assert(0 == ok);
    return XA_RESULT_SUCCESS;
}


// callback invoked whenever there is new or changed stream information
static void StreamChangeCallback(XAStreamInformationItf caller,
        XAuint32 eventId,
        XAuint32 streamIndex,
        void * pEventData,
        void * pContext )
{
    LOGV("StreamChangeCallback called for stream %u", streamIndex);
    // pContext was specified as NULL at RegisterStreamChangeCallback and is unused here
    assert(NULL == pContext);
    switch (eventId) {
      case XA_STREAMCBEVENT_PROPERTYCHANGE: {
        /** From spec 1.0.1:
            "This event indicates that stream property change has occurred.
            The streamIndex parameter identifies the stream with the property change.
            The pEventData parameter for this event is not used and shall be ignored."
         */

        XAresult res;
        XAuint32 domain;
        res = (*caller)->QueryStreamType(caller, streamIndex, &domain);
        assert(XA_RESULT_SUCCESS == res);
        switch (domain) {
          case XA_DOMAINTYPE_VIDEO: {
            XAVideoStreamInformation videoInfo;
            res = (*caller)->QueryStreamInformation(caller, streamIndex, &videoInfo);
            assert(XA_RESULT_SUCCESS == res);
            LOGV("Found video size %u x %u, codec ID=%u, frameRate=%u, bitRate=%u, duration=%u ms",
                        videoInfo.width, videoInfo.height, videoInfo.codecId, videoInfo.frameRate,
                        videoInfo.bitRate, videoInfo.duration);
          } break;
          default:
            fprintf(stderr, "Unexpected domain %u\n", domain);
            break;
        }
      } break;
      default:
        fprintf(stderr, "Unexpected stream event ID %u\n", eventId);
        break;
    }
}


// create the engine and output mix objects
void Java_com_example_nativemedia_NativeMedia_createEngine(JNIEnv* env, jclass clazz)
{
    XAresult res;

    // create engine
    res = xaCreateEngine(&engineObject, 0, NULL, 0, NULL, NULL);
    assert(XA_RESULT_SUCCESS == res);

    // realize the engine
    res = (*engineObject)->Realize(engineObject, XA_BOOLEAN_FALSE);
    assert(XA_RESULT_SUCCESS == res);

    // get the engine interface, which is needed in order to create other objects
    res = (*engineObject)->GetInterface(engineObject, XA_IID_ENGINE, &engineEngine);
    assert(XA_RESULT_SUCCESS == res);

    // create output mix
    res = (*engineEngine)->CreateOutputMix(engineEngine, &outputMixObject, 0, NULL, NULL);
    assert(XA_RESULT_SUCCESS == res);

    // realize the output mix
    res = (*outputMixObject)->Realize(outputMixObject, XA_BOOLEAN_FALSE);
    assert(XA_RESULT_SUCCESS == res);

}


// Enqueue the initial buffers, and optionally signal a discontinuity in the first buffer
static jboolean enqueueInitialBuffers(jboolean discontinuity)
{

    /* Fill our cache.
     * We want to read whole packets (integral multiples of MPEG2_TS_PACKET_SIZE).
     * fread returns units of "elements" not bytes, so we ask for 1-byte elements
     * and then check that the number of elements is a multiple of the packet size.
     */
    size_t bytesRead, small_chunk_pour_mtu_du_wifi;


    int passage = 0;
    
    /**
     * Vincent: remplacer fread par read
     * bloque souvent: peut être parce que avec le MTU j'ai été obliqé de baisser BUFFER_SIZE et NB_BUFFERS
     * pour que bytesread < 1500.
     * static char dataCache[BUFFER_SIZE * NB_BUFFERS];
     * 
     * le but est de remplir datacache avec des read() de longueur < MTU
     * 
     */
    //bytesRead = fread(dataCache, 1, BUFFER_SIZE * NB_BUFFERS, file);
    //bytesRead = read(sock, dataCache, BUFFER_SIZE * NB_BUFFERS);
    //LOGV("bytesRead dans enqueueInitialBuffers = %u", bytesRead);
    
    LOGV("on va rentrer dans la boucle...");
    
    for (bytesRead = 0;  bytesRead < (BUFFER_SIZE * NB_BUFFERS);) // (80 X 188)
    
    {  
    
	    LOGV("début de la boucle, bytesRead = %i", bytesRead);
	    
	    
	    small_chunk_pour_mtu_du_wifi = read(sock, dataCache + bytesRead, 752); //752 = 188 * 4
	    
	    LOGV("on vient de read() on a récup %i bytes", small_chunk_pour_mtu_du_wifi);
	    
		    
		    if (small_chunk_pour_mtu_du_wifi <= 0) {
		        // could be premature EOF or I/O error
		        return JNI_FALSE;
		    }
	    
			if ((small_chunk_pour_mtu_du_wifi % MPEG2_TS_PACKET_SIZE) != 0) {
			LOGV("*****************On a du packet foireux, je vire*********************");
			} else {
			bytesRead += small_chunk_pour_mtu_du_wifi;
			}
	    

	    passage += 1;
	    
	    LOGV("fin de la boucle n°%i, bytesRead = %i", passage, bytesRead);
	    
	    usleep(500); //si je fais pas ça j'ai plein de fois des packets trop courts: 696 au lieu de 752
    
	}
    
    

    
    
    size_t packetsRead = bytesRead / MPEG2_TS_PACKET_SIZE;
    LOGV("Initially queueing %zu packets", packetsRead);

    /* Enqueue the content of our cache before starting to play,
       we don't want to starve the player */
    size_t i;
    for (i = 0; i < NB_BUFFERS && packetsRead > 0; i++) {
        // compute size of this buffer
        size_t packetsThisBuffer = packetsRead;
        if (packetsThisBuffer > PACKETS_PER_BUFFER) {
            packetsThisBuffer = PACKETS_PER_BUFFER;
        }
        size_t bufferSize = packetsThisBuffer * MPEG2_TS_PACKET_SIZE;
        XAresult res;
        if (discontinuity) {
            // signal discontinuity
            XAAndroidBufferItem items[1];
            items[0].itemKey = XA_ANDROID_ITEMKEY_DISCONTINUITY;
            items[0].itemSize = 0;
            // DISCONTINUITY message has no parameters,
            //   so the total size of the message is the size of the key
            //   plus the size if itemSize, both XAuint32
            res = (*playerBQItf)->Enqueue(playerBQItf, NULL /*pBufferContext*/,
                    dataCache + i*BUFFER_SIZE, bufferSize, items /*pMsg*/,
                    sizeof(XAuint32)*2 /*msgLength*/);
            discontinuity = JNI_FALSE;
        } else {
            res = (*playerBQItf)->Enqueue(playerBQItf, NULL /*pBufferContext*/,
                    dataCache + i*BUFFER_SIZE, bufferSize, NULL, 0);
        }
        assert(XA_RESULT_SUCCESS == res);
        packetsRead -= packetsThisBuffer;
    }

    return JNI_TRUE;
}


// create streaming media player
jboolean Java_com_example_nativemedia_NativeMedia_createStreamingMediaPlayer(JNIEnv* env,
        jclass clazz, jobject assetMgr, jstring filename)
{
    XAresult res;
    
    struct sockaddr_in serv_addr;
    memset(&serv_addr, '0', sizeof(serv_addr));

    //android_fopen_set_asset_manager(AAssetManager_fromJava(env, assetMgr));
    // convert Java string to UTF-8
    //const char *utf8 = (*env)->GetStringUTFChars(env, filename, NULL);
    //assert(NULL != utf8);

    /* open the file to play
    file = android_fopen(utf8, "rb");
    if (file == NULL) {
        return JNI_FALSE;
    }*/
    
    //Vincent sockets
    LOGV("début de Java_com_example_nativemedia_NativeMedia_createStreamingMediaPlayer");
    
    sock = 0;
    
    if ((sock = socket(AF_INET, SOCK_STREAM, 0)) < 0) //je mets un close(sock) dans Java_com_example_nativemedia_NativeMedia_shutdown
		{
		LOGV("Erreur à la création du socket");
		return JNI_FALSE;
		}

	LOGV("socket créé, numéro=%i", sock);
	
	serv_addr.sin_family = AF_INET;
    serv_addr.sin_port = htons(8080);
    //comment passer de l'IP type 127.0.0.1 à l'integer?
    serv_addr.sin_addr.s_addr = inet_addr("192.168.1.12");
    
	if (connect(sock, (struct sockaddr *)&serv_addr, sizeof(serv_addr)) < 0)
		{
		LOGV("connect() a planté");
		return JNI_FALSE;
		}
    
   

    // configure data source
    XADataLocator_AndroidBufferQueue loc_abq = { XA_DATALOCATOR_ANDROIDBUFFERQUEUE, NB_BUFFERS };
    XADataFormat_MIME format_mime = {
            XA_DATAFORMAT_MIME, XA_ANDROID_MIME_MP2TS, XA_CONTAINERTYPE_MPEG_TS };
    XADataSource dataSrc = {&loc_abq, &format_mime};

    // configure audio sink
    XADataLocator_OutputMix loc_outmix = { XA_DATALOCATOR_OUTPUTMIX, outputMixObject };
    XADataSink audioSnk = { &loc_outmix, NULL };

    // configure image video sink
    XADataLocator_NativeDisplay loc_nd = {
            XA_DATALOCATOR_NATIVEDISPLAY,        // locatorType
            // the video sink must be an ANativeWindow created from a Surface or SurfaceTexture
            (void*)theNativeWindow,              // hWindow
            // must be NULL
            NULL                                 // hDisplay
    };
    XADataSink imageVideoSink = {&loc_nd, NULL};

    // declare interfaces to use
    XAboolean     required[NB_MAXAL_INTERFACES]
                           = {XA_BOOLEAN_TRUE, XA_BOOLEAN_TRUE,           XA_BOOLEAN_TRUE};
    XAInterfaceID iidArray[NB_MAXAL_INTERFACES]
                           = {XA_IID_PLAY,     XA_IID_ANDROIDBUFFERQUEUESOURCE,
                                               XA_IID_STREAMINFORMATION};

    // create media player
    res = (*engineEngine)->CreateMediaPlayer(engineEngine, &playerObj, &dataSrc,
            NULL, &audioSnk, &imageVideoSink, NULL, NULL,
            NB_MAXAL_INTERFACES /*XAuint32 numInterfaces*/,
            iidArray /*const XAInterfaceID *pInterfaceIds*/,
            required /*const XAboolean *pInterfaceRequired*/);
    assert(XA_RESULT_SUCCESS == res);

    // release the Java string and UTF-8
    //(*env)->ReleaseStringUTFChars(env, filename, utf8);

    // realize the player
    res = (*playerObj)->Realize(playerObj, XA_BOOLEAN_FALSE);
    assert(XA_RESULT_SUCCESS == res);

    // get the play interface
    res = (*playerObj)->GetInterface(playerObj, XA_IID_PLAY, &playerPlayItf);
    assert(XA_RESULT_SUCCESS == res);

    // get the stream information interface (for video size)
    res = (*playerObj)->GetInterface(playerObj, XA_IID_STREAMINFORMATION, &playerStreamInfoItf);
    assert(XA_RESULT_SUCCESS == res);

    // get the volume interface
    res = (*playerObj)->GetInterface(playerObj, XA_IID_VOLUME, &playerVolItf);
    assert(XA_RESULT_SUCCESS == res);

    // get the Android buffer queue interface
    res = (*playerObj)->GetInterface(playerObj, XA_IID_ANDROIDBUFFERQUEUESOURCE, &playerBQItf);
    assert(XA_RESULT_SUCCESS == res);

    // specify which events we want to be notified of
    res = (*playerBQItf)->SetCallbackEventsMask(playerBQItf, XA_ANDROIDBUFFERQUEUEEVENT_PROCESSED);
    assert(XA_RESULT_SUCCESS == res);

    // register the callback from which OpenMAX AL can retrieve the data to play
    res = (*playerBQItf)->RegisterCallback(playerBQItf, AndroidBufferQueueCallback, NULL);
    assert(XA_RESULT_SUCCESS == res);

    // we want to be notified of the video size once it's found, so we register a callback for that
    res = (*playerStreamInfoItf)->RegisterStreamChangeCallback(playerStreamInfoItf,
            StreamChangeCallback, NULL);
    assert(XA_RESULT_SUCCESS == res);

    // enqueue the initial buffers
    if (!enqueueInitialBuffers(JNI_FALSE)) {
        return JNI_FALSE;
    }

    // prepare the player
    res = (*playerPlayItf)->SetPlayState(playerPlayItf, XA_PLAYSTATE_PAUSED);
    assert(XA_RESULT_SUCCESS == res);

    // set the volume
    res = (*playerVolItf)->SetVolumeLevel(playerVolItf, 0);
    assert(XA_RESULT_SUCCESS == res);

    // start the playback
    res = (*playerPlayItf)->SetPlayState(playerPlayItf, XA_PLAYSTATE_PLAYING);
        assert(XA_RESULT_SUCCESS == res);

    return JNI_TRUE;
}


// set the playing state for the streaming media player
void Java_com_example_nativemedia_NativeMedia_setPlayingStreamingMediaPlayer(JNIEnv* env,
        jclass clazz, jboolean isPlaying)
{
    XAresult res;

    // make sure the streaming media player was created
    if (NULL != playerPlayItf) {

        // set the player's state
        res = (*playerPlayItf)->SetPlayState(playerPlayItf, isPlaying ?
            XA_PLAYSTATE_PLAYING : XA_PLAYSTATE_PAUSED);
        assert(XA_RESULT_SUCCESS == res);

    }

}


// shut down the native media system
void Java_com_example_nativemedia_NativeMedia_shutdown(JNIEnv* env, jclass clazz)
{
    // destroy streaming media player object, and invalidate all associated interfaces
    if (playerObj != NULL) {
        (*playerObj)->Destroy(playerObj);
        playerObj = NULL;
        playerPlayItf = NULL;
        playerBQItf = NULL;
        playerStreamInfoItf = NULL;
        playerVolItf = NULL;
    }

    // destroy output mix object, and invalidate all associated interfaces
    if (outputMixObject != NULL) {
        (*outputMixObject)->Destroy(outputMixObject);
        outputMixObject = NULL;
    }

    // destroy engine object, and invalidate all associated interfaces
    if (engineObject != NULL) {
        (*engineObject)->Destroy(engineObject);
        engineObject = NULL;
        engineEngine = NULL;
    }

    /* close the file
    if (file != NULL) {
        fclose(file);
        file = NULL;
    }*/
    
    //vincent socket
    LOGV("on va fermer le socket numéro %i", sock);
    close(sock);

    // make sure we don't leak native windows
    if (theNativeWindow != NULL) {
        ANativeWindow_release(theNativeWindow);
        theNativeWindow = NULL;
    }
}


// set the surface
void Java_com_example_nativemedia_NativeMedia_setSurface(JNIEnv *env, jclass clazz, jobject surface)
{
    // obtain a native window from a Java surface
    theNativeWindow = ANativeWindow_fromSurface(env, surface);
}


// rewind the streaming media player
void Java_com_example_nativemedia_NativeMedia_rewindStreamingMediaPlayer(JNIEnv *env, jclass clazz)
{
    XAresult res;
    XAuint32  state;

    if (!playerPlayItf) {
        return;
    }
    res = (*playerPlayItf)->GetPlayState(playerPlayItf, &state);
    assert(XA_RESULT_SUCCESS == res);

    if(state == XA_PLAYSTATE_PAUSED || state == XA_PLAYSTATE_STOPPED) {
        discontinuity = JNI_TRUE;
        return;
    }

    // make sure the streaming media player was created
    if (NULL != playerBQItf && NULL != file) {
        // first wait for buffers currently in queue to be drained
        int ok;
        ok = pthread_mutex_lock(&mutex);
        assert(0 == ok);
        discontinuity = JNI_TRUE;
        // wait for discontinuity request to be observed by buffer queue callback
        // Note: can't rewind after EOS, which we send when reaching EOF
        // (don't send EOS if you plan to play more content through the same player)
        while (discontinuity && !reachedEof) {
            ok = pthread_cond_wait(&cond, &mutex);
            assert(0 == ok);
        }
        ok = pthread_mutex_unlock(&mutex);
        assert(0 == ok);
    }

}
