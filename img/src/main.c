#ifdef __CUSTOMER_CODE__
#include "ril.h"
#include "ril_util.h"
#include "ql_type.h"
#include "ql_gnss.h"
#include "ril_sms.h"
#include "ril_telephony.h"
#include "ril_system.h"
#include "ql_stdlib.h"
#include "ql_error.h"
#include "ql_trace.h"
#include "ql_uart.h"
#include "ql_system.h"
#include "ql_memory.h"
#include "ql_timer.h"
#include "custom_feature_def.h"
#include "nema_pro.h"
#include "ril_gps.h"
#include "ql_socket.h"
#include "math.h"
#include "ril_network.h"
#include "ql_gprs.h"
#include "ril_network.h"
#include "ril_location.h"
#include "ql_timer.h"
#if (defined(__OCPU_RIL_SUPPORT__) && defined(__OCPU_RIL_SMS_SUPPORT__))
#define APN      "CMNET\0"
#define USERID   ""
#define PASSWD   ""
#define DEBUG_ENABLE 1
#if DEBUG_ENABLE > 0
#define DEBUG_PORT  UART_PORT1
#define DBG_BUF_LEN   512
static char DBG_BUFFER[DBG_BUF_LEN];
#define APP_DEBUG(FORMAT,...) {\
    Ql_memset(DBG_BUFFER, 0, DBG_BUF_LEN);\
    Ql_sprintf(DBG_BUFFER,FORMAT,##__VA_ARGS__); \
    if (UART_PORT2 == (DEBUG_PORT)) \
    {\
        Ql_Debug_Trace(DBG_BUFFER);\
    } else {\
        Ql_UART_Write((Enum_SerialPort)(DEBUG_PORT), (u8*)(DBG_BUFFER), Ql_strlen((const char *)(DBG_BUFFER)));\
    }\
}
#else
#define APP_DEBUG(FORMAT,...) 
#endif
#define CON_SMS_BUF_MAX_CNT   (1)
#define CON_SMS_SEG_MAX_CHAR  (160)
#define CON_SMS_SEG_MAX_BYTE  (4 * CON_SMS_SEG_MAX_CHAR)
#define CON_SMS_MAX_SEG       (7)
typedef struct
{
    u8 aData[CON_SMS_SEG_MAX_BYTE];
    u16 uLen;
} ConSMSSegStruct;

typedef struct
{
    u16 uMsgRef;
    u8 uMsgTot;

    ConSMSSegStruct asSeg[CON_SMS_MAX_SEG];
    bool abSegValid[CON_SMS_MAX_SEG];
} ConSMSStruct;
static bool ConSMSBuf_IsIntact(ConSMSStruct *pCSBuf,u8 uCSMaxCnt,u8 uIdx,ST_RIL_SMS_Con *pCon);
static bool ConSMSBuf_AddSeg(ConSMSStruct *pCSBuf,u8 uCSMaxCnt,u8 uIdx,ST_RIL_SMS_Con *pCon,u8 *pData,u16 uLen);
static s8 ConSMSBuf_GetIndex(ConSMSStruct *pCSBuf,u8 uCSMaxCnt,ST_RIL_SMS_Con *pCon);
static bool ConSMSBuf_ResetCtx(ConSMSStruct *pCSBuf,u8 uCSMaxCnt,u8 uIdx);
static void gps_location(char *data, float *lat, float *lon,ticks *rs_new, u8 *hour, u8 *min,u8 *sec, u8 *day,u8 *month, u8 *year);
void gps_speed(char *data,u8 *speed);
ST_LocInfo locinfo;
static void Location_Program(u8 mode);
static void Callback_Location(s32 result,ST_LocInfo* loc_info);
char strPhNum[] = "0909694794\0";
char strreply[] = "hello there\0";
static char IMEI[20];
static char GET_IMEI[20];
static s32 Volt;
static s32 Cap;
char sendGPS[] = "GETLOCATION";
char sendTCP[] = "TRACKING";
char sendinfo[] = "GETINFOR";
#define TIMEOUT_COUNT 2
static u32 Timer_TCP = 0x102;
static u32 ON_Interval = 20000;
static s32 m_param1 = 0;
#define SERIAL_RX_BUFFER_LEN  2048
static u8 m_RxBuf_Uart[SERIAL_RX_BUFFER_LEN];
char pass[]="123456";
float latitude=0;
float longitude=0;
#define APN      "cmnet"
#define USERID   ""
#define PASSWD   ""
/***********************************************************************
 * GLOBAL DATA DEFINITIONS
************************************************************************/
ConSMSStruct g_asConSMSBuf[CON_SMS_BUF_MAX_CNT];
static s8 ConSMSBuf_GetIndex(ConSMSStruct *pCSBuf,u8 uCSMaxCnt,ST_RIL_SMS_Con *pCon)
{
	u8 uIdx = 0;
	
    if(    (NULL == pCSBuf) || (0 == uCSMaxCnt) 
        || (NULL == pCon)
      )
    {
        APP_DEBUG("Enter ConSMSBuf_GetIndex,FAIL! Parameter is INVALID. pCSBuf:%x,uCSMaxCnt:%d,pCon:%x\r\n",pCSBuf,uCSMaxCnt,pCon);
        return -1;
    }

    if((pCon->msgTot) > CON_SMS_MAX_SEG)
    {
        APP_DEBUG("Enter ConSMSBuf_GetIndex,FAIL! msgTot:%d is larger than limit:%d\r\n",pCon->msgTot,CON_SMS_MAX_SEG);
        return -1;
    }
    
	for(uIdx = 0; uIdx < uCSMaxCnt; uIdx++)  //Match all exist records
	{
        if(    (pCon->msgRef == pCSBuf[uIdx].uMsgRef)
            && (pCon->msgTot == pCSBuf[uIdx].uMsgTot)
          )
        {
            return uIdx;
        }
	}

	for (uIdx = 0; uIdx < uCSMaxCnt; uIdx++)
	{
		if (0 == pCSBuf[uIdx].uMsgTot)  //Find the first unused record
		{
            pCSBuf[uIdx].uMsgTot = pCon->msgTot;
            pCSBuf[uIdx].uMsgRef = pCon->msgRef;
            
			return uIdx;
		}
	}

    APP_DEBUG("Enter ConSMSBuf_GetIndex,FAIL! No avail index in ConSMSBuf,uCSMaxCnt:%d\r\n",uCSMaxCnt);
    
	return -1;
}

/*****************************************************************************
 * FUNCTION
 *  ConSMSBuf_AddSeg
 *
 * DESCRIPTION
 *  This function is used to add segment in <pCSBuf>
 *  
 * PARAMETERS
 *  <pCSBuf>     The SMS index in storage,it starts from 1
 *  <uCSMaxCnt>  TRUE: The module should reply a SMS to the sender; FALSE: The module only read this SMS.
 *  <uIdx>       Index of <pCSBuf> which will be stored
 *  <pCon>       The pointer of 'ST_RIL_SMS_Con' data
 *  <pData>      The pointer of CON-SMS-SEG data
 *  <uLen>       The length of CON-SMS-SEG data
 *
 * RETURNS
 *  FALSE:   FAIL!
 *  TRUE: SUCCESS.
 *
 * NOTE
 *  1. This is an internal function
 *****************************************************************************/
static bool ConSMSBuf_AddSeg(ConSMSStruct *pCSBuf,u8 uCSMaxCnt,u8 uIdx,ST_RIL_SMS_Con *pCon,u8 *pData,u16 uLen)
{
    u8 uSeg = 1;
    
    if(    (NULL == pCSBuf) || (0 == uCSMaxCnt) 
        || (uIdx >= uCSMaxCnt)
        || (NULL == pCon)
        || (NULL == pData)
        || (uLen > (CON_SMS_SEG_MAX_CHAR * 4))
      )
    {
        APP_DEBUG("Enter ConSMSBuf_AddSeg,FAIL! Parameter is INVALID. pCSBuf:%x,uCSMaxCnt:%d,uIdx:%d,pCon:%x,pData:%x,uLen:%d\r\n",pCSBuf,uCSMaxCnt,uIdx,pCon,pData,uLen);
        return FALSE;
    }

    if((pCon->msgTot) > CON_SMS_MAX_SEG)
    {
        APP_DEBUG("Enter ConSMSBuf_GetIndex,FAIL! msgTot:%d is larger than limit:%d\r\n",pCon->msgTot,CON_SMS_MAX_SEG);
        return FALSE;
    }

    uSeg = pCon->msgSeg;
    pCSBuf[uIdx].abSegValid[uSeg-1] = TRUE;
    Ql_memcpy(pCSBuf[uIdx].asSeg[uSeg-1].aData,pData,uLen);
    pCSBuf[uIdx].asSeg[uSeg-1].uLen = uLen;
    
	return TRUE;
}

/*****************************************************************************
 * FUNCTION
 *  ConSMSBuf_IsIntact
 *
 * DESCRIPTION
 *  This function is used to check the CON-SMS is intact or not
 *  
 * PARAMETERS
 *  <pCSBuf>     The SMS index in storage,it starts from 1
 *  <uCSMaxCnt>  TRUE: The module should reply a SMS to the sender; FALSE: The module only read this SMS.
 *  <uIdx>       Index of <pCSBuf> which will be stored
 *  <pCon>       The pointer of 'ST_RIL_SMS_Con' data
 *
 * RETURNS
 *  FALSE:   FAIL!
 *  TRUE: SUCCESS.
 *
 * NOTE
 *  1. This is an internal function
 *****************************************************************************/
static bool ConSMSBuf_IsIntact(ConSMSStruct *pCSBuf,u8 uCSMaxCnt,u8 uIdx,ST_RIL_SMS_Con *pCon)
{
    u8 uSeg = 1;
	
    if(    (NULL == pCSBuf) 
        || (0 == uCSMaxCnt) 
        || (uIdx >= uCSMaxCnt)
        || (NULL == pCon)
      )
    {
        APP_DEBUG("Enter ConSMSBuf_IsIntact,FAIL! Parameter is INVALID. pCSBuf:%x,uCSMaxCnt:%d,uIdx:%d,pCon:%x\r\n",pCSBuf,uCSMaxCnt,uIdx,pCon);
        return FALSE;
    }

    if((pCon->msgTot) > CON_SMS_MAX_SEG)
    {
        APP_DEBUG("Enter ConSMSBuf_GetIndex,FAIL! msgTot:%d is larger than limit:%d\r\n",pCon->msgTot,CON_SMS_MAX_SEG);
        return FALSE;
    }
        
	for (uSeg = 1; uSeg <= (pCon->msgTot); uSeg++)
	{
        if(FALSE == pCSBuf[uIdx].abSegValid[uSeg-1])
        {
            APP_DEBUG("Enter ConSMSBuf_IsIntact,FAIL! uSeg:%d has not received!\r\n",uSeg);
            return FALSE;
        }
	}
    
    return TRUE;
}

/*****************************************************************************
 * FUNCTION
 *  ConSMSBuf_ResetCtx
 *
 * DESCRIPTION
 *  This function is used to reset ConSMSBuf context
 *  
 * PARAMETERS
 *  <pCSBuf>     The SMS index in storage,it starts from 1
 *  <uCSMaxCnt>  TRUE: The module should reply a SMS to the sender; FALSE: The module only read this SMS.
 *  <uIdx>       Index of <pCSBuf> which will be stored
 *
 * RETURNS
 *  FALSE:   FAIL!
 *  TRUE: SUCCESS.
 *
 * NOTE
 *  1. This is an internal function
 *****************************************************************************/
static bool ConSMSBuf_ResetCtx(ConSMSStruct *pCSBuf,u8 uCSMaxCnt,u8 uIdx)
{
    if(    (NULL == pCSBuf) || (0 == uCSMaxCnt) 
        || (uIdx >= uCSMaxCnt)
      )
    {
        APP_DEBUG("Enter ConSMSBuf_ResetCtx,FAIL! Parameter is INVALID. pCSBuf:%x,uCSMaxCnt:%d,uIdx:%d\r\n",pCSBuf,uCSMaxCnt,uIdx);
        return FALSE;
    }
    
    //Default reset
    Ql_memset(&pCSBuf[uIdx],0x00,sizeof(ConSMSStruct));

    //TODO: Add special reset here
    
    return TRUE;
}

/*****************************************************************************
 * FUNCTION
 *  SMS_Initialize
 *
 * DESCRIPTION
 *  Initialize SMS environment.
 *  
 * PARAMETERS
 *  VOID
 *
 * RETURNS
 *  TRUE:  This function works SUCCESS.
 *  FALSE: This function works FAIL!
 *****************************************************************************/
static bool SMS_Initialize(void)
{
    s32 iResult = 0;
    u8  nCurrStorage = 0;
    u32 nUsed = 0;
    u32 nTotal = 0;
    
    // Set SMS storage:
    // By default, short message is stored into SIM card. You can change the storage to ME if needed, or
    // you can do it again to make sure the short message storage is SIM card.
    #if 0
    {
        iResult = RIL_SMS_SetStorage(RIL_SMS_STORAGE_TYPE_SM,&nUsed,&nTotal);
        if (RIL_ATRSP_SUCCESS != iResult)
        {
            APP_DEBUG("Fail to set SMS storage, cause:%d\r\n", iResult);
            return FALSE;
        }
        APP_DEBUG("<-- Set SMS storage to SM, nUsed:%u,nTotal:%u -->\r\n", nUsed, nTotal);

        iResult = RIL_SMS_GetStorage(&nCurrStorage, &nUsed ,&nTotal);
        if(RIL_ATRSP_SUCCESS != iResult)
        {
            APP_DEBUG("Fail to get SMS storage, cause:%d\r\n", iResult);
            return FALSE;
        }
        APP_DEBUG("<-- Check SMS storage: curMem=%d, used=%d, total=%d -->\r\n", nCurrStorage, nUsed, nTotal);
    }
    #endif

    // Enable new short message indication
    // By default, the auto-indication for new short message is enalbed. You can do it again to 
    // make sure that the option is open.
    #if 0
    {
        iResult = Ql_RIL_SendATCmd("AT+CNMI=2,1",Ql_strlen("AT+CNMI=2,1"),NULL,NULL,0);
        if (RIL_AT_SUCCESS != iResult)
        {
            APP_DEBUG("Fail to send \"AT+CNMI=2,1\", cause:%d\r\n", iResult);
            return FALSE;
        }
        APP_DEBUG("<-- Enable new SMS indication -->\r\n");
    }
    #endif

    // Delete all existed short messages (if needed)
    iResult = RIL_SMS_DeleteSMS(0, RIL_SMS_DEL_ALL_MSG);
    if (iResult != RIL_AT_SUCCESS)
    {
        APP_DEBUG("Fail to delete all messages, iResult=%d,cause:%d\r\n", iResult, Ql_RIL_AT_GetErrCode());
        return FALSE;
    }
    APP_DEBUG("Delete all existed messages\r\n");
    
    return TRUE;
}

void SMS_TextMode_Read(u32 nIndex)
{
    s32 iResult;
    ST_RIL_SMS_TextInfo *pTextInfo = NULL;
    ST_RIL_SMS_DeliverParam *pDeliverTextInfo = NULL;
    ST_RIL_SMS_SubmitParam *pSubmitTextInfo = NULL;
    LIB_SMS_CharSetEnum eCharSet = LIB_SMS_CHARSET_GSM;
    
    pTextInfo = Ql_MEM_Alloc(sizeof(ST_RIL_SMS_TextInfo));
    if (NULL == pTextInfo)
    {
        return;
    }        

    Ql_memset(pTextInfo,0x00,sizeof(ST_RIL_SMS_TextInfo));
    iResult = RIL_SMS_ReadSMS_Text(nIndex, eCharSet, pTextInfo);
    if (iResult != RIL_AT_SUCCESS)
    {
        Ql_MEM_Free(pTextInfo);
        APP_DEBUG("< Fail to read PDU SMS, cause:%d >\r\n", iResult);
        return;
    }        
    if (RIL_SMS_STATUS_TYPE_INVALID == (pTextInfo->status))
    {
        APP_DEBUG("<-- SMS[index=%d] doesn't exist -->\r\n", nIndex);
        return;
    }

    // Resolve the read short message
    if (LIB_SMS_PDU_TYPE_DELIVER == (pTextInfo->type))
    {
        pDeliverTextInfo = &((pTextInfo->param).deliverParam);
        APP_DEBUG("<-- Read short message (index:%u) with charset %d -->\r\n", nIndex, eCharSet);

        if(FALSE == pDeliverTextInfo->conPres) //Normal SMS
        {
            APP_DEBUG(
                "short message info: \r\n\tstatus:%u \r\n\ttype:%u \r\n\talpha:%u \r\n\tsca:%s \r\n\toa:%s \r\n\tscts:%s \r\n\tdata length:%u\r\ncp:0,cy:0,cr:0,ct:0,cs:0\r\n",
                    (pTextInfo->status),
                    (pTextInfo->type),
                    (pDeliverTextInfo->alpha),
                    (pTextInfo->sca),
                    (pDeliverTextInfo->oa),
                    (pDeliverTextInfo->scts),
                    (pDeliverTextInfo->length)
           );
        }
        else
        {
            APP_DEBUG(
                "short message info: \r\n\tstatus:%u \r\n\ttype:%u \r\n\talpha:%u \r\n\tsca:%s \r\n\toa:%s \r\n\tscts:%s \r\n\tdata length:%u\r\ncp:1,cy:%d,cr:%d,ct:%d,cs:%d\r\n",
                    (pTextInfo->status),
                    (pTextInfo->type),
                    (pDeliverTextInfo->alpha),
                    (pTextInfo->sca),
                    (pDeliverTextInfo->oa),
                    (pDeliverTextInfo->scts),
                    (pDeliverTextInfo->length),
                    pDeliverTextInfo->con.msgType,
                    pDeliverTextInfo->con.msgRef,
                    pDeliverTextInfo->con.msgTot,
                    pDeliverTextInfo->con.msgSeg
           );
        }
        
        APP_DEBUG("\r\n\tmessage content:");
        APP_DEBUG("%s\r\n",(pDeliverTextInfo->data));
        APP_DEBUG("\r\n");
    }
    else if (LIB_SMS_PDU_TYPE_SUBMIT == (pTextInfo->type))
    {// short messages in sent-list of drafts-list
    } else {
        APP_DEBUG("<-- Unkown short message type! type:%d -->\r\n", (pTextInfo->type));
    }
    Ql_MEM_Free(pTextInfo);
}

void SMS_TextMode_Send(void)
{
    /*s32 iResult;
    u32 nMsgRef;
    char strPhNum[] = "0909694794\0";
    char strTextMsg[] = "Quectel Module SMS Test\0";
    ST_RIL_SMS_SendExt sExt;

    //Initialize
    Ql_memset(&sExt,0x00,sizeof(sExt));

    APP_DEBUG("< Send Normal Text SMS begin... >\r\n");
    
    iResult = RIL_SMS_SendSMS_Text(strPhNum, Ql_strlen(strPhNum), LIB_SMS_CHARSET_GSM, strTextMsg, Ql_strlen(strTextMsg), &nMsgRef);
    if (iResult != RIL_AT_SUCCESS)
    {   
        APP_DEBUG("< Fail to send Text SMS, iResult=%d, cause:%d >\r\n", iResult, Ql_RIL_AT_GetErrCode());
        return;
    }
    APP_DEBUG("< Send Text SMS successfully, MsgRef:%u >\r\n", nMsgRef);
	*/
}

void SMS_PDUMode_Read(u32 nIndex)
{
    s32 iResult;
    ST_RIL_SMS_PDUInfo *pPDUInfo = NULL;

    pPDUInfo = Ql_MEM_Alloc(sizeof(ST_RIL_SMS_PDUInfo));
    if (NULL == pPDUInfo)
    {
        return;
    }
    
    iResult = RIL_SMS_ReadSMS_PDU(nIndex, pPDUInfo);
    if (RIL_AT_SUCCESS != iResult)
    {
        Ql_MEM_Free(pPDUInfo);
        APP_DEBUG("< Fail to read PDU SMS, cause:%d >\r\n", iResult);
        return;
    }

    do
    {
        if (RIL_SMS_STATUS_TYPE_INVALID == (pPDUInfo->status))
        {
            APP_DEBUG("<-- SMS[index=%d] doesn't exist -->\r\n", nIndex);
            break;
        }

        APP_DEBUG("<-- Send Text SMS[index=%d] successfully -->\r\n", nIndex);
        APP_DEBUG("status:%u,data length:%u\r\n", (pPDUInfo->status), (pPDUInfo->length));
        APP_DEBUG("data = %s\r\n",(pPDUInfo->data));
    } while(0);
    
    Ql_MEM_Free(pPDUInfo);
}

void SMS_PDUMode_Send(void)
{
    s32 iResult;
    u32 nMsgRef;
    char pduStr[] = "1234923asdf";
    iResult = RIL_SMS_SendSMS_PDU(pduStr, sizeof(pduStr), &nMsgRef);
    if (RIL_AT_SUCCESS != iResult)
    {
        APP_DEBUG("< Fail to send PDU SMS, cause:%d >\r\n", iResult);
        return;
    }
    APP_DEBUG("< Send PDU SMS successfully, MsgRef:%u >\r\n", nMsgRef);

}
static void Hdlr_RecvNewSMS(u32 nIndex, bool bAutoReply)
{
    s32 iResult = 0;
    u32 uMsgRef = 0;
    ST_RIL_SMS_TextInfo *pTextInfo = NULL;
    ST_RIL_SMS_DeliverParam *pDeliverTextInfo = NULL;
    char aPhNum[RIL_SMS_PHONE_NUMBER_MAX_LEN] = {0,};
    const char aReplyCon[] = {"Module has received SMS."};
    bool bResult = FALSE;
    
    pTextInfo = Ql_MEM_Alloc(sizeof(ST_RIL_SMS_TextInfo));
    if (NULL == pTextInfo)
    {
        APP_DEBUG("%s/%d:Ql_MEM_Alloc FAIL! size:%u\r\n", sizeof(ST_RIL_SMS_TextInfo), __func__, __LINE__);
        return;
    }
    Ql_memset(pTextInfo, 0x00, sizeof(ST_RIL_SMS_TextInfo));
    iResult = RIL_SMS_ReadSMS_Text(nIndex, LIB_SMS_CHARSET_GSM, pTextInfo);
    if (iResult != RIL_AT_SUCCESS)
    {
        Ql_MEM_Free(pTextInfo);
        APP_DEBUG("Fail to read text SMS[%d], cause:%d\r\n", nIndex, iResult);
        return;
    }        
    
    if ((LIB_SMS_PDU_TYPE_DELIVER != (pTextInfo->type)) || (RIL_SMS_STATUS_TYPE_INVALID == (pTextInfo->status)))
    {
        Ql_MEM_Free(pTextInfo);
        APP_DEBUG("WARNING: NOT a new received SMS.\r\n");    
        return;
    }
    
    pDeliverTextInfo = &((pTextInfo->param).deliverParam);    

    if(TRUE == pDeliverTextInfo->conPres)  //Receive CON-SMS segment
    {
        s8 iBufIdx = 0;
        u8 uSeg = 0;
        u16 uConLen = 0;

        iBufIdx = ConSMSBuf_GetIndex(g_asConSMSBuf,CON_SMS_BUF_MAX_CNT,&(pDeliverTextInfo->con));
        if(-1 == iBufIdx)
        {
            APP_DEBUG("Enter Hdlr_RecvNewSMS,WARNING! ConSMSBuf_GetIndex FAIL! Show this CON-SMS-SEG directly!\r\n");

            APP_DEBUG(
                "status:%u,type:%u,alpha:%u,sca:%s,oa:%s,scts:%s,data length:%u,cp:1,cy:%d,cr:%d,ct:%d,cs:%d\r\n",
                    (pTextInfo->status),
                    (pTextInfo->type),
                    (pDeliverTextInfo->alpha),
                    (pTextInfo->sca),
                    (pDeliverTextInfo->oa),
                    (pDeliverTextInfo->scts),
                    (pDeliverTextInfo->length),
                    pDeliverTextInfo->con.msgType,
                    pDeliverTextInfo->con.msgRef,
                    pDeliverTextInfo->con.msgTot,
                    pDeliverTextInfo->con.msgSeg
            );
            APP_DEBUG("data = %s\r\n",(pDeliverTextInfo->data));
            APP_DEBUG("NUMBER PHONE1 : %s\r\n",(pDeliverTextInfo->oa));

            Ql_MEM_Free(pTextInfo);
        
            return;
        }

        bResult = ConSMSBuf_AddSeg(
                    g_asConSMSBuf,
                    CON_SMS_BUF_MAX_CNT,
                    iBufIdx,
                    &(pDeliverTextInfo->con),
                    (pDeliverTextInfo->data),
                    (pDeliverTextInfo->length)
        );
        if(FALSE == bResult)
        {
            APP_DEBUG("Enter Hdlr_RecvNewSMS,WARNING! ConSMSBuf_AddSeg FAIL! Show this CON-SMS-SEG directly!\r\n");

            APP_DEBUG(
                "status:%u,type:%u,alpha:%u,sca:%s,oa:%s,scts:%s,data length:%u,cp:1,cy:%d,cr:%d,ct:%d,cs:%d\r\n",
                (pTextInfo->status),
                (pTextInfo->type),
                (pDeliverTextInfo->alpha),
                (pTextInfo->sca),
                (pDeliverTextInfo->oa),
                (pDeliverTextInfo->scts),
                (pDeliverTextInfo->length),
                pDeliverTextInfo->con.msgType,
                pDeliverTextInfo->con.msgRef,
                pDeliverTextInfo->con.msgTot,
                pDeliverTextInfo->con.msgSeg
            );
            APP_DEBUG("data = %s\r\n",(pDeliverTextInfo->data));

            Ql_MEM_Free(pTextInfo);
        
            return;
        }

        bResult = ConSMSBuf_IsIntact(
                    g_asConSMSBuf,
                    CON_SMS_BUF_MAX_CNT,
                    iBufIdx,
                    &(pDeliverTextInfo->con)
        );
        if(FALSE == bResult)
        {
            APP_DEBUG(
                "Enter Hdlr_RecvNewSMS,WARNING! ConSMSBuf_IsIntact FAIL! Waiting. cp:1,cy:%d,cr:%d,ct:%d,cs:%d\r\n",
                pDeliverTextInfo->con.msgType,
                pDeliverTextInfo->con.msgRef,
                pDeliverTextInfo->con.msgTot,
                pDeliverTextInfo->con.msgSeg
            );

            Ql_MEM_Free(pTextInfo);

            return;
        }

        //Show the CON-SMS
        APP_DEBUG(
            "status:%u,type:%u,alpha:%u,sca:%s,oa:%s,scts:%s",
            (pTextInfo->status),
            (pTextInfo->type),
            (pDeliverTextInfo->alpha),
            (pTextInfo->sca),
            (pDeliverTextInfo->oa),
            (pDeliverTextInfo->scts)
        );
        
        uConLen = 0;
        for(uSeg = 1; uSeg <= pDeliverTextInfo->con.msgTot; uSeg++)
        {
            uConLen += g_asConSMSBuf[iBufIdx].asSeg[uSeg-1].uLen;
        }

        APP_DEBUG(",data length:%u",uConLen);
        APP_DEBUG("\r\n"); //Print CR LF

        for(uSeg = 1; uSeg <= pDeliverTextInfo->con.msgTot; uSeg++)
        {
            APP_DEBUG("data = %s ,len = %d",
                g_asConSMSBuf[iBufIdx].asSeg[uSeg-1].aData,
                g_asConSMSBuf[iBufIdx].asSeg[uSeg-1].uLen
            );
        }

        APP_DEBUG("\r\n"); 
        bResult = ConSMSBuf_ResetCtx(g_asConSMSBuf,CON_SMS_BUF_MAX_CNT,iBufIdx);
        if(FALSE == bResult)
        {
            APP_DEBUG("Enter Hdlr_RecvNewSMS,WARNING! ConSMSBuf_ResetCtx FAIL! iBufIdx:%d\r\n",iBufIdx);
        }

        Ql_MEM_Free(pTextInfo);
        
        return;
    }
    
    APP_DEBUG("<-- RIL_SMS_ReadSMS_Text OK. eCharSet:LIB_SMS_CHARSET_GSM,nIndex:%u -->\r\n",nIndex);
    APP_DEBUG("status:%u,type:%u,alpha:%u,sca:%s,oa:%s,scts:%s,data length:%u\r\n",
        pTextInfo->status,
        pTextInfo->type,
        pDeliverTextInfo->alpha,
        pTextInfo->sca,
        pDeliverTextInfo->oa,
        pDeliverTextInfo->scts,
        pDeliverTextInfo->length);
    APP_DEBUG("data = %s\r\n",(pDeliverTextInfo->data));
    APP_DEBUG("NUMBER PHONE2 : %s\r\n",(pDeliverTextInfo->oa));
    Ql_strcpy(aPhNum, pDeliverTextInfo->oa);
    APP_DEBUG("NUMBER PHONE3 : %s",aPhNum);
    Ql_MEM_Free(pTextInfo);

char *ptr=0, *ptr_config;
char control[] = "MIOT";
ptr =Ql_strstr(pDeliverTextInfo->data,control);
if(Ql_strncmp(ptr,control,4)==0)
{
if(ptr[5]==pass[0],ptr[6]==pass[1],ptr[7]==pass[2],ptr[8]==pass[3],ptr[9]==pass[4],ptr[10]==pass[5])
{
APP_DEBUG("\n---CORRECT---");
ptr_config = Ql_strstr(pDeliverTextInfo->data,sendGPS);
if(Ql_strncmp(ptr_config,sendGPS,11)==0)
{
s32 iRet = 0;
s32 yRet = 0;
u8 rdBuff_GPS[1000];
u8 Report_data[74];
u8 hour,min,sec,day,month,year,speed;
float lat =0, lon=0;
				ticks rs_new;
				Ql_memset(Report_data,0,sizeof(Report_data));
            	Ql_memset(rdBuff_GPS,0,sizeof(rdBuff_GPS));
            	iRet = RIL_GPS_Read("RMC",rdBuff_GPS);
				gps_location(rdBuff_GPS, &lat, &lon,&rs_new,&hour,&min,&sec,&day,&month,&year);
            	//APP_DEBUG("%s\r\n",rdBuff_GPS);
				u8 rdBuff_VTG[1000];
            	Ql_memset(rdBuff_VTG,0,sizeof(rdBuff_VTG));
            	yRet = RIL_GPS_Read("VTG",rdBuff_VTG);
				gps_speed(rdBuff_VTG,&speed);
                Location_Program(0);
                APP_DEBUG("<--Module location: latitude=%f, longitude=%f -->\r\n", locinfo.latitude, locinfo.longitude);
				Ql_sprintf(Report_data,"GPS: http://maps.google.com/maps?q=%.6f,%.6f&t=m&z=36\r\nAGPS: http://maps.google.com/maps?q=%.6f,%.6f&t=m&z=36 ",lon,lat,locinfo.latitude,locinfo.longitude);
				APP_DEBUG(Report_data);
u32 nMsgRef;
ST_RIL_SMS_SendExt sExt;
Ql_memset(&sExt,0x00,sizeof(sExt));

    APP_DEBUG("< Send SMS GPS... >\r\n");
    
    iResult = RIL_SMS_SendSMS_Text(aPhNum, Ql_strlen(aPhNum), LIB_SMS_CHARSET_GSM, Report_data, Ql_strlen(Report_data), &nMsgRef);
    if (iResult != RIL_AT_SUCCESS)
    {   
        APP_DEBUG("< Fail to send Text SMS, iResult=%d, cause:%d >\r\n", iResult, Ql_RIL_AT_GetErrCode());
        return;
    }
    APP_DEBUG("< Send Text SMS successfully, MsgRef:%u >\r\n", nMsgRef); 
    if (bAutoReply)
    {
        if (!Ql_strstr(aPhNum, "10086"))  // Not reply SMS from operator
        {
            APP_DEBUG("<-- Replying SMS... -->\r\n");
            iResult = RIL_SMS_SendSMS_Text(aPhNum, Ql_strlen(aPhNum),LIB_SMS_CHARSET_GSM,(u8*)aReplyCon,Ql_strlen(aReplyCon),&uMsgRef);
            if (iResult != RIL_AT_SUCCESS)
            {
                APP_DEBUG("RIL_SMS_SendSMS_Text FAIL! iResult:%u\r\n",iResult);
                return;
            }
            APP_DEBUG("<-- RIL_SMS_SendTextSMS OK. uMsgRef:%d -->\r\n", uMsgRef);
        }
    }
    return;
}
ptr_config = Ql_strstr(pDeliverTextInfo->data,sendTCP);
if(Ql_strncmp(ptr_config,sendTCP,8)==0)
{
s32 xRet = Ql_Timer_Start(Timer_TCP,ON_Interval,TRUE);
APP_DEBUG("...Timer is on...\r\n")
}



ptr_config = Ql_strstr(pDeliverTextInfo->data,sendinfo);
if(Ql_strncmp(ptr_config,sendinfo,8)==0)
{
    s32 iRet = 0;
    u8 Report_info[50];
    Ql_memset(GET_IMEI, 0x0, sizeof(GET_IMEI));
        	    iRet = RIL_GetIMEI(GET_IMEI);
        	    Ql_strncpy(IMEI,GET_IMEI+2,15);
               // APP_DEBUG("<-- IMEI: %s,-->\r\n", IMEI);
    s32 tRet = RIL_GetPowerSupply(&Cap,&Volt);
               // APP_DEBUG("<-- Cap :%d, voltage:%d -->\r\n",Cap,Volt);
    Ql_memset(Report_info,0,sizeof(Report_info));
    Ql_sprintf(Report_info,"IMEI : %s \r\nBATERY VOLTAGE: %d mV\r\nCAPACITY: %d uF",IMEI,Volt,Cap);
    u32 nMsgRef;
    ST_RIL_SMS_SendExt sExt;
    Ql_memset(&sExt,0x00,sizeof(sExt));

    APP_DEBUG("< Send SMS GPS... >\r\n");
    
    iResult = RIL_SMS_SendSMS_Text(aPhNum, Ql_strlen(aPhNum), LIB_SMS_CHARSET_GSM, Report_info, Ql_strlen(Report_info), &nMsgRef);
    if (iResult != RIL_AT_SUCCESS)
    {   
        APP_DEBUG("< Fail to send Text SMS, iResult=%d, cause:%d >\r\n", iResult, Ql_RIL_AT_GetErrCode());
        return;
    }
    APP_DEBUG("< Send Text SMS successfully, MsgRef:%u >\r\n", nMsgRef); 
    if (bAutoReply)
    {
        if (!Ql_strstr(aPhNum, "10086"))  // Not reply SMS from operator
        {
            APP_DEBUG("<-- Replying SMS... -->\r\n");
            iResult = RIL_SMS_SendSMS_Text(aPhNum, Ql_strlen(aPhNum),LIB_SMS_CHARSET_GSM,(u8*)aReplyCon,Ql_strlen(aReplyCon),&uMsgRef);
            if (iResult != RIL_AT_SUCCESS)
            {
                APP_DEBUG("RIL_SMS_SendSMS_Text FAIL! iResult:%u\r\n",iResult);
                return;
            }
            APP_DEBUG("<-- RIL_SMS_SendTextSMS OK. uMsgRef:%d -->\r\n", uMsgRef);
        }
    }
    return;

}
}

}
}

static s32 ReadSerialPort(Enum_SerialPort port, /*[out]*/u8* pBuffer, /*[in]*/u32 bufLen)
{
    s32 rdLen = 0;
    s32 rdTotalLen = 0;
    if (NULL == pBuffer || 0 == bufLen)
    {
        return -1;
    }
    Ql_memset(pBuffer, 0x0, bufLen);
    while (1)
    {
        rdLen = Ql_UART_Read(port, pBuffer + rdTotalLen, bufLen - rdTotalLen);
        if (rdLen <= 0)  // All data is read out, or Serial Port Error!
        {
            break;
        }
        rdTotalLen += rdLen;
        // Continue to read...
    }
    if (rdLen < 0) // Serial Port Error!
    {
        APP_DEBUG("<--Fail to read from port[%d]-->\r\n", port);
        return -99;
    }
    return rdTotalLen;
}
void Callback_GPS_CMD_Hdlr(char *str_URC)
{
	if(str_URC != NULL)
	{
		APP_DEBUG("%s", str_URC);
	}
}
static void CallBack_UART_Hdlr(Enum_SerialPort port, Enum_UARTEventType msg, bool level, void* customizedPara)
{
 s32 iRet = 0;
	s32 yRet = 0;
    s32 tRet = 0;
    switch (msg)
    {
        case EVENT_UART_READY_TO_READ:
        {
            char* p = NULL;
            s32 totalBytes = ReadSerialPort(port, m_RxBuf_Uart, sizeof(m_RxBuf_Uart));
            if (totalBytes <= 0)
            {
                break;
            }
			p = Ql_strstr(m_RxBuf_Uart, "RESET");
            if(p)
            {
            	Ql_Reset(0);
				break;
             }
            p = Ql_strstr(m_RxBuf_Uart, "IMEI");
            if(p)
            {
                Ql_memset(GET_IMEI, 0x0, sizeof(GET_IMEI));
        	    iRet = RIL_GetIMEI(GET_IMEI);
        	    Ql_strncpy(IMEI,GET_IMEI+2,15);
                APP_DEBUG("<-- IMEI: %s,-->\r\n", IMEI);
                tRet = RIL_GetPowerSupply(&Cap,&Volt);
                APP_DEBUG("<-- Cap :%d, voltage:%d -->\r\n",Cap,Volt);
                break;
            }
            p = Ql_strstr(m_RxBuf_Uart, "GSM");
            if(p)
            {
            	u32 rssi;
            	u32 ber;
            	s32 nRet = RIL_NW_GetSignalQuality(&rssi, &ber);
            	APP_DEBUG("<-- Signal strength:%d, BER:%d -->\r\n", rssi, ber);
                break;
            }
            p = Ql_strstr(m_RxBuf_Uart, "GPS");
            if(p)
            {
            	u8 rdBuff_GPS[1000];
				u8 hour,min,sec,day,month,year,speed;
				float lat =0, lon=0;
				ticks rs_new;
            	Ql_memset(rdBuff_GPS,0,sizeof(rdBuff_GPS));
            	iRet = RIL_GPS_Read("RMC",rdBuff_GPS);
				gps_location(rdBuff_GPS, &lat, &lon,&rs_new,&hour,&min,&sec,&day,&month,&year);
            	//APP_DEBUG("%s\r\n",rdBuff_GPS);
				u8 rdBuff_VTG[1000];
            	Ql_memset(rdBuff_VTG,0,sizeof(rdBuff_VTG));
            	yRet = RIL_GPS_Read("VTG",rdBuff_VTG);
				gps_speed(rdBuff_VTG,&speed);
				APP_DEBUG("<--Position :%f:%f-->\r\n",lon,lat);
				APP_DEBUG("<--Speed :%.2f-->\r\n",speed);
            	//APP_DEBUG("%s\r\n",rdBuff_VTG);
                break;
            }
            p = Ql_strstr(m_RxBuf_Uart, "GET_LOCATION");
            if(p)
            {
                Location_Program(0);
                break;
            }
            p = Ql_strstr(m_RxBuf_Uart, "GET_BYCELL");
            if(p)
            {
                Location_Program(1);
                break;
            }

            APP_DEBUG("<--ERROR-->\r\n");
        }break;

        case EVENT_UART_READY_TO_WRITE:
        {
            //...
        }break;

        default:
        break;
    }

}
static void InitSerialPort(void)
{
    s32 iResult = 0;

    //Register & Open UART port
    iResult = Ql_UART_Register(UART_PORT1, CallBack_UART_Hdlr, NULL);
    if (iResult != QL_RET_OK)
    {
        Ql_Debug_Trace("Fail to register UART port[%d]:%d\r\n",UART_PORT1);
    }
    
    iResult = Ql_UART_Open(UART_PORT1, 115200, FC_NONE);
    if (iResult != QL_RET_OK)
    {
        Ql_Debug_Trace("Fail to open UART port[%d], baud rate:115200, FC_NONE\r\n", UART_PORT1);
    }    
}

/*****************************************************************************
 * FUNCTION
 *  proc_main_task
 *
 * DESCRIPTION
 *  Entry function of this example.
 *  
 * PARAMETERS
 *  <iTaskID>  Task ID
 *
 * RETURNS
 *  VOID
 *
 * NOTE
 *  1. This is the entrance to application
 *****************************************************************************/
void proc_main_task(s32 iTaskID)
{
    s32 iResult = 0;
    ST_MSG taskMsg;

    //Register & open UART port
    InitSerialPort();
    
    APP_DEBUG("OpenCPU: SMS Example\r\n");
    iResult = Ql_Timer_Register(Timer_TCP,ON_Interval,&m_param1);
    if(iResult<0)
    {
        APP_DEBUG("...Register timer fail...\r\n")
    }
    // START MESSAGE LOOP OF THIS TASK
    while (TRUE) 
    {
        s32 i = 0;
    
        Ql_memset(&taskMsg, 0x0, sizeof(ST_MSG));
        Ql_OS_GetMessage(&taskMsg);
        switch (taskMsg.message)
        {
        case MSG_ID_RIL_READY:
            {
                APP_DEBUG("<-- RIL is ready -->\r\n");
                Ql_RIL_Initialize(); // MUST call this function
				RIL_GPS_Open(1);
                for(i = 0; i < CON_SMS_BUF_MAX_CNT; i++)
                {
                    ConSMSBuf_ResetCtx(g_asConSMSBuf,CON_SMS_BUF_MAX_CNT,i);
                }
                
                break;
            }
        case MSG_ID_URC_INDICATION:
            switch (taskMsg.param1)
            {
            case URC_SYS_INIT_STATE_IND:
                {
                    APP_DEBUG("<-- Sys Init Status %d -->\r\n", taskMsg.param2);
                    if (SYS_STATE_SMSOK == taskMsg.param2)
                    {
                        APP_DEBUG("\r\n<-- SMS module is ready -->\r\n");
                        APP_DEBUG("\r\n<-- Initialize SMS-related options -->\r\n");
                        iResult = SMS_Initialize();         
                        if (!iResult)
                        {
                            APP_DEBUG("Fail to initialize SMS\r\n");
                        }

                        SMS_TextMode_Send();
                    }
                    break;
                }
            case URC_SIM_CARD_STATE_IND:
                {
                    APP_DEBUG("\r\n<-- SIM Card Status:%d -->\r\n", taskMsg.param2);
                }
                break;

            case URC_GSM_NW_STATE_IND:
                {
                    APP_DEBUG("\r\n<-- GSM Network Status:%d -->\r\n", taskMsg.param2);
                    break;
                }

            case URC_GPRS_NW_STATE_IND:
                {
                    APP_DEBUG("\r\n<-- GPRS Network Status:%d -->\r\n", taskMsg.param2);
                    break;
                }

            case URC_CFUN_STATE_IND:
                {
                    APP_DEBUG("\r\n<-- CFUN Status:%d -->\r\n", taskMsg.param2);
                    break;
                }

            case URC_COMING_CALL_IND:
                {
                    ST_ComingCall* pComingCall = (ST_ComingCall*)(taskMsg.param2);
                    APP_DEBUG("\r\n<-- Coming call, number:%s, type:%d -->\r\n", pComingCall->phoneNumber, pComingCall->type);
                    break;
               }

            case URC_NEW_SMS_IND:
                {
                    APP_DEBUG("\r\n<-- New SMS Arrives: index=%d\r\n", taskMsg.param2);
                    Hdlr_RecvNewSMS((taskMsg.param2), FALSE);
                    break;
                }

            case URC_MODULE_VOLTAGE_IND:
                {
                    APP_DEBUG("\r\n<-- VBatt Voltage Ind: type=%d\r\n", taskMsg.param2);
                    break;
                }

            default:
                break;
            }
            break;

        default:
            break;
        }
    }
}
void gps_speed(char *data,u8 *speed){
	//$GNVTG,256.96,T,,M,0.01,N,0.02,K,D*2B
	u8								i, id_comma, id_text;
	char								buff[6];
	float								speed_new;
	static float						speed_old[2] = {0, 0};

	id_text = 0;
	id_comma = 0;
	Ql_memset(buff, '\x00', 6);
	for(i = 0; i < strlen(data); i++){
		if(data[i] == ','){
			id_text = 0;
			id_comma += 1;
		}
		else if(id_comma == 7){
			buff[id_text++] = data[i];
		}
	}
	if(buff[0] == '\x00')
		speed_new = 0;
	else
		Ql_sscanf(buff,"%f", &speed_new);

	*speed = (u8)((speed_new + speed_old[0] + speed_old[1])/3);
	speed_old[1] = speed_old[0];
	speed_old[0] = speed_new;
}
float gps_convert(char *data){
	signed int					i1, i2;
	float						sign;

	Ql_sscanf(data, "%d.%d", &i1, &i2);

	sign = ((int)(i1%100) + (float)i2 / 10000)/60;
	sign += (int)i1/100;
	return sign;
}
const u8 data_month[12]={31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
static void gps_location(char *data, float *lat, float *lon,ticks *rs_new, u8 *hour, u8 *min,u8 *sec, u8 *day,u8 *month, u8 *year)
{
	//$GNRMC,083653.191,A,1050.0913,N,10640.1431,E,0.18,0.00,030818,,,A*72
	u8								i, id_comma, id_text;
	char							buff[4][11+1];//time, date, longitude, latitude
	id_text = 0;
	id_comma = 0;
	Ql_memset(buff[0], '\x00', 11);
	Ql_memset(buff[1], '\x00', 11);
	Ql_memset(buff[2], '\x00', 11);
	Ql_memset(buff[3], '\x00', 11);
	for(i = 0; i < Ql_strlen(data); i++){
		if(data[i] == ','){
			id_text = 0;
			id_comma += 1;
		}
		/*get time*/
		else if(id_comma == 1){
			buff[0][id_text++] = data[i];
		}
		/*lay kinh do*/
		else if(id_comma == 3){
			buff[2][id_text++] = data[i];
		}

		/*Lay vi do*/
		else if(id_comma == 5){
			buff[3][id_text++] = data[i];
		}
		/*Lay ngay*/
		else if(id_comma == 9){
			buff[1][id_text++] = data[i];
		}
	}

	if(buff[0][0] == '\x00' || buff[1][0] == '\x00')
		return;
	/*chuyen doi thoi gian*/
	*hour = (buff[0][0]-48)*10 + buff[0][1]-48;
	*min = (buff[0][2]-48)*10 + buff[0][3]-48;
	*sec = (buff[0][4]-48)*10 + buff[0][5]-48;
	/*chuyen doi thoi gian*/
	*day = (buff[1][0]-48)*10 + buff[1][1]-48;
	*month = (buff[1][2]-48)*10 + buff[1][3]-48;
	*year = (buff[1][4]-48)*10 + buff[1][5]-48;
	if((*hour += 7) > 23){
			*hour -= 24;
			u8 leap_month = data_month[*month];
			if(*year % 4 == 0)
				leap_month += 1;
			if((*day += 1) > leap_month){
				if((*month += 1) > 12){
					*year += 1;
				}
			}
		}

	if(buff[2][0] == '\x00' || buff[3][0] == '\x00'){
		//location_gps_report_data(0, 0);
		return;
	}
	/*lay gia tri vi tri*/
	*lon = gps_convert(buff[2]);
	*lat = gps_convert(buff[3]);
	static float				long_old = 0;
	static float				lat_old = 0;
	float						long_new, lat_new;
	float						rs,rs_1, rs_2, rs_3;
    #define dec_2_rad(val)			(((double)val*3.14)/180)
	lat_new = dec_2_rad(*lon);
	long_new = dec_2_rad(*lat);

		if(long_old != 0 && lat_old != 0 && long_new != 0 && lat_new != 0){
			rs_1 = sin(long_old - long_new) * cos(lat_new);
			rs_2 = cos(lat_old)*sin(lat_new);
			rs_3 = sin(lat_old)*cos(lat_new)*cos(long_old - long_new);
			rs = -atan2(rs_1, rs_2 - rs_3);
			if(rs < 0)
				rs = rs + 3.14 * 2;
				rs = (rs*180)/3.14;
				*rs_new = rs;
		}

	long_old = long_new;
	lat_old = lat_new;
}
static void Location_Program(u8 mode)
{
	s32 ret;
	u8  pdpCntxtId;

    u8 asynch = 0;
	ST_CellInfo GetLocation;
	GetLocation.cellId = 22243;
	GetLocation.lac = 21764;
	GetLocation.mnc = 01;
	GetLocation.mcc = 460;
	GetLocation.rssi = 0;
	GetLocation.timeAd = 0;

	// Set PDP context
	ret = Ql_GPRS_GetPDPContextId();
	APP_DEBUG("<-- The PDP context id available is: %d (can be 0 or 1)-->\r\n", ret);
	if (ret >= 0)
	{
	    pdpCntxtId = (u8)ret;
	} else {
    	APP_DEBUG("<-- Fail to get PDP context id, try to use PDP id(0) -->\r\n");
	    pdpCntxtId = 0;
	}

	ret = RIL_NW_SetGPRSContext(pdpCntxtId);
	APP_DEBUG("<-- Set PDP context id to %d -->\r\n", pdpCntxtId);
	if (ret != RIL_AT_SUCCESS)
	{
	    APP_DEBUG("<-- Ql_RIL_SendATCmd error  ret=%d-->\r\n",ret );
	}

	// Set APN
	ret = RIL_NW_SetAPN(1, APN, USERID, PASSWD);
	APP_DEBUG("<-- Set APN -->\r\n");

    //PDP activated
    ret = RIL_NW_OpenPDPContext();
    if (ret == RIL_AT_SUCCESS)
	{
	    APP_DEBUG("<--PDPContext activated ret=%d-->\r\n",ret );
	}

	// Request to get location
	APP_DEBUG("<-- Getting module location... -->\r\n");
	if(mode==0)
	{
        if(asynch == 1)
        {
    		APP_DEBUG("<--Ql_Getlocation-->\r\n");
    		ret = RIL_GetLocation(Callback_Location);
            //ret = RIL_NW_ClosePDPContext();
    		if(ret != RIL_AT_SUCCESS)
    		{
    			APP_DEBUG("<-- Ql_Getlocation error  ret=%d-->\r\n",ret );
                ret = RIL_NW_ClosePDPContext();
    		}
        }
        else if(asynch == 0)
        {
            ret = RIL_GetLocation_Ex(&locinfo);
    		if(ret == RIL_AT_SUCCESS)
    		{
    			APP_DEBUG("<-- Getlocation succeed  ret=%d-->\r\n",ret );
                APP_DEBUG("<--Module location: latitude=%f, longitude=%f -->\r\n", locinfo.latitude, locinfo.longitude);
                ret = RIL_NW_ClosePDPContext();
    		}
        }
	}
	else if(mode==1)
	{
		APP_DEBUG("<--Ql_GetlocationByCell-->\r\n");
		ret = RIL_GetLocationByCell(&GetLocation,Callback_Location);
		if(ret!=RIL_AT_SUCCESS)
		{
			APP_DEBUG("<-- Ql_GetlocationByCell error  ret=%d-->\r\n",ret );
		}
	}
}

void Callback_Location(s32 result, ST_LocInfo* loc_info)
{
    APP_DEBUG("\r\n<--result = %d ,Module location: latitude=%f, longitude=%f -->\r\n",result, loc_info->latitude, loc_info->longitude);
}

void Timer_handler(u32 timerId, void* param)
{
    *((s32*)param) +=1;
    if(Timer_TCP == timerId)
    {
        APP_DEBUG("<-- stack Timer_handler, param:%d -->\r\n", *((s32*)param));
        // stack_timer repeat        
    }

}

#endif  // __OCPU_RIL_SUPPORT__ && __OCPU_RIL_SMS_SUPPORT__
#endif  //__EXAMPLE_ALARM__