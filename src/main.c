//#ifdef __CUSTOMER_CODE__
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
//#if (defined(__OCPU_RIL_SUPPORT__) && defined(__OCPU_RIL_SMS_SUPPORT__))
#define APN "CMNET\0"
#define USERID ""
#define PASSWD ""
#define DEBUG_ENABLE 1
#if DEBUG_ENABLE > 0
#define DEBUG_PORT UART_PORT1
#define DBG_BUF_LEN 512
static char DBG_BUFFER[DBG_BUF_LEN];
#define APP_DEBUG(FORMAT, ...)                                                                                       \
    {                                                                                                                \
        Ql_memset(DBG_BUFFER, 0, DBG_BUF_LEN);                                                                       \
        Ql_sprintf(DBG_BUFFER, FORMAT, ##__VA_ARGS__);                                                               \
        if (UART_PORT2 == (DEBUG_PORT))                                                                              \
        {                                                                                                            \
            Ql_Debug_Trace(DBG_BUFFER);                                                                              \
        }                                                                                                            \
        else                                                                                                         \
        {                                                                                                            \
            Ql_UART_Write((Enum_SerialPort)(DEBUG_PORT), (u8 *)(DBG_BUFFER), Ql_strlen((const char *)(DBG_BUFFER))); \
        }                                                                                                            \
    }
#else
#define APP_DEBUG(FORMAT, ...)
#endif
#define CON_SMS_BUF_MAX_CNT (1)
#define CON_SMS_SEG_MAX_CHAR (160)
#define CON_SMS_SEG_MAX_BYTE (4 * CON_SMS_SEG_MAX_CHAR)
#define CON_SMS_MAX_SEG (7)
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
static bool ConSMSBuf_IsIntact(ConSMSStruct *pCSBuf, u8 uCSMaxCnt, u8 uIdx, ST_RIL_SMS_Con *pCon);
static bool ConSMSBuf_AddSeg(ConSMSStruct *pCSBuf, u8 uCSMaxCnt, u8 uIdx, ST_RIL_SMS_Con *pCon, u8 *pData, u16 uLen);
static s8 ConSMSBuf_GetIndex(ConSMSStruct *pCSBuf, u8 uCSMaxCnt, ST_RIL_SMS_Con *pCon);
static bool ConSMSBuf_ResetCtx(ConSMSStruct *pCSBuf, u8 uCSMaxCnt, u8 uIdx);
static void gps_location(char *data, float *lat, float *lon, ticks *rs_new, u8 *hour, u8 *min, u8 *sec, u8 *day, u8 *month, u8 *year);
void gps_speed(char *data, u8 *speed);
ST_LocInfo locinfo;
char strPhNum[] = "0909694794\0";
char strreply[] = "hello there\0";
static char IMEI[20];
static char GET_IMEI[20];
static s32 Volt;
static s32 Cap;
static char Number[15];
char sendGPS[] = "GETLOCATION";
char sendTCP[] = "TRACKING";
char sendinfo[] = "GETINFOR";
#define SERIAL_RX_BUFFER_LEN 2048
static u8 m_RxBuf_Uart[SERIAL_RX_BUFFER_LEN];
char pass[] = "123456";
float latitude = 0;
float longitude = 0;
#define APN "cmnet"
#define USERID ""
#define PASSWD ""
/***********************************************************************
 * GLOBAL DATA DEFINITIONS
 ************************************************************************/
ConSMSStruct g_asConSMSBuf[CON_SMS_BUF_MAX_CNT];
static s8 ConSMSBuf_GetIndex(ConSMSStruct *pCSBuf, u8 uCSMaxCnt, ST_RIL_SMS_Con *pCon)
{
    u8 uIdx = 0;

    if ((NULL == pCSBuf) || (0 == uCSMaxCnt) || (NULL == pCon))
    {
        APP_DEBUG("Enter ConSMSBuf_GetIndex,FAIL! Parameter is INVALID. pCSBuf:%x,uCSMaxCnt:%d,pCon:%x\r\n", pCSBuf, uCSMaxCnt, pCon);
        return -1;
    }

    if ((pCon->msgTot) > CON_SMS_MAX_SEG)
    {
        APP_DEBUG("Enter ConSMSBuf_GetIndex,FAIL! msgTot:%d is larger than limit:%d\r\n", pCon->msgTot, CON_SMS_MAX_SEG);
        return -1;
    }

    for (uIdx = 0; uIdx < uCSMaxCnt; uIdx++) // Match all exist records
    {
        if ((pCon->msgRef == pCSBuf[uIdx].uMsgRef) && (pCon->msgTot == pCSBuf[uIdx].uMsgTot))
        {
            return uIdx;
        }
    }

    for (uIdx = 0; uIdx < uCSMaxCnt; uIdx++)
    {
        if (0 == pCSBuf[uIdx].uMsgTot) // Find the first unused record
        {
            pCSBuf[uIdx].uMsgTot = pCon->msgTot;
            pCSBuf[uIdx].uMsgRef = pCon->msgRef;

            return uIdx;
        }
    }

    APP_DEBUG("Enter ConSMSBuf_GetIndex,FAIL! No avail index in ConSMSBuf,uCSMaxCnt:%d\r\n", uCSMaxCnt);

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
static bool ConSMSBuf_AddSeg(ConSMSStruct *pCSBuf, u8 uCSMaxCnt, u8 uIdx, ST_RIL_SMS_Con *pCon, u8 *pData, u16 uLen)
{
    u8 uSeg = 1;

    if ((NULL == pCSBuf) || (0 == uCSMaxCnt) || (uIdx >= uCSMaxCnt) || (NULL == pCon) || (NULL == pData) || (uLen > (CON_SMS_SEG_MAX_CHAR * 4)))
    {
        APP_DEBUG("Enter ConSMSBuf_AddSeg,FAIL! Parameter is INVALID. pCSBuf:%x,uCSMaxCnt:%d,uIdx:%d,pCon:%x,pData:%x,uLen:%d\r\n", pCSBuf, uCSMaxCnt, uIdx, pCon, pData, uLen);
        return FALSE;
    }

    if ((pCon->msgTot) > CON_SMS_MAX_SEG)
    {
        APP_DEBUG("Enter ConSMSBuf_GetIndex,FAIL! msgTot:%d is larger than limit:%d\r\n", pCon->msgTot, CON_SMS_MAX_SEG);
        return FALSE;
    }

    uSeg = pCon->msgSeg;
    pCSBuf[uIdx].abSegValid[uSeg - 1] = TRUE;
    Ql_memcpy(pCSBuf[uIdx].asSeg[uSeg - 1].aData, pData, uLen);
    pCSBuf[uIdx].asSeg[uSeg - 1].uLen = uLen;

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
static bool ConSMSBuf_IsIntact(ConSMSStruct *pCSBuf, u8 uCSMaxCnt, u8 uIdx, ST_RIL_SMS_Con *pCon)
{
    u8 uSeg = 1;

    if ((NULL == pCSBuf) || (0 == uCSMaxCnt) || (uIdx >= uCSMaxCnt) || (NULL == pCon))
    {
        // APP_DEBUG("Enter ConSMSBuf_IsIntact,FAIL! Parameter is INVALID. pCSBuf:%x,uCSMaxCnt:%d,uIdx:%d,pCon:%x\r\n", pCSBuf, uCSMaxCnt, uIdx, pCon);
        return FALSE;
    }

    if ((pCon->msgTot) > CON_SMS_MAX_SEG)
    {
        // APP_DEBUG("Enter ConSMSBuf_GetIndex,FAIL! msgTot:%d is larger than limit:%d\r\n", pCon->msgTot, CON_SMS_MAX_SEG);
        return FALSE;
    }

    for (uSeg = 1; uSeg <= (pCon->msgTot); uSeg++)
    {
        if (FALSE == pCSBuf[uIdx].abSegValid[uSeg - 1])
        {
            // APP_DEBUG("Enter ConSMSBuf_IsIntact,FAIL! uSeg:%d has not received!\r\n", uSeg);
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
static bool ConSMSBuf_ResetCtx(ConSMSStruct *pCSBuf, u8 uCSMaxCnt, u8 uIdx)
{
    if ((NULL == pCSBuf) || (0 == uCSMaxCnt) || (uIdx >= uCSMaxCnt))
    {
        APP_DEBUG("Enter ConSMSBuf_ResetCtx,FAIL! Parameter is INVALID. pCSBuf:%x,uCSMaxCnt:%d,uIdx:%d\r\n", pCSBuf, uCSMaxCnt, uIdx);
        return FALSE;
    }

    // Default reset
    Ql_memset(&pCSBuf[uIdx], 0x00, sizeof(ConSMSStruct));

    // TODO: Add special reset here

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
    u8 nCurrStorage = 0;
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
    // APP_DEBUG("Delete all existed messages\r\n"); //Xóa ngày 9.3.2022

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

    Ql_memset(pTextInfo, 0x00, sizeof(ST_RIL_SMS_TextInfo));
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

        if (FALSE == pDeliverTextInfo->conPres) // Normal SMS
        {
            /*
            APP_DEBUG(
                "short message info: \r\n\tstatus:%u \r\n\ttype:%u \r\n\talpha:%u \r\n\tsca:%s \r\n\toa:%s \r\n\tscts:%s \r\n\tdata length:%u\r\ncp:0,cy:0,cr:0,ct:0,cs:0\r\n",
                (pTextInfo->status),
                (pTextInfo->type),
                (pDeliverTextInfo->alpha),
                (pTextInfo->sca),
                (pDeliverTextInfo->oa),
                (pDeliverTextInfo->scts),
                (pDeliverTextInfo->length));
                */
        }
        else
        {
            /*
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
                pDeliverTextInfo->con.msgSeg);
                */
        }

        // APP_DEBUG("\r\n\tmessage content:");
        // Tin nhắn dài sai số điện thoại chỉ định thì vào đây
        Ql_strcpy(Number, pDeliverTextInfo->oa);
        if (Ql_strcmp(Number, "+84764316794"))
        {
            APP_DEBUG("Saisodienthoai"); // Xóa ngày 9.3.2022
        }
        else
        {
            APP_DEBUG("%s\r\n", (pDeliverTextInfo->data));
            // Test tin nhan dai
            // APP_DEBUG("Long sms");

            // Test show number comming
            // APP_DEBUG(Number);
        }

        APP_DEBUG("\r\n");
    }
    else if (LIB_SMS_PDU_TYPE_SUBMIT == (pTextInfo->type))
    { // short messages in sent-list of drafts-list
    }
    else
    {
        APP_DEBUG("<-- Unkown short message type! type:%d -->\r\n", (pTextInfo->type));
    }
    Ql_MEM_Free(pTextInfo);
}

void SMS_TextMode_Send(void)
{
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

        // APP_DEBUG("<-- Send Text SMS[index=%d] successfully -->\r\n", nIndex);
        // APP_DEBUG("status:%u,data length:%u\r\n", (pPDUInfo->status), (pPDUInfo->length));
        APP_DEBUG("data = %s\r\n", (pPDUInfo->data));
    } while (0);

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
    char strPhNum[] = "0977413768\0";
    ST_RIL_SMS_TextInfo *pTextInfo = NULL;
    ST_RIL_SMS_DeliverParam *pDeliverTextInfo = NULL;
    char aPhNum[RIL_SMS_PHONE_NUMBER_MAX_LEN] = {
        0,
    };
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
        // APP_DEBUG("Fail to read text SMS[%d], cause:%d\r\n", nIndex, iResult);    // Xóa ngày 9.3.2022
        return;
    }

    if ((LIB_SMS_PDU_TYPE_DELIVER != (pTextInfo->type)) || (RIL_SMS_STATUS_TYPE_INVALID == (pTextInfo->status)))
    {
        Ql_MEM_Free(pTextInfo);
        APP_DEBUG("WARNING: NOT a new received SMS.\r\n");
        return;
    }

    pDeliverTextInfo = &((pTextInfo->param).deliverParam);

    if (TRUE == pDeliverTextInfo->conPres) // Receive CON-SMS segment
    {
        s8 iBufIdx = 0;
        u8 uSeg = 0;
        u16 uConLen = 0;

        iBufIdx = ConSMSBuf_GetIndex(g_asConSMSBuf, CON_SMS_BUF_MAX_CNT, &(pDeliverTextInfo->con));
        if (-1 == iBufIdx)
        {
            // APP_DEBUG("Enter Hdlr_RecvNewSMS,WARNING! ConSMSBuf_GetIndex FAIL! Show this CON-SMS-SEG directly!\r\n");
            /*
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
                            pDeliverTextInfo->con.msgSeg);
                            */
            // APP_DEBUG("data = %s\r\n", (pDeliverTextInfo->data));
            // APP_DEBUG("NUMBER PHONE1 : %s\r\n", (pDeliverTextInfo->oa));

            Ql_MEM_Free(pTextInfo);

            return;
        }

        bResult = ConSMSBuf_AddSeg(
            g_asConSMSBuf,
            CON_SMS_BUF_MAX_CNT,
            iBufIdx,
            &(pDeliverTextInfo->con),
            (pDeliverTextInfo->data),
            (pDeliverTextInfo->length));
        if (FALSE == bResult)
        {
            // APP_DEBUG("Enter Hdlr_RecvNewSMS,WARNING! ConSMSBuf_AddSeg FAIL! Show this CON-SMS-SEG directly!\r\n");
            /*
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
                pDeliverTextInfo->con.msgSeg);
                */
            // APP_DEBUG("data = %s\r\n", (pDeliverTextInfo->data));

            Ql_strcpy(Number, pDeliverTextInfo->oa);
            if (Ql_strcmp(Number, "+84764316794"))
            {
                APP_DEBUG("Saisodienthoai"); // Xóa ngày 9.3.2022
            }
            else
            {
                APP_DEBUG("%s\r\n", (pDeliverTextInfo->data));
                // Test tin nhan >160 ky tu
                // APP_DEBUG("TEST_DATA_OUT");

                // Test show number comming
                // APP_DEBUG(Number);
            }
            Ql_MEM_Free(pTextInfo);
            return;
        }

        bResult = ConSMSBuf_IsIntact(
            g_asConSMSBuf,
            CON_SMS_BUF_MAX_CNT,
            iBufIdx,
            &(pDeliverTextInfo->con));
        if (FALSE == bResult)
        {
            /*
            APP_DEBUG(
                "Enter Hdlr_RecvNewSMS,WARNING! ConSMSBuf_IsIntact FAIL! Waiting. cp:1,cy:%d,cr:%d,ct:%d,cs:%d\r\n",
                pDeliverTextInfo->con.msgType,
                pDeliverTextInfo->con.msgRef,
                pDeliverTextInfo->con.msgTot,
                pDeliverTextInfo->con.msgSeg);
        */
            Ql_MEM_Free(pTextInfo);

            return;
        }

        // Show the CON-SMS
        /*
        APP_DEBUG(
            "status:%u,type:%u,alpha:%u,sca:%s,oa:%s,scts:%s",
            (pTextInfo->status),
            (pTextInfo->type),
            (pDeliverTextInfo->alpha),
            (pTextInfo->sca),
            (pDeliverTextInfo->oa),
            (pDeliverTextInfo->scts));
            */

        uConLen = 0;
        for (uSeg = 1; uSeg <= pDeliverTextInfo->con.msgTot; uSeg++)
        {
            uConLen += g_asConSMSBuf[iBufIdx].asSeg[uSeg - 1].uLen;
        }

        // APP_DEBUG(",data length:%u", uConLen);
        APP_DEBUG("\r\n"); // Print CR LF

        // Tin nhắn dài hơn 160 ký tự xử lý ở đây

        // for (uSeg = 1; uSeg <= pDeliverTextInfo->con.msgTot; uSeg++)
        // {
        //     APP_DEBUG(g_asConSMSBuf[iBufIdx].asSeg[uSeg - 1].aData, g_asConSMSBuf[iBufIdx].asSeg[uSeg - 1].uLen);
        //     //Test do dai tin nhan OK
        //     //APP_DEBUG("Test tin nhan dai");
        // }

        Ql_strcpy(Number, pDeliverTextInfo->oa);
        if (Ql_strcmp(Number, "+84764316794"))
        {
            APP_DEBUG("Saisodienthoai"); // Xóa ngày 9.3.2022
        }
        else
        {
            for (uSeg = 1; uSeg <= pDeliverTextInfo->con.msgTot; uSeg++)
            {
                APP_DEBUG(g_asConSMSBuf[iBufIdx].asSeg[uSeg - 1].aData, g_asConSMSBuf[iBufIdx].asSeg[uSeg - 1].uLen);
                // Test do dai tin nhan OK
                // APP_DEBUG("Test tin nhan dai");
            }
        }

        APP_DEBUG("\r\n");
        bResult = ConSMSBuf_ResetCtx(g_asConSMSBuf, CON_SMS_BUF_MAX_CNT, iBufIdx);
        if (FALSE == bResult)
        {
            // APP_DEBUG("Enter Hdlr_RecvNewSMS,WARNING! ConSMSBuf_ResetCtx FAIL! iBufIdx:%d\r\n", iBufIdx);
        }

        Ql_MEM_Free(pTextInfo);

        return;
    }

    // APP_DEBUG("<-- RIL_SMS_ReadSMS_Text OK. eCharSet:LIB_SMS_CHARSET_GSM,nIndex:%u -->\r\n",nIndex);
    /*APP_DEBUG("status:%u,type:%u,alpha:%u,sca:%s,oa:%s,scts:%s,data length:%u\r\n",
        pTextInfo->status,
        pTextInfo->type,
        pDeliverTextInfo->alpha,
        pTextInfo->sca,
        pDeliverTextInfo->oa,
        pDeliverTextInfo->scts,
        pDeliverTextInfo->length);*/
    // APP_DEBUG("data = %s\r\n",(pDeliverTextInfo->data));
    // Điều chỉnh bỏ ký tự
    // Bỏ ký tự data ở đây
    // So sánh số điện thoại đúng với tin nhắn <160 ký tự.
    // if (strPhNum == (pDeliverTextInfo->oa))
    Ql_strcpy(Number, pDeliverTextInfo->oa);
    if (Ql_strcmp(Number, "+84764316794"))
    {
        APP_DEBUG("Saisodienthoaigoi"); // Xóa ngày 9.3.2022
    }
    else
    {
        APP_DEBUG("%s\r\n", (pDeliverTextInfo->data));
        // Test tin nhan <160 ky tu ok.
        // APP_DEBUG("TEST_DATA_OUT");
        // Test show number comming
        // APP_DEBUG(Number);
    }

    // APP_DEBUG("NUMBER PHONE3 : %s",aPhNum);
    Ql_MEM_Free(pTextInfo);

    // xu ly tin nhăn tại đây////////

    u32 nMsgRef;
    ST_RIL_SMS_SendExt sExt;
    Ql_memset(&sExt, 0x00, sizeof(sExt));
}

static s32 ReadSerialPort(Enum_SerialPort port, /*[out]*/ u8 *pBuffer, /*[in]*/ u32 bufLen)
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
        if (rdLen <= 0) // All data is read out, or Serial Port Error!
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
    if (str_URC != NULL)
    {
        APP_DEBUG("%s", str_URC);
    }
}

static void CallBack_UART_Hdlr(Enum_SerialPort port, Enum_UARTEventType msg, bool level, void *customizedPara)
{
    s32 iRet = 0;
    s32 yRet = 0;
    s32 tRet = 0;
    switch (msg)
    {
    case EVENT_UART_READY_TO_READ:
    {
        char *p = NULL;
        s32 totalBytes = ReadSerialPort(port, m_RxBuf_Uart, sizeof(m_RxBuf_Uart));
        if (totalBytes <= 0)
        {
            break;
        }
        p = Ql_strstr(m_RxBuf_Uart, "THANGGSM");
        if (p)
        {
            APP_DEBUG("OK");
            break;
        }
        p = Ql_strstr(m_RxBuf_Uart, "IMEI");
        if (p)
        {
            Ql_memset(GET_IMEI, 0x0, sizeof(GET_IMEI));
            iRet = RIL_GetIMEI(GET_IMEI);
            Ql_strncpy(IMEI, GET_IMEI + 2, 15);
            APP_DEBUG("<-- IMEI: %s,-->\r\n", IMEI);
            tRet = RIL_GetPowerSupply(&Cap, &Volt);
            APP_DEBUG("<-- Cap :%d, voltage:%d -->\r\n", Cap, Volt);
            break;
        }

        // APP_DEBUG("<--ERROR-->\r\n");       //Xóa ngày 9.3.2022
    }
    break;

    case EVENT_UART_READY_TO_WRITE:
    {
        //...
    }
    break;

    default:
        break;
    }
}

static void InitSerialPort(void)
{
    s32 iResult = 0;

    // Register & Open UART port
    iResult = Ql_UART_Register(UART_PORT1, CallBack_UART_Hdlr, NULL);
    if (iResult != QL_RET_OK)
    {
        Ql_Debug_Trace("Fail to register UART port[%d]:%d\r\n", UART_PORT1);
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

    // Register & open UART port
    InitSerialPort();

    // APP_DEBUG("OpenCPU: SMS Example\r\n");    //Xóa ngày 9.3.2022

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
            // APP_DEBUG("<-- RIL is ready -->\r\n");        //Xóa ngày 9.3.2022
            Ql_RIL_Initialize(); // MUST call this function
            RIL_GPS_Open(1);
            for (i = 0; i < CON_SMS_BUF_MAX_CNT; i++)
            {
                ConSMSBuf_ResetCtx(g_asConSMSBuf, CON_SMS_BUF_MAX_CNT, i);
            }

            break;
        }
        case MSG_ID_URC_INDICATION:
            switch (taskMsg.param1)
            {
            case URC_SYS_INIT_STATE_IND:
            {
                // APP_DEBUG("<-- Sys Init Status %d -->\r\n", taskMsg.param2);  //Xóa ngày 9.3.2022
                if (SYS_STATE_SMSOK == taskMsg.param2)
                {
                    // APP_DEBUG("\r\n<-- SMS module is ready -->\r\n"); //Xóa ngày 9.3.2022
                    // APP_DEBUG("\r\n<-- Initialize SMS-related options -->\r\n");  //Xóa ngày 9.3.2022
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
                // APP_DEBUG("\r\n<-- SIM Card Status:%d -->\r\n", taskMsg.param2);      //Xóa ngày 9.3.2022
            }
            break;

            case URC_GSM_NW_STATE_IND:
            {
                // APP_DEBUG("\r\n<-- GSM Network Status:%d -->\r\n", taskMsg.param2);   //Xóa ngày 9.3.2022
                break;
            }

            case URC_GPRS_NW_STATE_IND:
            {
                // APP_DEBUG("\r\n<-- GPRS Network Status:%d -->\r\n", taskMsg.param2);  //Xóa ngày 9.3.2022
                break;
            }

            case URC_CFUN_STATE_IND:
            {
                // APP_DEBUG("\r\n<-- CFUN Status:%d -->\r\n", taskMsg.param2);  //Xóa ngày 9.3.2022
                break;
            }

            case URC_COMING_CALL_IND:
            {
                ST_ComingCall *pComingCall = (ST_ComingCall *)(taskMsg.param2);
                // APP_DEBUG("\r\n<-- Coming call, number:%s, type:%d -->\r\n", pComingCall->phoneNumber, pComingCall->type);
                APP_DEBUG("\r\n<-- Coming call Server, number:%s>\r\n", pComingCall->phoneNumber, pComingCall->type);
                break;
            }

            case URC_NEW_SMS_IND:
            {
                // APP_DEBUG("\r\n<-- New SMS Arrives: index=%d\r\n", taskMsg.param2);
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

//#endif  __OCPU_RIL_SUPPORT__ && __OCPU_RIL_SMS_SUPPORT__
//#endif //__EXAMPLE_ALARM__
//#endif __CUSTOMER_CODE__