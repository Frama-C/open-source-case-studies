/*
 **********************************************************************
 * Copyright (C) Miroslav Lichvar  2017
 * 
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of version 2 of the GNU General Public License as
 * published by the Free Software Foundation.
 * 
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 * 
 **********************************************************************
 */

#include <config.h>
#include <sysincl.h>
#include <cmdparse.h>
#include <conf.h>
#include <keys.h>
#include <ntp_io.h>
#include <sched.h>
#include <local.h>
#include "test.h"

static struct timespec current_time;
static NTP_Receive_Buffer req_buffer, res_buffer;
static int req_length, res_length;

#define NIO_OpenServerSocket(addr) ((addr)->ip_addr.family != IPADDR_UNSPEC ? 100 : 0)
#define NIO_CloseServerSocket(fd) assert(fd == 100)
#define NIO_OpenClientSocket(addr) ((addr)->ip_addr.family != IPADDR_UNSPEC ? 101 : 0)
#define NIO_CloseClientSocket(fd) assert(fd == 101)
#define NIO_SendPacket(msg, to, from, len, process_tx) (memcpy(&req_buffer, msg, len), req_length = len, 1)
#define SCH_AddTimeoutByDelay(delay, handler, arg) (1 ? 102 : (handler(arg), 1))
#define SCH_AddTimeoutInClass(delay, separation, randomness, class, handler, arg) \
  add_timeout_in_class(delay, separation, randomness, class, handler, arg)
#define SCH_RemoveTimeout(id) assert(!id || id == 102)
#define LCL_ReadRawTime(ts) (*ts = current_time)
#define LCL_ReadCookedTime(ts, err) do {double *p = err; *ts = current_time; if (p) *p = 0.0;} while (0)
#define SRC_UpdateReachability(inst, reach)
#define SRC_ResetReachability(inst)

static SCH_TimeoutID
add_timeout_in_class(double min_delay, double separation, double randomness,
                     SCH_TimeoutClass class, SCH_TimeoutHandler handler, SCH_ArbitraryArgument arg)
{
  return 102;
}

#include <ntp_core.c>

static NCR_Instance inst;

static void
advance_time(double x)
{
  UTI_AddDoubleToTimespec(&current_time, x, &current_time);
}

static void
send_request(void)
{
  NTP_Local_Address local_addr;
  NTP_Local_Timestamp local_ts;
  uint32_t prev_tx_count;

  prev_tx_count = inst->report.total_tx_count;

  transmit_timeout(inst);
  TEST_CHECK(!inst->valid_rx);
  TEST_CHECK(!inst->updated_timestamps);
  TEST_CHECK(prev_tx_count + 1 == inst->report.total_tx_count);

  advance_time(1e-4);

  local_addr.ip_addr.family = IPADDR_UNSPEC;
  local_addr.if_index = INVALID_IF_INDEX;
  local_addr.sock_fd = 101;
  local_ts.ts = current_time;
  local_ts.err = 0.0;
  local_ts.source = NTP_TS_DAEMON;

  NCR_ProcessTxKnown(inst, &local_addr, &local_ts, &req_buffer.ntp_pkt, req_length);
}

static void
send_response(int interleaved, int authenticated, int allow_update, int valid_ts, int valid_auth)
{
  NTP_Packet *req, *res;

  req = &req_buffer.ntp_pkt;
  res = &res_buffer.ntp_pkt;

  TEST_CHECK(req_length >= NTP_NORMAL_PACKET_LENGTH);

  res->lvm = NTP_LVM(LEAP_Normal, NTP_LVM_TO_VERSION(req->lvm),
                     NTP_LVM_TO_MODE(req->lvm) == MODE_CLIENT ? MODE_SERVER : MODE_ACTIVE);
  res->stratum = 1;
  res->poll = req->poll;
  res->precision = -20;
  res->root_delay = UTI_DoubleToNtp32(0.1);
  res->root_dispersion = UTI_DoubleToNtp32(0.1);
  res->reference_id = 0;
  UTI_ZeroNtp64(&res->reference_ts);
  res->originate_ts = interleaved ? req->receive_ts : req->transmit_ts;

  advance_time(TST_GetRandomDouble(1e-4, 1e-2));
  UTI_TimespecToNtp64(&current_time, &res->receive_ts, NULL);
  advance_time(TST_GetRandomDouble(-1e-4, 1e-3));
  UTI_TimespecToNtp64(&current_time, &res->transmit_ts, NULL);
  advance_time(TST_GetRandomDouble(1e-4, 1e-2));

  if (!valid_ts) {
    // FRAMAC-C/EVA patch: using a temporary variable improves precision in the
    // switch (this will be possibly improved in a future release)
    long tmp = random() % (allow_update ? 4 : 5);
    switch (tmp) {
      case 0:
        res->originate_ts.hi = random();
        break;
      case 1:
        res->originate_ts.lo = random();
        break;
      case 2:
        UTI_ZeroNtp64(&res->originate_ts);
        break;
      case 3:
        UTI_ZeroNtp64(&res->receive_ts);
        break;
      case 4:
        UTI_ZeroNtp64(&res->transmit_ts);
        break;
      default:
        assert(0);
    }
  }

  if (authenticated) {
    res->auth_keyid = req->auth_keyid;
    KEY_GenerateAuth(ntohl(res->auth_keyid), (unsigned char *)res, NTP_NORMAL_PACKET_LENGTH,
                     res->auth_data, 16);
    res_length = NTP_NORMAL_PACKET_LENGTH + 4 + 16;
  } else {
    res_length = NTP_NORMAL_PACKET_LENGTH;
  }

  if (!valid_auth) {
    // FRAMAC-C/EVA patch: using a temporary variable improves precision in the
    // switch (this will be possibly improved in a future release)
    long tmp = random() % 3;
    switch (tmp) {
      case 0:
        res->auth_keyid++;
        break;
      case 1:
        res->auth_data[random() % 16]++;
        break;
      case 2:
        res_length = NTP_NORMAL_PACKET_LENGTH;
        break;
      default:
        assert(0);
    }
  }
}

static void
process_response(int valid, int updated)
{
  NTP_Local_Address local_addr;
  NTP_Local_Timestamp local_ts;
  NTP_Packet *res;
  uint32_t prev_rx_count, prev_valid_count;
  struct timespec prev_rx_ts;
  int prev_open_socket;

  res = &res_buffer.ntp_pkt;

  local_addr.ip_addr.family = IPADDR_UNSPEC;
  local_addr.if_index = INVALID_IF_INDEX;
  local_addr.sock_fd = NTP_LVM_TO_MODE(res->lvm) == MODE_ACTIVE ? 100 : 101;
  local_ts.ts = current_time;
  local_ts.err = 0.0;
  local_ts.source = NTP_TS_DAEMON;

  prev_rx_count = inst->report.total_rx_count;
  prev_valid_count = inst->report.total_valid_count;
  prev_rx_ts = inst->local_rx.ts;
  prev_open_socket = inst->local_addr.sock_fd != INVALID_SOCK_FD;

  NCR_ProcessRxKnown(inst, &local_addr, &local_ts, res, res_length);

  if (prev_open_socket)
    TEST_CHECK(prev_rx_count + 1 == inst->report.total_rx_count);
  else
    TEST_CHECK(prev_rx_count == inst->report.total_rx_count);

  if (valid)
    TEST_CHECK(prev_valid_count + 1 == inst->report.total_valid_count);
  else
    TEST_CHECK(prev_valid_count == inst->report.total_valid_count);

  if (updated)
    TEST_CHECK(UTI_CompareTimespecs(&inst->local_rx.ts, &prev_rx_ts));
  else
    TEST_CHECK(!UTI_CompareTimespecs(&inst->local_rx.ts, &prev_rx_ts));
}

void
test_unit(void)
{
  char source_line[] = "127.0.0.1";
  char conf[][100] = {
    "port 0",
    "keyfile ntp_core.keys"
  };
  int i, j, interleaved, authenticated, valid, updated, has_updated;
  CPS_NTP_Source source;
  NTP_Remote_Address remote_addr;

  CNF_Initialise(0, 0);
  for (i = 0; i < sizeof conf / sizeof conf[0]; i++)
    CNF_ParseLine(NULL, i + 1, conf[i]);

  LCL_Initialise();
  TST_RegisterDummyDrivers();
  SCH_Initialise();
  SRC_Initialise();
  NIO_Initialise(IPADDR_UNSPEC);
  NCR_Initialise();
  REF_Initialise();
  KEY_Initialise();

  for (i = 0; i < NB_TESTS; i++) {
    CPS_ParseNTPSourceAdd(source_line, &source);
    if (random() % 2)
      source.params.interleaved = 1;
    if (random() % 2)
      source.params.authkey = 1;

    UTI_ZeroTimespec(&current_time);
    advance_time(TST_GetRandomDouble(1.0, 1e9));

    TST_GetRandomAddress(&remote_addr.ip_addr, IPADDR_UNSPEC, -1);
    remote_addr.port = 123;

    inst = NCR_GetInstance(&remote_addr, random() % 2 ? NTP_SERVER : NTP_PEER, &source.params);
    NCR_StartInstance(inst);
    has_updated = 0;

    for (j = 0; j < 50; j++) {
      DEBUG_LOG("iteration %d, %d", i, j);

      interleaved = random() % 2 && (inst->mode != MODE_CLIENT ||
                                     inst->tx_count < MAX_CLIENT_INTERLEAVED_TX);
      authenticated = random() % 2;
      valid = (!interleaved || (source.params.interleaved && has_updated)) &&
              (!source.params.authkey || authenticated);
      updated = (valid || inst->mode == MODE_ACTIVE) &&
                (!source.params.authkey || authenticated);
      has_updated = has_updated || updated;

      send_request();

      send_response(interleaved, authenticated, 1, 0, 1);
      process_response(0, inst->mode == MODE_CLIENT ? 0 : updated);

      if (source.params.authkey) {
        send_response(interleaved, authenticated, 1, 1, 0);
        process_response(0, 0);
      }

      send_response(interleaved, authenticated, 1, 1, 1);
      process_response(valid, updated);
      process_response(0, 0);

      advance_time(-1.0);

      send_response(interleaved, authenticated, 1, 1, 1);
      process_response(0, 0);

      advance_time(1.0);

      send_response(interleaved, authenticated, 1, 1, 1);
      process_response(0, inst->mode == MODE_CLIENT ? 0 : updated);
    }

    NCR_DestroyInstance(inst);
  }

  KEY_Finalise();
  REF_Finalise();
  NCR_Finalise();
  NIO_Finalise();
  SRC_Finalise();
  SCH_Finalise();
  LCL_Finalise();
  CNF_Finalise();
  HSH_Finalise();
}
