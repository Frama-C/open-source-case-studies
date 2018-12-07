/*
 * $Id: autopilot.h,v 1.2 2007/07/25 14:21:30 nemer Exp $
 *  
 * Copyright (C) 2003  Pascal Brisset, Antoine Drouin
 *
 * This file is part of paparazzi.
 *
 * paparazzi is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2, or (at your option)
 * any later version.
 *
 * paparazzi is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with paparazzi; see the file COPYING.  If not, write to
 * the Free Software Foundation, 59 Temple Place - Suite 330,
 * Boston, MA 02111-1307, USA. 
 *
 */

#ifndef AUTOPILOT_H
#define AUTOPILOT_H

#include "link_autopilot.h"

#define TRESHOLD1 TRESHOLD_MANUAL_PPRZ
#define TRESHOLD2 200 * CLOCK


#define  PPRZ_MODE_MANUAL   0
#define  PPRZ_MODE_AUTO1    1
#define  PPRZ_MODE_AUTO2    2
#define  PPRZ_MODE_HOME     3
#define  PPRZ_MODE_NB       4

#define PPRZ_MODE_OF_PULSE(pprz, mega8_status) \
  (pprz > TRESHOLD2 ? PPRZ_MODE_AUTO2 : \
        (pprz > TRESHOLD1 ? PPRZ_MODE_AUTO1 : PPRZ_MODE_MANUAL))

extern uint8_t pprz_mode;


#define VERTICAL_MODE_MANUAL      0
#define VERTICAL_MODE_AUTO_GAZ    1
#define VERTICAL_MODE_AUTO_CLIMB  2
#define VERTICAL_MODE_AUTO_ALT    3
#define VERTICAL_MODE_NB          4

#define LATERAL_MODE_MANUAL    0
#define LATERAL_MODE_ROLL_RATE 1
#define LATERAL_MODE_ROLL      2
#define LATERAL_MODE_COURSE    3
#define LATERAL_MODE_NB        4

#define VERTICAL_MODE_OF_PULSE(pprz) (pprz < TRESHOLD2 ? VERTICAL_MODE_MANUAL:  \
                                                          VERTICAL_MODE_AUTO_ALT)

#define IR_ESTIM_MODE_OFF        0
#define IR_ESTIM_MODE_ON         1

#define IR_ESTIM_MODE_OF_PULSE(pprz) (pprz < TRESHOLD2 ? IR_ESTIM_MODE_OFF:  \
                                                          IR_ESTIM_MODE_ON)

extern uint8_t ir_estim_mode;

#define STICK_PUSHED(pprz) (pprz < TRESHOLD1 || pprz > TRESHOLD2)


#define TRIM_PPRZ(pprz) (pprz <  MIN_PPRZ ? MIN_PPRZ :  \
                         (pprz >  MAX_PPRZ ? MAX_PPRZ : \
                                   pprz))

#define TRIM_UPPRZ(pprz) (pprz <  0 ? 0 :  \
                          (pprz >  MAX_PPRZ ? MAX_PPRZ : \
                                    pprz))


#define FLOAT_OF_PPRZ(pprz, center, travel) ((float)pprz / (float)MAX_PPRZ * travel + center)

extern uint8_t fatal_error_nb;

#define GAZ_THRESHOLD_TAKEOFF (pprz_t)(MAX_PPRZ * 0.9)

extern uint8_t inflight_calib_mode;
//extern uint16_t flight_time;
extern uint8_t vertical_mode;
extern bool_t auto_pitch;
extern uint8_t lateral_mode;
extern uint8_t vsupply;

extern bool_t rc_event_1, rc_event_2;

extern float slider_1_val, slider_2_val;

extern bool_t launch;


#define ModeUpdate(_mode, _value) { \
  uint8_t new_mode = _value; \
  if (_mode != new_mode) { _mode = new_mode; return TRUE; } \
  return FALSE; \
}

#define CheckEvent(_event) (_event ? _event = FALSE, TRUE : FALSE)

#ifdef CTL_BRD_V1_1
extern struct adc_buf buf_bat;
#endif

void periodic_task( void );
void use_gps_pos(void);
void radio_control_task(void);
/*receive_gps_data_task */
void send_gps_pos( void );
void send_radIR(void);
void send_takeOff(void);
/*end receive_gps_data_task*/
void stabilisation_task(void);
#endif /* AUTOPILOT_H */
