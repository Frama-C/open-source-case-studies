/*
 * Paparazzi mcu0 $Id: gps.h,v 1.1 2006/06/15 09:25:56 casse Exp $
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

/*
 * Parse SIRF protocol from ublox SAM module
 *
*/


#ifndef GPS_H
#define GPS_H

#include "std.h"

extern uint8_t gps_mode;
extern float   gps_ftow;    /* ms */
extern float   gps_falt;    /* m       */
extern float   gps_fspeed;  /* m/s     */
extern float   gps_fclimb;  /* m/s     */
extern float   gps_fcourse; /* rad     */
extern int32_t gps_utm_east, gps_utm_north;
extern float gps_east, gps_north; /* m */

void gps_init( void );
void parse_gps_msg( void );
extern volatile uint8_t gps_msg_received;
extern bool_t gps_pos_available;
extern uint8_t gps_nb_ovrn;

#ifdef UBX
#include "ubx.h"
#else
#include "sirf.h"
#endif


#endif /* GPS_H */
