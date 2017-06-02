/*
 * Paparazzi autopilot $Id: ubx.h,v 1.1 2006/06/15 09:26:01 casse Exp $
 *  
 * Copyright (C) 2004  Pascal Brisset, Antoine Drouin
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
 * UBX protocol specific code
 *
*/


#ifndef UBX_H
#define UBX_H

#define GPS_FIX_VALID(gps_mode) (gps_mode == 3)
extern const int32_t utm_east0;
extern const int32_t utm_north0;

#endif /* UBX_H */
