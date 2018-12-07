/*
 * Paparazzi mcu0 $Id: infrared.h,v 1.1 2006/06/15 09:25:57 casse Exp $
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

#ifndef INFRARED_H
#define INFRARED_H


extern int16_t ir_roll;  /* averaged roll adc */
extern int16_t ir_pitch; /* averaged pitch adc */


extern float   ir_rad_of_ir;
extern int16_t ir_contrast;
extern int16_t ir_roll_neutral;
extern int16_t ir_pitch_neutral;

void ir_init(void);
void ir_update(void);
void ir_gain_calib(void);

#endif /* INFRARED_H */
