/*
 * $Id: link_fbw.h,v 1.1 2006/06/15 09:25:57 casse Exp $
 *  
 * Copyright (C) 2003 Pascal Brisset, Antoine Drouin
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

#ifndef LINK_FBW_H
#define LINK_FBW_H

#include <inttypes.h>

#include "link_autopilot.h"

void link_fbw_init(void);
void link_fbw_send(void);
void link_fbw_on_spi_it(void);

extern volatile uint8_t link_fbw_nb_err;
extern uint8_t link_fbw_fbw_nb_err;

extern struct inter_mcu_msg from_fbw;
extern struct inter_mcu_msg to_fbw;
extern volatile uint8_t link_fbw_receive_complete;
extern volatile uint8_t link_fbw_receive_valid;

#endif /* LINK_FBW_H */
