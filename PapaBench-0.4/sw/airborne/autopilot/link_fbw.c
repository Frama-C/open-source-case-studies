/*
 * $Id: link_fbw.c,v 1.2 2007/07/25 14:21:30 nemer Exp $
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

#include <avr/io.h>
#include <avr/signal.h>
#include <avr/interrupt.h>

#include "link_fbw.h"
#include "spi.h"

struct inter_mcu_msg from_fbw;
struct inter_mcu_msg to_fbw;
volatile uint8_t link_fbw_receive_complete = TRUE;
volatile uint8_t link_fbw_receive_valid = FALSE;
volatile uint8_t link_fbw_nb_err;
uint8_t link_fbw_fbw_nb_err;

static uint8_t idx_buf;
static uint8_t xor_in, xor_out;

void link_fbw_init(void) {
  link_fbw_nb_err;
  link_fbw_receive_complete = FALSE;  
}

void link_fbw_send(void) {
  if (spi_cur_slave != SPI_NONE) {
    spi_nb_ovrn++;
    return;
  }

  /* Enable SPI, Master, set clock rate fck/16 */ 
  SPI_START(_BV(SPE) | _BV(MSTR) | _BV(SPR0)); // | _BV(SPR1);
  SPI_SELECT_SLAVE0();

  idx_buf = 0;
  xor_in = 0;
  xor_out = ((uint8_t*)&to_fbw)[idx_buf];
  SPDR = xor_out;
  link_fbw_receive_valid = FALSE;
  // Other bytes will follow SIG_SPI interrupts
}

void link_fbw_on_spi_it( void ) {
  /* setup OCR1A to pop in 200 clock cycles */
  /* this leaves time for the slave (fbw)   */
  /* to process the byte we've sent and to  */
  /* prepare a new one to be sent           */
  OCR1A = TCNT1 + 200;
  /* clear interrupt flag  */
  sbi(TIFR, OCF1A);
  /* enable OC1A interrupt */
  sbi(TIMSK, OCIE1A);
}


/* send the next byte */
SIGNAL(SIG_OUTPUT_COMPARE1A) {
  uint8_t tmp;

  /* disable OC1A interrupt */
  cbi(TIMSK, OCIE1A); 

  idx_buf++;

  /* we have sent/received a complete frame */
  if (idx_buf == FRAME_LENGTH) {
    /* read checksum from receive register  */
    tmp = SPDR;
    /* notify valid frame                   */
    if (tmp == xor_in) {
      link_fbw_receive_valid = TRUE;
      link_fbw_fbw_nb_err = from_fbw.nb_err;
    }
    else
      link_fbw_nb_err++;
    link_fbw_receive_complete = TRUE;
    /* unselect slave0                      */
    SPI_UNSELECT_SLAVE0();
    SPI_STOP();
    return;
  }

  /* we are sending/receiving payload       */
  if (idx_buf < FRAME_LENGTH - 1) {
    /* place new payload byte in send register */
    tmp = ((uint8_t*)&to_fbw)[idx_buf];
    SPI_SEND(tmp);
    xor_out ^= tmp;
  } 
  /* we are done sending the payload */
  else { // idx_buf == FRAME_LENGTH - 1
    /* place checksum in send register */
    SPI_SEND(xor_out);
  }
  
  /* read the byte from receive register */
  tmp = SPDR;
  ((uint8_t*)&from_fbw)[idx_buf-1] = tmp;
  xor_in ^= tmp;
}
