/*
 * Paparazzi $Id: uart.c,v 1.1 2006/06/15 09:26:00 casse Exp $
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
#include <avr/signal.h>
#include <avr/interrupt.h>
#include <avr/io.h>
#include "uart.h"
#include "std.h"

#define TX_BUF_SIZE      256
static uint8_t           tx_head0; /* next free in buf */
static volatile uint8_t  tx_tail0; /* next char to send */
static uint8_t           tx_buf0[ TX_BUF_SIZE ];

static uint8_t           tx_head1; /* next free in buf */
static volatile uint8_t  tx_tail1; /* next char to send */
static uint8_t           tx_buf1[ TX_BUF_SIZE ];

void uart0_transmit( unsigned char data ) {
  if (UCSR0B & _BV(TXCIE)) {
    /* we are waiting for the last char to be sent : buffering */
    if (tx_tail0 == tx_head0 + 1) { /* BUF_SIZE = 256 */
      /* Buffer is full (almost, but tx_head = tx_tail means "empty" */
      return;
    }
    tx_buf0[tx_head0] = data;
    tx_head0++; /* BUF_SIZE = 256 */
  } else { /* Channel is free: just send */
    UDR0 = data;
    sbi(UCSR0B, TXCIE);
  }
}

void uart1_transmit( unsigned char data ) {
  if (UCSR1B & _BV(TXCIE)) {
    /* we are waiting for the last char to be sent : buffering */
    if (tx_tail1 == tx_head1 + 1) { /* BUF_SIZE = 256 */
      /* Buffer is full (almost, but tx_head = tx_tail means "empty" */
      return;
    }
    tx_buf1[tx_head1] = data;
    tx_head1++; /* BUF_SIZE = 256 */
  } else { /* Channel is free: just send */
    UDR1 = data;
    sbi(UCSR1B, TXCIE);
  }
}


void uart0_print_string(const uint8_t* s) {
  uint8_t i = 0;
  while (s[i]) {
    uart0_transmit(s[i]);
    i++;
  }
}

void uart0_print_hex(const uint8_t c) {
  const uint8_t hex[16] = { '0', '1', '2', '3', '4', '5', '6', '7', 
                            '8', '9', 'A', 'B', 'C', 'D', 'E', 'F' };
  uint8_t high = (c & 0xF0)>>4;
  uint8_t low  = c & 0x0F;
  uart0_transmit(hex[high]);
  uart0_transmit(hex[low]);
}


SIGNAL(SIG_UART0_TRANS) {
  if (tx_head0 == tx_tail0) {
    /* Nothing more to send */
    cbi(UCSR0B, TXCIE); /* disable interrupt */
  } else {
    UDR0 = tx_buf0[tx_tail0];
    tx_tail0++; /* warning tx_buf_len is 256 */
  }
}

SIGNAL(SIG_UART1_TRANS) {
  if (tx_head1 == tx_tail1) {
    /* Nothing more to send */
    cbi(UCSR1B, TXCIE); /* disable interrupt */
  } else {
    UDR1 = tx_buf1[tx_tail1];
    tx_tail1++; /* warning tx_buf_len is 256 */
  }
}

void uart0_init( void ) {
  /* Baudrate is 38.4k */
  UBRR0H = 0; 
  UBRR0L = 25; // 38.4
  // UBRR0L = 103; //9600
  /* single speed */ 
  UCSR0A = 0; 
  /* Enable receiver and transmitter */ 
  UCSR0B = _BV(RXEN) | _BV(TXEN);
  /* Set frame format: 8data, 1stop bit */ 
  UCSR0C = _BV(UCSZ1) | _BV(UCSZ0);
  /* Enable uart receive interrupt */
  sbi(UCSR0B, RXCIE ); 
}

void uart1_init( void ) {
  /* Baudrate is 38.4k */
  UBRR1H = 0; 
  UBRR1L = 25; // 38.4
  // UBRR1L = 103; //9600


  /* single speed */ 
  UCSR1A = 0; 
  /* Enable receiver and transmitter */ 
  UCSR1B = _BV(RXEN) | _BV(TXEN);
  /* Set frame format: 8data, 1stop bit */ 
  UCSR1C = _BV(UCSZ1) | _BV(UCSZ0);
  /* Enable uart receive interrupt */
  sbi(UCSR1B, RXCIE ); 
}

