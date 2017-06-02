# 
#  $Id: Makefile,v 1.3 2008/10/22 19:41:18 casse Exp $
#  Copyright (C) 2003 Pascal Brisset, Antoine Drouin
#
# This file is part of paparazzi.
#
# paparazzi is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2, or (at your option)
# any later version.
#
# paparazzi is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with paparazzi; see the file COPYING.  If not, write to
# the Free Software Foundation, 59 Temple Place - Suite 330,
# Boston, MA 02111-1307, USA.  
# 


FBW=../fly_by_wire

LOCAL_CFLAGS= $(CTL_BRD_FLAGS) $(GPS_FLAGS) $(SIMUL_FLAGS) -D __AVR_ATmega128__

VARINCLUDE=../../var/include

ARCH	  = atmega128
TARGET 	  = autopilot

LOW_FUSE  = e0
HIGH_FUSE = 99
EXT_FUSE  = ff
LOCK_FUSE = ff


INCLUDES = -I $(FBW) -I ../../include -I $(VARINCLUDE)

GPS = gps_ubx.c
GPS_FLAGS=-DUBX

ifdef PAPABENCH_SINGLE
SINGLE_SOURCES = \
	../fly_by_wire/adc_fbw.c \
	../fly_by_wire/ppm.o \
	../fly_by_wire/spi.o \
	../fly_by_wire/main.o \
	../fly_by_wire/servo.o \
	../fly_by_wire/uart.o
endif

$(TARGET).srcs = \
	$(ARCH_CRT0) \
	main.c \
	modem.c \
	link_fbw.c \
	spi.c \
	adc.c \
	$(GPS) \
	infrared.c \
	pid.c \
	nav.c \
	uart.c \
	estimator.c	\
	if_calib.c \
	mainloop.c \
	../../lib/c/math.c \
	$(ARCH_SOURCES) \
	$(SINGLE_SOURCES)

include $(BASE)/conf/Makefile.std

autopilot.install : warn_conf

warn_conf :
	@echo
	@echo '###########################################################'
	@grep AIRFRAME_NAME $(VARINCLUDE)/airframe.h
	@grep RADIO_NAME $(VARINCLUDE)/radio.h
	@grep FLIGHT_PLAN_NAME $(VARINCLUDE)/flight_plan.h
	@echo '###########################################################'
	@echo


.depend : $(VARINCLUDE)/messages.h $(VARINCLUDE)/flight_plan.h  $(VARINCLUDE)/ubx_protocol.h  $(VARINCLUDE)/inflight_calib.h $(VARINCLUDE)/airframe.h  $(VARINCLUDE)/radio.h 
main.o : $(VARINCLUDE)/messages.h
nav.o : $(VARINCLUDE)/flight_plan.h
gps_ubx.o : $(VARINCLUDE)/ubx_protocol.h
if_calib.o : $(VARINCLUDE)/inflight_calib.h

clean : avr_clean
