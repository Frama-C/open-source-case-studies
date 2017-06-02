# 
#  $Id: Makefile,v 1.2 2007/11/16 14:12:00 casse Exp $
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

LOCAL_CFLAGS= $(CTL_BRD_FLAGS) -D__AVR_ATmega8__

ARCH	  = atmega8
TARGET	  = fbw
#LOW_FUSE  = 3f # crystal       #
#LOW_FUSE  = 31 # internal 1MHz #
#LOW_FUSE  = 1e  # ceramic resonator slow rising power p26 #
LOW_FUSE  = 2e  # ceramic resonator slow rising power p26 #
HIGH_FUSE = cb
EXT_FUSE  = ff
LOCK_FUSE = ff
VARINCLUDE = ../../var/include
INCLUDES = -I ../../include -I $(VARINCLUDE)

ifeq ($(CTL_BRD_VERSION),V1_2_1)
CTL_BRD_FLAGS=-DCTL_BRD_V1_2_1
endif

ifeq ($(CTL_BRD_VERSION),V1_2)
CTL_BRD_FLAGS=-DCTL_BRD_V1_2
endif

ifeq ($(CTL_BRD_VERSION),V1_1)
CTL_BRD_FLAGS=-DCTL_BRD_V1_1
endif


$(TARGET).srcs = \
	$(ARCH_CRT0) \
	main.c \
	ppm.c \
	servo.c \
	spi.c \
	uart.c \
	adc_fbw.c \
	$(ARCH_SOURCES)


include $(BASE)/conf/Makefile.std

fbw.install : warn_conf

warn_conf :
	@echo
	@echo '###########################################################'
	@grep AIRFRAME_NAME $(VARINCLUDE)/airframe.h
	@grep RADIO_NAME $(VARINCLUDE)/radio.h
	@echo '###########################################################'
	@echo


main.o .depend : $(VARINCLUDE)/radio.h $(VARINCLUDE)/airframe.h
ppm.s : $(VARINCLUDE)/radio.h

clean : avr_clean


