# 
#   $Id: Makefile,v 1.1 2006/06/15 09:29:10 casse Exp $
#   Copyright (C) 2003 Antoine Drouin
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

CC := powerpc-linux-gnu-gcc

CFLAGS := -Wall -g -O2 -I ../../include/c
AR := ar

GLIB_CFLAGS=`pkg-config --cflags glib-2.0`
GLIB_LIBS=`pkg-config --libs glib-2.0`

GOBJECT_CFLAGS=`pkg-config --cflags gobject-2.0`
GOBJECT_LIBS=`pkg-config --libs gobject-2.0`

GTK_CFLAGS=`pkg-config --cflags gtk+-2.0`
GTK_LIBS=`pkg-config --libs gtk+-2.0`

GNOME_CFLAGS=`pkg-config --cflags libgnomeui-2.0`
GNOME_LIBS=`pkg-config --libs libgnomeui-2.0`
 
LIBXML_CFLAGS=`pkg-config --cflags libxml-2.0`
LIBXML_LIBS=`pkg-config --libs  libxml-2.0`	



all: libpaparazzi.a

clean:
	rm -f libpaparazzi.a *~ core *.o .depend

# --------------------------------------------------------------------------
LIB_PAPARAZZI_SRC := \
	downlink.c \
	geometry.c \
	logger.c \
	network.c \
	protocol.c \
	traces.c \
	transport.c \

CFLAGS := $(CFLAGS) $(GLIB_CFLAGS) $(GTK_CFLAGS) $(LIBXML_CFLAGS)
# $(GNOME_CFLAGS)
#PLAY_LIBS := $(GLIB_LIBS) $(GTK_LIBS) $(LIBXML_LIBS) $(GNOME_LIBS) -lm 
LIB_PAPARAZZI_O := $(LIB_PAPARAZZI_SRC:.c=.o)
libpaparazzi.a: $(LIB_PAPARAZZI_O)
	$(AR) -r $@ $^ 

#
# Dependencies
#

.depend:
	$(CC) -M $(CFLAGS) $(LIB_PAPARAZZI_SRC) > .depend

ifneq ($(MAKECMDGOALS),clean)
-include .depend
endif


