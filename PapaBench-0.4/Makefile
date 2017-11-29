#   Paparazzi main $Id: Makefile,v 1.6 2008/10/22 19:41:17 casse Exp $
#   Copyright (C) 2004 Pascal Brisset Antoine Drouin
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

PACKAGE=PapaBench
VERSION=0.4
RELEASE=0
export BASE=$(PWD)
DIST= \
	COPYING \
	AUTHORS \
	README \
	Loops_Bounds.txt \
	PapaBench_for_wcet.txt \
	Makefile
DISTDIRS=aadl_sources avr conf sw


LIB=sw/lib
AIRBORNE=sw/airborne
CONFIGURATOR=sw/configurator
FBW=$(AIRBORNE)/fly_by_wire
AP=$(AIRBORNE)/autopilot
TMTC=sw/ground_segment/tmtc
WIND=sw/ground_segment/wind
VISU3D=sw/ground_segment/visu3d
LOGALIZER=sw/logalizer
SIMULATOR=sw/simulator
TOOLS=sw/tools
MAKE=make
ifdef PAPABENCH_SINGLE
PAPABENCH_FLAGS=PAPABENCH_SINGLE=yes
FBW_FLAGS=PAPABENCH_NOLINK=yes
endif

# Rules
all : fbw ap 

configure : configurator
	PAPARAZZI_DIR=`pwd` $(CONFIGURATOR)/configurator

lib:
	cd $(LIB)/c; $(MAKE)

fbw fly_by_wire : 
	cd $(FBW); $(MAKE) $(PAPABENCH_FLAGS) $(FBW_FLAGS) all

ap autopilot : 
	cd $(AP); $(MAKE) $(PAPABENCH_FLAGS) all

upload_fbw: fbw
	cd $(FBW); $(MAKE) upload

upload_ap: ap
	cd $(AP); $(MAKE) upload

erase_fbw:
	cd $(FBW); $(MAKE) erase

erase_ap:
	cd $(AP); $(MAKE) erase

airborne: fbw ap

doxygen:
	mkdir -p dox
	doxygen Doxyfile

clean:
	cd $(FBW); $(MAKE) clean
	cd $(AP); $(MAKE) clean


# Distribution building
DISTNAME=$(PACKAGE)-$(VERSION)
ifneq ($(RELEASE),0)
DISTNAME:=$(DISTNAME)-$(RELEASE)
endif

dist: clean
	-mkdir $(DISTNAME)
	cp -R $(DIST) $(DISTNAME)
	for d in $(DISTDIRS); do \
		for f in `find $$d ! -path "*/CVS*"`; do \
			if test -d $$f; then \
				mkdir $(DISTNAME)/$$f; \
			else \
				cp $$f $(DISTNAME)/$$f; \
			fi; \
		done; \
	done
	tar cvfz $(DISTNAME).tgz $(DISTNAME)
	rm -rf $(DISTNAME)

