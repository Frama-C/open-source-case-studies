/* revision.h -- define the version number
 * Copyright (C) 1992-1993 Jean-loup Gailly.
 * This is free software; you can redistribute it and/or modify it under the
 * terms of the GNU General Public License, see the file COPYING.
 */

#define VERSION "1.2.4"
#define PATCHLEVEL 0
#define REVDATE "18 Aug 93"

/* This version does not support compression into old compress format: */
#ifdef LZW
#  undef LZW
#endif

/* $Id: revision.h,v 0.25 1993/06/24 08:29:52 jloup Exp $ */
