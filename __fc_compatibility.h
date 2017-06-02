/**************************************************************************/
/*                                                                        */
/*  This file is part of Frama-C.                                         */
/*                                                                        */
/*  Copyright (C) 2007-2015                                               */
/*    CEA (Commissariat à l'énergie atomique et aux énergies              */
/*         alternatives)                                                  */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 2.1.                                              */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 2.1                 */
/*  for more details (enclosed in the file licenses/LGPLv2.1).            */
/*                                                                        */
/**************************************************************************/

/* Definitions for better compatibility with several specific features,
   e.g. GNU extensions, GCC-specific features, etc. */

#define _VA_LIST_DEFINED

#define __builtin_expect(exp, c) ((exp) == (c))
#define __builtin___vsprintf_chk(args...) __vsprintf_chk(args)
#define __builtin___vsnprintf_chk(args...) __vsnprintf_chk(args)
#define __builtin___snprintf_chk(args...) __snprintf_chk(args)
#define __builtin___memcpy_chk(args...) __memcpy_chk(args)
#define __builtin___memmove_chk(args...) __memmove_chk(args)
#define __builtin___mempcpy_chk(args...) __mempcpy_chk(args)
#define __builtin___memset_chk(args...) __memset_chk(args)
#define __builtin___strcpy_chk(args...) __strcpy_chk(args)
#define __builtin___stpcpy_chk(args...) __stpcpy_chk(args)
#define __builtin___strncpy_chk(args...) __strncpy_chk(args)
#define __builtin___strcat_chk(args...) __strcat_chk(args)
#define __builtin___strncat_chk(args...) __strncat_chk(args)

#define __GNUC_PREREQ(...) 1

// Currently, these _chk() functions perform no checks.
#define __strcat_chk(d,s,bos) strcat(d,s)
#define __strncat_chk(d,s,n,bos) strncat(d,s,n)
#define __strcpy_chk(d,s,bos) strcpy(d,s)
#define __strncpy_chk(d,s,n,bos) strncpy(d,s,n)
#define __memcpy_chk(d,s,n,bos) memcpy(d,s,n)
#define __memmove_chk(d,s,n,bos) memmove(d,s,n)
#define __memset_chk(s,c,n,bos) memset(s,c,n)

// Requires inclusion of __fc_builtin.h
#define __builtin_constant_p(exp) (Frama_C_interval(0,1))
