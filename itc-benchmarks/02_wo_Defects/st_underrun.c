/********Software Analysis - FY2013*************/
/*
* File Name: data_lost.c
* Defect Classification
* ---------------------
* Defect Type: Stack related defects
* Defect Sub-type: Stack underrun
* Description: Defect Free Code to identify false positives in stack underrun conditions
*/

/* (Note) The default stack reservation size used by the linker in windows XP (64bit) is 1 MB(=1048576 bytes)*/
/*	Index starts from zero*/

#include "HeaderFile.h"

/*
 * Types of defects: stack underrun
 * Complexity: When using char array
 */
void st_underrun_001 ()
{
	 char buf[10];
	 strcpy(buf, "my string");
	 int len = strlen(buf) -1;
	 while (buf[len] != 'Z')
	 {
		 len--; /*Tool should not detect this line as error*/ /* No Stack Under RUN error */
		 if ( len < 0 )
			 break;
	 }
}

/*
 * Types of defects: stack underrun
 * Complexity:-	When using structure - passed as function arguments - one function level  _
 */
typedef struct {
	char buf[10];
	char buf1[10];
	char buf2[10];
	char buf3[10];
	char buf4[10];
	char buf5[10];
	char buf6[10];
} st_underrun_002_s_001;

void st_underrun_002_func_001 (st_underrun_002_s_001 s)
{

	 int len = strlen(s.buf) - 1;
	 for (;s.buf[len] != 'Z';len--)  /*Tool should not detect this line as error*/ /* No Stack Under RUN error */
	 {
	    //Frama-C: test patched to avoid unintentional undefined behavior
	    if ( len <= 0 )
			 break;
	 }
}

void st_underrun_002 ()
{
	st_underrun_002_s_001 s;
	strcpy(s.buf,"STRING");
	st_underrun_002_func_001(s);
}

/*
 * Types of defects: stack underrun
 * Complexity: When using structure - passed as function arguments - pointer to structure - 2 function Level _ _
 */
typedef struct {
	char buf[10];
	char buf1[10];
	char buf2[10];
	char buf3[10];
	char buf4[10];
} st_underrun_003_s_001;

void st_underrun_003_func_001 (st_underrun_003_s_001 *s)
{
	char buf[10] = "STRING";
	strcpy(s->buf,buf);
}

void st_underrun_003_func_002 (st_underrun_003_s_001 *s)
{
	 int len = strlen(s->buf) - 1;
	 do
	 {
		 s->buf[len] = 'A';
		 len--;
		 if ( len < 0 )
			 break;
	 }while (s->buf[len] != 'Z'); /*Tool should not detect this line as error*/ /* No Stack Under RUN error */
}

void st_underrun_003 ()
{
	st_underrun_003_s_001 s;
	st_underrun_003_func_001(&s);
	st_underrun_003_func_002(&s);
}

/*
 * Types of defects: stack underrun
 * Complexity: When using structure - passed as function arguments - pointer to structure -, return structure -3 function Level _ _ _
 */
typedef struct {
	char buf[10];
	char buf1[10];
	char buf2[10];
} st_underrun_004_s_001;

void st_underrun_004_func_002 (st_underrun_004_s_001 *s)
{
	char buf[10] = "STRING";
	strcpy(s->buf,buf);
}

st_underrun_004_s_001 st_underrun_004_func_001 (st_underrun_004_s_001 *s)
{
	st_underrun_004_s_001 s1;
	st_underrun_004_func_002(s);
	int len = strlen(s->buf) - 1;
	 do
	 {
		 s->buf[len] = 'B';
		 s1.buf[len] = s->buf[len];
		 len--;
		 if ( len < 0 )
			 break;
	 }while (s->buf[len] != 'Z'); /*Tool should not detect this line as error*/ /* No Stack Under RUN error */
	 return s1;
}

void st_underrun_004 ()
{
	st_underrun_004_s_001 s,s2;
	s2 = st_underrun_004_func_001(&s);
        sink = s2.buf[0];
}

/*
 * Types of defects: stack underrun
 * Complexity: Stack under run when using	Recursive function	9 Level	__ __ __ __ __ __ __ __ __ __
 */
typedef struct {
	char buf[10];
} st_underrun_005_s_001;

void st_underrun_005_func_001 (st_underrun_005_s_001 s, int cnt)
{
	while (s.buf[cnt] != 'Z' )
	{
		cnt--;
		if(cnt>0)
		{
			st_underrun_005_func_001(s, cnt);
		}
	    else
	    {
	    	break;
			/*s.buf[cnt] = 'C';*/ /*Tool should not detect this line as error*/ /* No Stack Under RUN error */
		}
	}
}

void st_underrun_005 ()
{
	char buf[10];
	st_underrun_005_s_001 s;
	strcpy(s.buf,"STRING !");
#ifndef __FRAMAC__
	// Frama-C/Eva: function call commented due to recursive call
	st_underrun_005_func_001(s,8);
#endif
	buf[0] = s.buf[1];
        sink = buf[0];
}

/*
 * Types of defects: stack underrun
 * Complexity:-	Stack under run when using Function pointer	Level 1	__
 */
typedef struct {
	char buf[10];
	char buf1[10];
	char buf2[10];
	char buf3[10];
	char buf4[10];
	char buf5[10];
	char buf6[10];
} st_underrun_006_s_001;

void st_underrun_006_func_001 (st_underrun_006_s_001 s)
{
  // JDR: commenting out -- this most certainly does access invalid RAM
#if 0
	 int len = strlen(s.buf) - 1;
	 char c = 0;
	 for (;s.buf[len] != 'Z';len--) /*Tool should not detect this line as error*/ /* No Stack Under RUN error */
	 {
         c = s.buf[len];
		 if ( len < 0 )
			 break;
	 }
         sink = c;
#endif
}

void st_underrun_006 ()
{
	st_underrun_006_s_001 s;
        // JDR: this is an array overrun (copying 12 bytes into a 10-byte array)
        // but maybe it is OK since the struct is guaranteed to have buf1 right
        // after buf?
	strcpy(s.buf,"STRING !!!!");
	void (*func)(st_underrun_006_s_001);
	func = st_underrun_006_func_001;
	func(s);
}

/*
 * Types of defects: stack underrun
 * Complexity: Stack under run in a function called form else condition
 */
typedef struct {
	char buf[10];
	char buf1[10];
	char buf2[10];
	char buf3[10];
	char buf4[10];
	char buf5[10];
} st_underrun_007_s_001;

void st_underrun_007_func_001 (st_underrun_007_s_001 *s)
{
	 int len = strlen(s->buf) - 1;
	 char c = 0;
	 for (;s->buf[len] != 'Z';len--)  
	 {
        c = s->buf[len]; /*Tool should not detect this line as error*/ /* No Stack Under RUN error */
		 //Frama-C: test patched to avoid unintentional undefined behavior
		 if ( len <= 0 )
			 break;
	 }
         sink = c;
}

void st_underrun_007_func_002 (st_underrun_007_s_001 s)
{
	s.buf[0] += 1;
}

void st_underrun_007 ()
{
	int flag = 0;
	st_underrun_007_s_001 s = {0};
	s.buf[0] = 1;
	if (flag >1 )
	{
		st_underrun_007_func_002(s);
	}
	else
	{
		st_underrun_007_func_001(&s);
	}
}

/*
 * Types of defects: stack underrun
 * Complexity: stack underrun main function
 */

extern volatile int vflag;
void st_underrun_main ()
{
	if (vflag == 1 || vflag ==888)
	{
		st_underrun_001();
	}

	if (vflag == 2 || vflag ==888)
	{
		st_underrun_002();
	}

	if (vflag == 3 || vflag ==888)
	{
		st_underrun_003();
	}

	if (vflag == 4 || vflag ==888)
	{
		st_underrun_004();
	}

	if (vflag == 5 || vflag ==888)
	{
		st_underrun_005();
	}

	if (vflag == 6 || vflag ==888)
	{
		st_underrun_006();
	}

	if (vflag == 7 || vflag ==888)
	{
		st_underrun_007();
	}
}
