/*------------------------------------------------------------------------------
 *
 *    Copyright (C) 1998 : Space Systems Finland Ltd.
 *
 * Space Systems Finland Ltd (SSF) allows you to use this version of
 * the DEBIE-I DPU software for the specific purpose and under the
 * specific conditions set forth in the Terms Of Use document enclosed
 * with or attached to this software. In particular, the software
 * remains the property of SSF and you must not distribute the software
 * to third parties without written and signed authorization from SSF.
 *
 *    System Name:   DEBIE DPU SW
 *    Module     :   target_isr_ctrl.h
 *
 * Macros and operations to control and handle interrupts.
 *
 * This version uses the harness functions for I/O and kernel simulation.
 *
 * Based on the SSF DHI file isr_ctrl.h, rev 1.16, Sun Jul 25 15:02:08 1999.
 *      
 *      
 *- * --------------------------------------------------------------------------
 */


#ifndef TARGET_ISR_CTRL_H
#define TARGET_ISR_CTRL_H


/* Simulation of hit trigger. */

extern void          Enable_Hit_Trigger  (void);
extern void          Disable_Hit_Trigger (void);
extern unsigned char Hit_Trigger_Flag    (void);

/* Macros for access to hit trigger. */

#define SET_HIT_TRIGGER_ISR_FLAG   {}
#define CLEAR_HIT_TRIGGER_ISR_FLAG {}
#define ENABLE_HIT_TRIGGER         Enable_Hit_Trigger ()
#define DISABLE_HIT_TRIGGER        Disable_Hit_Trigger ();
#define HIT_TRIGGER_FLAG  Hit_Trigger_Flag ()


#define SET_INTERRUPT_PRIORITIES {}
/* Sets Timer 1, Timer 2 and External interrupt 0 and 1 */
/* priorities high, others to low.                      */

#define DISABLE_INTERRUPT_MASTER {}
#define ENABLE_INTERRUPT_MASTER  {}
/* Clear and set interrupt master enable bit */

/* Simulation of Telecommand Timer */

extern unsigned char TC_Timer_Overflow_Flag       (void);
extern void          Clear_TC_Timer_Overflow_Flag (void);
extern void          Set_TC_Timer_Overflow_Flag   (void);

/* Macros for Telecommand Timer */

#define DISABLE_TC_TIMER_ISR {}
/* Macro for clearing TC timer interrupt enable flag */

#define TC_TIMER_OVERFLOW_FLAG TC_Timer_Overflow_Flag ()
/* TC timer overflow flag */

#define CLEAR_TC_TIMER_OVERFLOW_FLAG Clear_TC_Timer_Overflow_Flag ()
#define SET_TC_TIMER_OVERFLOW_FLAG   Set_TC_Timer_Overflow_Flag   ()
/* TC timer overflow flag manipulation macros. */

#endif
