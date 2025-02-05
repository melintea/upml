#define rand	pan_rand
#define pthread_equal(a,b)	((a)==(b))
#if defined(HAS_CODE) && defined(VERBOSE)
	#ifdef BFS_PAR
		bfs_printf("Pr: %d Tr: %d\n", II, t->forw);
	#else
		cpu_printf("Pr: %d Tr: %d\n", II, t->forw);
	#endif
#endif
	switch (t->forw) {
	default: Uerror("bad forward move");
	case 0:	/* if without executable clauses */
		continue;
	case 1: /* generic 'goto' or 'skip' */
		IfNotBlocked
		_m = 3; goto P999;
	case 2: /* generic 'else' */
		IfNotBlocked
		if (trpt->o_pm&1) continue;
		_m = 3; goto P999;

		 /* PROC :init: */
	case 3: // STATE 1 - switch.promela:48 - [(run TestEnvironment())] (0:0:0 - 1)
		IfNotBlocked
		reached[1][1] = 1;
		if (!(addproc(II, 1, 0)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 4: // STATE 3 - switch.promela:50 - [((_nr_pr==1))] (0:0:0 - 1)
		IfNotBlocked
		reached[1][3] = 1;
		if (!((((int)now._nr_pr)==1)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 5: // STATE 4 - switch.promela:51 - [-end-] (0:0:0 - 1)
		IfNotBlocked
		reached[1][4] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* PROC TestEnvironment */
	case 6: // STATE 1 - switch.promela:16 - [{c_code2}] (0:0:0 - 1)
		IfNotBlocked
		reached[0][1] = 1;
		/* c_code2 */
		{ 
		sv_save();initialize(); }

#if defined(C_States) && (HAS_TRACK==1)
		c_update((uchar *) &(now.c_state[0]));
#endif
;
		_m = 3; goto P999; /* 0 */
	case 7: // STATE 2 - switch.promela:19 - [flippedWall = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[0][2] = 1;
		(trpt+1)->bup.oval = ((int)((P0 *)_this)->flippedWall);
		((P0 *)_this)->flippedWall = 0;
#ifdef VAR_RANGES
		logval("TestEnvironment:flippedWall", ((int)((P0 *)_this)->flippedWall));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 8: // STATE 3 - switch.promela:19 - [{c_code3}] (0:0:0 - 1)
		IfNotBlocked
		reached[0][3] = 1;
		/* c_code3 */
		{ 
		sv_save();flip_lamp_switch(); }

#if defined(C_States) && (HAS_TRACK==1)
		c_update((uchar *) &(now.c_state[0]));
#endif
;
		_m = 3; goto P999; /* 0 */
	case 9: // STATE 4 - switch.promela:20 - [flippedWall = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[0][4] = 1;
		(trpt+1)->bup.oval = ((int)((P0 *)_this)->flippedWall);
		((P0 *)_this)->flippedWall = 1;
#ifdef VAR_RANGES
		logval("TestEnvironment:flippedWall", ((int)((P0 *)_this)->flippedWall));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 10: // STATE 5 - switch.promela:20 - [{c_code4}] (0:0:0 - 1)
		IfNotBlocked
		reached[0][5] = 1;
		/* c_code4 */
		{ 
		sv_save();flip_wall_switch(); }

#if defined(C_States) && (HAS_TRACK==1)
		c_update((uchar *) &(now.c_state[0]));
#endif
;
		_m = 3; goto P999; /* 0 */
	case 11: // STATE 8 - switch.promela:22 - [{c_code5}] (0:0:0 - 3)
		IfNotBlocked
		reached[0][8] = 1;
		/* c_code5 */
		{ 
		sv_save();now.isLigtOn = is_light_on(); }

#if defined(C_States) && (HAS_TRACK==1)
		c_update((uchar *) &(now.c_state[0]));
#endif
;
		_m = 3; goto P999; /* 0 */
	case 12: // STATE 9 - switch.promela:22 - [assert((isLigtOn==0))] (0:0:0 - 1)
		IfNotBlocked
		reached[0][9] = 1;
		spin_assert((((int)now.isLigtOn)==0), "(isLigtOn==0)", II, tt, t);
		_m = 3; goto P999; /* 0 */
	case 13: // STATE 10 - switch.promela:25 - [((flippedWall==0))] (0:0:1 - 1)
		IfNotBlocked
		reached[0][10] = 1;
		if (!((((int)((P0 *)_this)->flippedWall)==0)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 14: // STATE 11 - switch.promela:25 - [{c_code6}] (0:0:0 - 1)
		IfNotBlocked
		reached[0][11] = 1;
		/* c_code6 */
		{ 
		sv_save();flip_wall_switch(); }

#if defined(C_States) && (HAS_TRACK==1)
		c_update((uchar *) &(now.c_state[0]));
#endif
;
		_m = 3; goto P999; /* 0 */
	case 15: // STATE 12 - switch.promela:26 - [((flippedWall==1))] (0:0:1 - 1)
		IfNotBlocked
		reached[0][12] = 1;
		if (!((((int)((P0 *)_this)->flippedWall)==1)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 16: // STATE 13 - switch.promela:26 - [{c_code7}] (0:0:0 - 1)
		IfNotBlocked
		reached[0][13] = 1;
		/* c_code7 */
		{ 
		sv_save();flip_lamp_switch(); }

#if defined(C_States) && (HAS_TRACK==1)
		c_update((uchar *) &(now.c_state[0]));
#endif
;
		_m = 3; goto P999; /* 0 */
	case 17: // STATE 16 - switch.promela:28 - [{c_code8}] (0:0:0 - 3)
		IfNotBlocked
		reached[0][16] = 1;
		/* c_code8 */
		{ 
		sv_save();now.isLigtOn = is_light_on(); }

#if defined(C_States) && (HAS_TRACK==1)
		c_update((uchar *) &(now.c_state[0]));
#endif
;
		_m = 3; goto P999; /* 0 */
	case 18: // STATE 17 - switch.promela:28 - [assert((isLigtOn==1))] (0:0:0 - 1)
		IfNotBlocked
		reached[0][17] = 1;
		spin_assert((((int)now.isLigtOn)==1), "(isLigtOn==1)", II, tt, t);
		_m = 3; goto P999; /* 0 */
	case 19: // STATE 18 - switch.promela:31 - [flippedWall = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[0][18] = 1;
		(trpt+1)->bup.oval = ((int)((P0 *)_this)->flippedWall);
		((P0 *)_this)->flippedWall = 0;
#ifdef VAR_RANGES
		logval("TestEnvironment:flippedWall", ((int)((P0 *)_this)->flippedWall));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 20: // STATE 19 - switch.promela:31 - [{c_code9}] (0:0:0 - 1)
		IfNotBlocked
		reached[0][19] = 1;
		/* c_code9 */
		{ 
		sv_save();flip_lamp_switch(); }

#if defined(C_States) && (HAS_TRACK==1)
		c_update((uchar *) &(now.c_state[0]));
#endif
;
		_m = 3; goto P999; /* 0 */
	case 21: // STATE 20 - switch.promela:32 - [flippedWall = 1] (0:0:2 - 1)
		IfNotBlocked
		reached[0][20] = 1;
		(trpt+1)->bup.ovals = grab_ints(2);
		(trpt+1)->bup.ovals[0] = ((int)((P0 *)_this)->flippedWall);
		((P0 *)_this)->flippedWall = 1;
#ifdef VAR_RANGES
		logval("TestEnvironment:flippedWall", ((int)((P0 *)_this)->flippedWall));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 22: // STATE 21 - switch.promela:32 - [{c_code10}] (0:0:0 - 1)
		IfNotBlocked
		reached[0][21] = 1;
		/* c_code10 */
		{ 
		sv_save();flip_wall_switch(); }

#if defined(C_States) && (HAS_TRACK==1)
		c_update((uchar *) &(now.c_state[0]));
#endif
;
		_m = 3; goto P999; /* 0 */
	case 23: // STATE 24 - switch.promela:34 - [{c_code11}] (0:0:0 - 3)
		IfNotBlocked
		reached[0][24] = 1;
		/* c_code11 */
		{ 
		sv_save();now.isLigtOn = is_light_on(); }

#if defined(C_States) && (HAS_TRACK==1)
		c_update((uchar *) &(now.c_state[0]));
#endif
;
		_m = 3; goto P999; /* 0 */
	case 24: // STATE 25 - switch.promela:34 - [assert((isLigtOn==0))] (0:0:0 - 1)
		IfNotBlocked
		reached[0][25] = 1;
		spin_assert((((int)now.isLigtOn)==0), "(isLigtOn==0)", II, tt, t);
		_m = 3; goto P999; /* 0 */
	case 25: // STATE 26 - switch.promela:42 - [{c_code12}] (0:0:0 - 1)
		IfNotBlocked
		reached[0][26] = 1;
		/* c_code12 */
		{ 
		sv_save();terminate(); }

#if defined(C_States) && (HAS_TRACK==1)
		c_update((uchar *) &(now.c_state[0]));
#endif
;
		_m = 3; goto P999; /* 0 */
	case 26: // STATE 27 - switch.promela:43 - [-end-] (0:0:0 - 1)
		IfNotBlocked
		reached[0][27] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */
	case  _T5:	/* np_ */
		if (!((!(trpt->o_pm&4) && !(trpt->tau&128))))
			continue;
		/* else fall through */
	case  _T2:	/* true */
		_m = 3; goto P999;
#undef rand
	}

