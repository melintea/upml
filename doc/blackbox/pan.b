	switch (t->back) {
	default: Uerror("bad return move");
	case  0: goto R999; /* nothing to undo */

		 /* PROC :init: */

	case 3: // STATE 1
		;
		;
		delproc(0, now._nr_pr-1);
		;
		goto R999;
;
		;
		
	case 5: // STATE 4
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC TestEnvironment */

	case 6: // STATE 1
		;
		sv_restor();
;
		;
		goto R999;

	case 7: // STATE 2
		;
		((P0 *)_this)->flippedWall = trpt->bup.oval;
		;
		goto R999;

	case 8: // STATE 3
		;
		sv_restor();
;
		;
		goto R999;

	case 9: // STATE 4
		;
		((P0 *)_this)->flippedWall = trpt->bup.oval;
		;
		goto R999;

	case 10: // STATE 5
		;
		sv_restor();
;
		;
		goto R999;

	case 11: // STATE 8
		;
		sv_restor();
;
		;
		goto R999;
;
		;
		;
		;
		
	case 14: // STATE 11
		;
		sv_restor();
;
		;
		goto R999;
;
		;
		
	case 16: // STATE 13
		;
		sv_restor();
;
		;
		goto R999;

	case 17: // STATE 16
		;
		sv_restor();
;
		;
		goto R999;
;
		;
		
	case 19: // STATE 18
		;
		((P0 *)_this)->flippedWall = trpt->bup.oval;
		;
		goto R999;

	case 20: // STATE 19
		;
		sv_restor();
;
		;
		goto R999;

	case 21: // STATE 20
		;
		((P0 *)_this)->flippedWall = trpt->bup.ovals[0];
		;
		ungrab_ints(trpt->bup.ovals, 2);
		goto R999;

	case 22: // STATE 21
		;
		sv_restor();
;
		;
		goto R999;

	case 23: // STATE 24
		;
		sv_restor();
;
		;
		goto R999;
;
		;
		
	case 25: // STATE 26
		;
		sv_restor();
;
		;
		goto R999;

	case 26: // STATE 27
		;
		p_restor(II);
		;
		;
		goto R999;
	}

