%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: Test Suite
%     Version: 12.06.12
%      Author: lasha.abzianidze{at}gmail.com 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- begin_tests(tt_reason).
test(1) :-
	reason(	[ (not,n:_~>n:_) @ ( (or,n:_~>n:_~>n:_) @ (man,n:_) @ (woman,n:_) ) ], 
			[ (and,n:_~>n:_~>n:_) @ ((not,n:_~>n:_) @ (man,n:_)) @ ((not,n:_~>n:_) @ (woman,n:_)) ]	 ).
test(2) :-
	reason(	[ (not,n:_~>n:_) @ ( (and,n:_~>n:_~>n:_) @ (man,n:_) @ (woman,n:_) ) ],
			[ (or,n:_~>n:_~>n:_) @ ((not,n:_~>n:_) @ (man,n:_)) @ ((not,n:_~>n:_) @ (woman,n:_)) ]	).
test(3) :-
	reason(	[ (and,n:_~>n:_~>n:_) @ ((not,n:_~>n:_) @ (man,n:_)) @ ((not,n:_~>n:_) @ (woman,n:_)) ],
			[ (not,n:_~>n:_) @ ((or,n:_~>n:_~>n:_) @ (man,n:_) @ (woman,n:_)) ] 	).
test(a4) :-
	reason(	[ (or,n:_~>n:_~>n:_) @ ((not,n:_~>n:_) @ (man,n:_)) @ ((not,n:_~>n:_) @ (woman,n:_)) ], 
		[ (not,n:_~>n:_) @ ((and,n:_~>n:_~>n:_) @ (man,n:_) @ (woman,n:_)) ]	).
test(b4) :-
	reason(	[ (or,n:_~>n:_~>n:_) @ ((not,n:_~>n:_) @ (man,n:_)) @ ((not,n:_~>n:_) @ (woman,n:_)) ], 
			[ (not,n:_~>n:_) @ ((and,n:_~>n:_~>n:_) @ (man,n:_) @ (woman,n:_)) ]	).
test(5) :-
	reason(	[ (lark,n:_) ],	
			[ (bird,n:_) ]	).
test(6, [fail]) :-
	reason(	[ (not,n:_~>n:_) @ ((and,n:_~>n:_~>n:_) @ (man,n:_) @ (woman,n:_)) ], 
			[ (and,n:_~>n:_~>n:_) @ ((not,n:_~>n:_) @ (man,n:_)) @ ((not,n:_~>n:_) @ (woman,n:_)) ]	).
test(7) :-
	reason(	[ (not,n:_~>n:_) @ (or @ (man,n:_) @ (woman,n:_)) ], 
			[ (or,n:_~>n:_~>n:_) @ ((not,n:_~>n:_) @ (man,n:_)) @ ((not,n:_~>n:_) @ (woman,n:_)) ]	).	
test(8, [fail]) :-
	reason(	[ (bird,n:_) ],
			[ (lark,n:_) ]	).	
/*test(a8) :-
	reason(	[ (man,n:_) ],
			[ not @ (woman,n:_) ]	).	*/
test(9, [fail]) :-
	reason(	[ (a,n:_~>(np:_~>s:_)~>s:dcl) @ (bird,n:_) @ (fly,np:_~>s:dcl) ],
			[ (a,n:_~>(np:_~>s:_)~>s:dcl) @ (lark,n:_) @ (fly,np:_~>s:dcl) ]	).
test(10) :-
	reason(	[ (a,n:_~>(np:_~>s:_)~>s:dcl) @ (lark,n:_) @ (fly,np:_~>s:dcl) ],
			[ (a,n:_~>(np:_~>s:_)~>s:dcl) @ (bird,n:_) @ (move,np:_~>s:dcl) ]	).	
test(12) :-
	reason(	[ every @ (who @ abst(X, touch @ X @ ('Mary',np:_)) @ person) @ run ], 
			[ most @ (who @ abst(X, kiss @ X @ ('Mary',np:_)) @ student) @ move ]	).	
test(13) :-
	reason(	[ no @ (bird,n:_) @ (move,np:_~>s:dcl) ], 
			[ no @ (lark,n:_) @ (fly,np:_~>s:dcl) ]	).
test(14) :-
	reason(	[ who @ abst(X, kiss @ X @ ('Mary',np:_)) @ student ], 
			[ who @ abst(X, touch @ X @ ('Mary',np:_)) @ person ]	).



test(16) :-
	reason(	[ and @ (sleep,np:_~>s:_) @ (not @ (sleep,np:_~>s:_)) @ ('John',np:_) ], 
			[ walk @ ('John',np:_) ]	).	
test(17) :-
	reason(	[ if @ (sleep @ ('John',np:_)) @ (snore @ ('John',np:_)) ],
			[ if @ (not @ snore @ ('John',np:_)) @ (not @ sleep @ ('John',np:_)) ]	).
test(18) :-
	reason(	[ if @ (sleep @ ('John',np:_)) @ (snore @ ('John',np:_)) ], 
			[ or @ (snore @ ('John',np:_)) @ (not @ sleep @ ('John',np:_)) ]	).
test(19) :-
	reason(	[ snore @ ('John',np:_) ], 
			[ sleep @ ('John',np:_) ]	).
test(20) :-
	reason(	[ most @ man @ walk ], 
			[ or @ (most @ man @ move) @ ((every,n:_~>(np:_~>s:_)~>s:dcl) @ (woman,n:_) @ move) ]	).
test(21) :-
	reason(	[ (a,n:_~>(np:_~>s:_)~>s:dcl) @ bachelor @ sleep ],
			[ or @ (a @ man @ sleep) @ (few @ human @ sleep) ]	). 
%%% does not close if you delete premises of monotone rules	
test(22) :-
	reason(	[ most @ (woman,n:_) ],
			[ (a,n:_~>(np:_~>s:_)~>s:dcl) @ (woman,n:_) ]	).	
test(23) :-
	reason(	[ (a,n:_~>(np:_~>s:_)~>s:dcl) @ bachelor @ sleep ],
			[ (a,n:_~>(np:_~>s:_)~>s:dcl) @ man @ sleep ]	).	
test(24, [fail]) :-
	reason(	[ (a,n:_~>(np:_~>s:_)~>s:dcl) @ dog @ run ],
			[ or @ (a @ hound @ (move,np:_~>s:dcl)) @ (most @ animal @ run) ]	).	
test(25) :-
	reason(	[ (a,n:_~>(np:_~>s:_)~>s:dcl) @ hound @ run ],
			[ or @ (a @ dog @ run) @ (most @ animal @ run) ]	).		
test(26, [fail]) :-
	reason(	[ (a,n:_~>(np:_~>s:_)~>s:dcl) @ dog @ run ],
			[ or @ (a @ man @ (move,np:_~>s:dcl)) @ (most @ animal @ sleep) ]	).
test(27) :-
	reason(	[ and @ (a @ dog @ run) @ (a @ bachelor @ sleep) ],
			[ (a,n:_~>(np:_~>s:_)~>s:dcl) @ man @ sleep ]	).
test(28) :-
	reason(	[ and @ (a @ bachelor @ sleep) @ (a @ dog @ run) ],
			[ (a,n:_~>(np:_~>s:_)~>s:dcl) @ man @ sleep ]	).
test(29) :-	
	reason(	[ sleep @ ('John',np:_) ],
			[ (a,n:_~>(np:_~>s:_)~>s:dcl) @ man @ sleep ]	).
test(30) :-	
	reason(	[ and @ (sleep @ ('John',np:_)) @ (sleep @ ('Mary',np:_)) ],
			[ and @ (a @ man @ sleep) @ (a @ (woman,n:_) @ sleep) ]	).
test(31) :-	
	reason(	[ sleep @ ('John',np:_) ],
			[ (a,n:_~>(np:_~>s:_)~>s:dcl) @ person @ sleep ]	).	
test(32) :-	
	reason(	[ no @ person @ sleep ],
			[ (not @ sleep) @ ('John',np:_) ]	).
test(33) :-	
	reason(	[ and @ ((every,n:_~>(np:_~>s:_)~>s:dcl) @ man @ walk) @ (no @ human @ (fly,np:_~>s:dcl)) ],
			[ and @ (walk @ ('John',np:_)) @ ((not @ (fly,np:_~>s:dcl)) @ ('Mary',np:_)) ]	).	
test(34) :-	
	reason(	[ (every,n:_~>(np:_~>s:_)~>s:dcl) @ man @ walk ],
			[ walk @ ('John',np:_) ]	).
test(35) :-	
	reason(	[ and  @ (no @ human @ (fly,np:_~>s:dcl)) @ ((every,n:_~>(np:_~>s:_)~>s:dcl) @ man @ walk) ],
			[ walk @ ('John',np:_) ]	).	
test(36, [fail]) :-	
	reason(	[ a @ man @ walk ],
			[ a @ (woman,n:_) @ (not @ abst(Y, a @ student @ abst(X, kiss @ X @ Y) ) ) ]	). 
test(37, [fail]) :-	
	reason(	[ a @ man @ walk ],
			[ a @ ( who @ (not @ abst(X, a @ student @ abst(Y, kiss@X@Y) )) @ woman ) @ walk ]	).	

:- end_tests(tt_reason).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% tests type subsumption
:- begin_tests(subsumption).
test(1) :-
	sub_type(np:_~>s:dcl, e~>s:dcl), !.
test(2, [fail]) :-
	sub_type(np:_~>s:dcl, e~>s:em), !.
test(3) :-
	sub_type(np:_~>s:dcl, e~>t), !.
test(4) :-
	sub_type(np:_~>s:_, np:_~>t), !.
test(5) :-
	sub_type(n:_~>np:_, (e~>t)~>np:_), !.
test(6) :-
	sub_type(n:_~>np:_, (e~>t)~>e), !.
test(7, [fail]) :-
	sub_type(n:_~>np:_, (e~>s:_)~>e), !.
test(8, [fail]) :-
	sub_type(n:_, np:_~>t), !.
test(9) :-
	sub_type(n:_, Type), sub_type(np:_~>s:dcl, Type), !.
:- end_tests(subsumption).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% tests monotonicity calculation
:- begin_tests(monotonicity).
test(1) :-
	ttExp_to_ttTerm( no @ (man,n:_), TT),
	tt_mon(TT, dw).
test(2) :-
	ttExp_to_ttTerm( (man,e~>t), TT),
	tt_mon(TT, non).
test(3) :-
	ttExp_to_ttTerm( (most,(e~>t)~>(e~>t)~>t), TT),
	tt_mon(TT, non).
test(4, [fail]) :-
	ttExp_to_ttTerm( every @ (man,n:_) @ run, TT),
	tt_mon(TT, _).
test(5) :-
	ttExp_to_ttTerm( most @ (man,n:_), TT),
	tt_mon(TT, up).
test(6, [fail]) :-
	ttExp_to_ttTerm( ('John',np:_), TT),
	tt_mon(TT, _).
test(7) :-
	ttExp_to_ttTerm( (run,np:_~>s:_), TT),
	tt_mon(TT, non).
test(8) :-
	ttExp_to_ttTerm( every @ (man,e~>t), TT),
	tt_mon(TT, up).
/*test(9) :-
	ttExp_to_ttTerm( (a,n:_~>(np:_~>s:_)~>s:_) , TT),
	tt_mon(TT, up).*/
:- end_tests(monotonicity).

/*
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% tests inferences 
:- begin_tests(reason).

test(1) :-
	reason(
		[ not @ (or @ (man,e~>t) @ (woman,e~>t)) ], 
		[ and @ (not @ (man,e~>t)) @ (not @ (woman,e~>t)) ]
	).
	
test(2) :-
	reason(
		[ not @ (and @ (man,e~>t) @ (woman,e~>t)) ],
		[ or @ (not @ (man,e~>t)) @ (not @ (woman,e~>t)) ]
	).
	
test(3) :-
	reason(
		[ and @ (not @ man) @ (not @ woman) ],
		[ not @ (or @ man @ woman) ] 
	).
	
test(a4) :-
	reason(
		[ or @ (not @ (man,e~>t)) @ (not @ (woman,e~>t)) ], 
		[ not @ (and @ (man,e~>t) @ (woman,e~>t)) ]
	).

test(b4) :-
	reason(
		[ or @ (not @ man) @ (not @ woman) ], 
		[ not @ (and @ man @ woman) ]
	).
	
test(5) :-
	reason(
		[ (lark,e~>t) ],	
		[ (bird,e~>t) ]
	).

test(6, [fail]) :-
	reason(
		[ not @ (and @ (man,e~>t) @ (woman,e~>t)) ], 
		[ and @ (not @ (man,e~>t)) @ (not @ (woman,e~>t)) ]
	).
	
test(7) :-
	reason(
		[ not @ (or @ (man,e~>t) @ (woman,e~>t)) ], 
		[ or @ (not @ (man,e~>t)) @ (not @ (woman,e~>t)) ]
	).	
	
test(8, [fail]) :-
	reason(
		[ (bird,e~>t) ],
		[ (lark,e~>t) ]
	).	

%test(a8) :-
%	reason(
%		[ (man,e~>t) ],
%		[ not @ (woman,e~>t) ]
%	).	

test(9, [fail]) :-
	reason(
		[ a @ bird @ (fly,e~>t) ],
		[ a @ lark @ (fly,e~>t) ]
	).
	
test(10) :-
	reason(
		[ a @ lark @ (fly,e~>t) ],
		[ a @ bird @ (move,e~>t) ]
	).	

test(a10) :-
	reason(
		[ a @ lark @ abst((X,e), a @ ((fly,e~>e~>t) @ (X,e)) @ (event,e~>t)) ],
		[ a @ bird @ abst((X,e), a @ ((move,e~>e~>t) @ (X,e)) @ (event,e~>t)) ]
	).

test(b10) :-
	reason(
		[ a @ lark @ abst((X,e), a @ ((fly,e~>e~>t) @ (X,e)) @ (event,e~>t)) ],
		[ a @ bird @ abst((X,e), a @ ((fly,e~>e~>t) @ (X,e)) @ (event,e~>t)) ]
	).

test(11) :-
	reason(
		[ every @ (and @ abst((X,e), (touch,e~>e~>t) @ (X,e) @ 'Mary') @ (person,e~>t)) @ (run,e~>t) ], 
		[ most @ (and @ abst((X,e), (kiss,e~>e~>t) @ (X,e) @ 'Mary') @ (student,e~>t) ) @ (move,e~>t) ]
	).
	

test(12) :-
	reason(
		[ every @ (who @ abst((X,e), (touch,e~>e~>t) @ (X,e) @ 'Mary') @ (person,e~>t)) @ (run,e~>t) ], 
		[ most @ (who @ abst((X,e), (kiss,e~>e~>t) @ (X,e) @ 'Mary') @ (student,e~>t) ) @ (move,e~>t) ]
	).	
	

test(13) :-
	reason(
		[ no @ bird @ (move,e~>t) ], 
		[ no @ lark @ (fly,e~>t) ]
	).

test(14) :-
	reason(
		[ and @ abst((X,e), (kiss,e~>e~>t) @ (X,e) @ 'Mary') @ (student,e~>t) ], 
		[ and @ abst((X,e), (touch,e~>e~>t) @ (X,e) @ 'Mary') @ (person,e~>t) ]
	).
	
test(15, [fail]) :-
	reason(
		[ if @ man @ woman ], 
		[ if @ (not @ woman) @ (not @ man) ]
	).	
	
test(16) :-
	reason(
		[ and @ (sleep,e~>t) @ (not @ (sleep,e~>t)) @ 'John' ], 
		[ (walk,e~>t) @ 'John' ]
	).	

test(17) :-
	reason(
		[ if @ ((sleep,e~>t) @ 'John') @ ((snore,e~>t) @ 'John') ],
		[ if @ (not @ (snore,e~>t) @ 'John') @ (not @ (sleep,e~>t) @ 'John') ]
	).

test(18) :-
	reason(
		[ if @ ((sleep,e~>t) @ 'John') @ ((snore,e~>t) @ 'John') ], 
		[ or @ ((snore,e~>t) @ 'John') @ (not @ (sleep,e~>t) @ 'John') ]
	).

test(19) :-
	reason(
		[ (snore,e~>t) @ 'John' ], 
		[ (sleep,e~>t) @ 'John' ]
	).

test(20) :-
	reason(
		[ most @ man @ (walk,e~>t) ], 
		[ or @ (most @ man @ (move,e~>t)) @ (every @ woman @ (move,e~>t)) ]
	).

test(21) :-
	reason(
		[ a @ bachelor @ (sleep,e~>t) ],
		[ or @ (a @ man @ (sleep,e~>t)) @ (few @ human @ (sleep,e~>t)) ]
	). %%% does not close if you delete premises of monotone rules	
	
test(22) :-
	reason(
		[ most @ woman ],
		[ a @ woman ]
	).	
	
test(23) :-
	reason(
		[ a @ bachelor @ (sleep,e~>t) ],
		[ a @ man @ (sleep,e~>t) ]
	).	
	
test(24, [fail]) :-
	reason(
		[ a @ dog @ (run,e~>t) ],
		[ or @ (a @ hound @ (move,e~>t)) @ (most @ animal @ (run,e~>t)) ]
	).	
	
test(25) :-
	reason(
		[ a @ hound @ (run,e~>t) ],
		[ or @ (a @ dog @ (run,e~>t)) @ (most @ animal @ (run,e~>t)) ]
	).		

test(26, [fail]) :-
	reason(
		[ a @ dog @ (run,e~>t) ],
		[ or @ (a @ man @ (move,e~>t)) @ (most @ animal @ (sleep,e~>t)) ]
	).
	
test(27) :-
	reason(
		[ and @ (a @ dog @ (run,e~>t)) @ (a @ bachelor @ (sleep,e~>t)) ],
		[ a @ man @ (sleep,e~>t) ]
	).
	
test(28) :-
	reason(
		[ and @ (a @ bachelor @ (sleep,e~>t)) @ (a @ dog @ (run,e~>t)) ],
		[ a @ man @ (sleep,e~>t) ]
	).

test(29) :-	
	reason(
		[ (sleep,e~>t) @ 'John' ],
		[ a @ man @ (sleep,e~>t) ]
	).
	
test(30) :-	
	reason(
		[ and @ ((sleep,e~>t) @ 'John') @ ((sleep,e~>t) @ 'Mary') ],
		[ and @ (a @ man @ (sleep,e~>t)) @ (a @ woman @ (sleep,e~>t)) ]
	).

test(31) :-	
	reason(
		[ (sleep,e~>t) @ 'John' ],
		[ a @ (person,e~>t) @ (sleep,e~>t) ]
	).	

test(32) :-	
	reason(
		[ no @ (person,e~>t) @ (sleep,e~>t) ],
		[ (not @ (sleep,e~>t)) @ 'John' ]
	).
	
test(33) :-	
	reason(
		[ and @ (every @ man @ (walk,e~>t)) @ (no @ human @ (fly,e~>t)) ],
		[ and @ ((walk,e~>t) @ 'John') @ ((not @ (fly,e~>t)) @ 'Mary') ]
	).	
		
test(34) :-	
	reason(
		[ every @ man @ (walk,e~>t) ],
		[ (walk,e~>t) @ 'John' ]
	).
	
test(35) :-	
	reason(
		[ and  @ (no @ human @ (fly,e~>t)) @ (every @ man @ (walk,e~>t)) ],
		[ (walk,e~>t) @ 'John' ]
	).	
%LOOPS
%test(36) :-	
%	reason(
%		[ a @ (man,e~>t) @ (walk,e~>t) ],
%		[ a @ (woman,e~>t) @ (not @ abst((Y,e), a @ (student,e~>t) @ abst((X,e), (kiss,e~>e~>t) @ (X,e) @ (Y,e)) ) ) ]
%	).	
	
:- end_tests(reason).
*/



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% tests Alpha-equivalence
:- begin_tests(alpha).

test(alpha1) :-
		alpha(X, X).
test(alpha2, [fail]) :-
		alpha(_, _).
test(alpha3, [fail]) :-
		alpha(_, const).
test(alpha4, [fail]) :-
		alpha(const1, const2).
test(alpha4) :-
		alpha(const1, const1).		
test(alpha5) :-
		alpha(abst(X, X), abst(X, X)).
test(alpha6) :-
		alpha(abst(X, X), abst(Y, Y)).
test(alpha7, [fail]) :-
		alpha(abst(X, abst(Y, X @ Y)), 
			  abst(X, abst(Y, Y @ X))).
test(alpha8) :-
		alpha(abst(X, abst(Y, X @ Y)), 
		      abst(Y, abst(X, Y @ X))).		
test(alpha9, [fail]) :-
		alpha(abst(_, const1), abst(_, const2)).
test(alpha10) :-
		alpha(abst(_, const), abst(_, const)).
test(alpha11, [fail]) :-
		alpha(abst(X, X) @ abst(_, _), 
		      abst(Y, Y) @ abst(_, _)).
test(alpha12, [fail]) :-
		alpha(abst(X, abst(X, X) @ Y), 
		      abst(Y, abst(Z, Z) @ Y)).
test(alpha13) :-
		alpha(abst(X, abst(X, X) @ Z), 
		      abst(_, abst(Z, Z) @ Z)).
test(alpha14, [fail]) :-
		alpha(abst(X, abst(X, X) @ X), 
		      abst(_, abst(Z, Z) @ Z)).
test(alpha15, [fail]) :-
		alpha(abst(X, abst(X, X) @ _), 
		      abst(_, abst(Z, Z) @ _)).				  
			  
:- end_tests(alpha).	




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% tests  betaNorm(LTerm, BetaNormForm)
:- begin_tests(betaNorm).

test(betaNorm1) :-
		betaNorm(abst(X, abst(Y, abst(P, and @ (X @ P) @ (Y @ P)))) @ abst(P, P @ 'John') @ abst(P, P @ 'Mary') @ abst(X, walk @ X ), and @ (walk @ 'John') @ (walk @ 'Mary')).

:- end_tests(betaNorm).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% tests  betaEtaNorm(LTerm, BetaEtaNormForm)
:- begin_tests(betaEtaNorm).

test(betaNorm1) :-
		betaEtaNorm(abst(X, abst(Y, abst(P, and @ (X @ P) @ (Y @ P)))) @ abst(P, P @ 'John') @ abst(P, P @ 'Mary') @ abst(X, walk @ X ), and @ (walk @ 'John') @ (walk @ 'Mary')).

:- end_tests(betaEtaNorm).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% tests  remove(E, OldList, NewList)
:- begin_tests(remove).

test(1) :-
	remove(a, [], []).
test(2) :-
	remove(a, [a,a,a,a], []).
test(3) :-
	remove(a, [a,b,c,a], [b,c]).
test(4) :-
	remove(a, [b,c,d], [b,c,d]).
test(5, [fail]) :-
	remove(a, [a,a], [a]).
test(6, [fail]) :-
	remove(a, [a,b,a], [b,a]).
test(7, [fail]) :-
	remove(a, [a,b,a], [a,b]).
test(8, [fail]) :-
	remove(a, [], [_|_]).
test(9, [fail]) :-
	remove(a, [b], []).

:- end_tests(remove).





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% tests  remove(E, OldList, NewList)
:- begin_tests(lambda_tt).
% Alpha equivalence
test(2) :-
	alpha_eq_tt( (john,e), (john,e)).
test(3) :-
	ttExp_to_ttTerm( abst((X,e), (see,e~>e~>t) @ (john,e) @ (X,e)), TTterm1),
	ttExp_to_ttTerm( abst((Y,e), (see,e~>e~>t) @ (john,e) @ (Y,e)), TTterm2), 
	alpha_eq_tt( TTterm1, TTterm2).
test(4) :-
	ttExp_to_ttTerm( abst((Y,e), abst((X,e), (see,e~>e~>t) @ (Y,e) @ (X,e))), TTterm1),
	ttExp_to_ttTerm( abst((X,e), abst((Y,e), (see,e~>e~>t) @ (X,e) @ (Y,e))), TTterm2),
	alpha_eq_tt( TTterm1, TTterm2).
test(5) :-
	ttExp_to_ttTerm( abst((A,e), abst((B,e), (see,e~>e~>t) @ (A,e) @ (B,e))), TTterm1),
	ttExp_to_ttTerm( abst((X,e), abst((Y,e), (see,e~>e~>t) @ (X,e) @ (Y,e))), TTterm2),
	alpha_eq_tt( TTterm1, TTterm2).
test(6) :-
	ttExp_to_ttTerm( abst((A,e), abst((A,e), (see,e~>e~>t) @ (A,e) )), TTterm1),
	ttExp_to_ttTerm( abst((_X,e), abst((Y,e), (see,e~>e~>t) @ (Y,e))), TTterm2),
	alpha_eq_tt( TTterm1, TTterm2).
test(7, [fail]) :-
	alpha_eq_tt( (john,e), (mary,e)).
test(8, [fail]) :-
	ttExp_to_ttTerm( abst((X,e), (see,e~>e~>t) @ (john,e) @ (X,e)), TTterm1),
	ttExp_to_ttTerm( abst((X,e), (see,e~>e~>t) @ (john,e) @ (_Y,e)), TTterm2), 
	alpha_eq_tt( TTterm1, TTterm2).
test(9, [fail]) :-
	ttExp_to_ttTerm( abst((Y,e), abst((X,e), (see,e~>e~>t) @ (Y,e) @ (X,e))), TTterm1),
	ttExp_to_ttTerm( abst((X,e), abst((Y,e), (see,e~>e~>t) @ (Y,e) @ (X,e))), TTterm2),
	alpha_eq_tt( TTterm1, TTterm2).
test(10, [fail]) :-
	ttExp_to_ttTerm( abst((A,e), abst((B,e), (see,e~>e~>t) @ (B,e) @ (A,e))), TTterm1),
	ttExp_to_ttTerm( abst((X,e), abst((Y,e), (see,e~>e~>t) @ (X,e) @ (Y,e))), TTterm2),
	alpha_eq_tt( TTterm1, TTterm2).
test(11) :-
	ttExp_to_ttTerm( abst((A,e), abst((A,e), (see,e~>e~>t) @ (A,e) )), TTterm1),
	ttExp_to_ttTerm( abst((Y,e), abst((_X,e), (see,e~>e~>t) @ (Y,e))), TTterm2),
	alpha_eq_tt( TTterm1, TTterm2).

% Alpha conversion 
test(c1) :-
	alpha_convert_tt( (abst((Y,e),(Y,e)),e~>e), X),
	X =@= (abst((Z,e),(Z,e)), e~>e) .
test(c2) :-
	alpha_convert_tt( (john,e), X),
	X =@= (john,e).
test(c3) :-
	ttExp_to_ttTerm( abst((X,e), (see,e~>e~>t) @ (john,e) @ (X,e)), TTterm1),
	ttExp_to_ttTerm( abst((Y,e), (see,e~>e~>t) @ (john,e) @ (Y,e)), TTterm2), 
	alpha_convert_tt( TTterm1, Z),
	Z =@= TTterm2.
test(c4) :-
	ttExp_to_ttTerm( abst((Y,e), abst((X,e), (see,e~>e~>t) @ (Y,e) @ (X,e))), TTterm1),
	ttExp_to_ttTerm( abst((X,e), abst((Y,e), (see,e~>e~>t) @ (X,e) @ (Y,e))), TTterm2),
	alpha_convert_tt( TTterm1, Z),
	Z =@= TTterm2.
test(c5) :-
	ttExp_to_ttTerm( abst((A,e), abst((B,e), (see,e~>e~>t) @ (A,e) @ (B,e))), TTterm1),
	ttExp_to_ttTerm( abst((X,e), abst((Y,e), (see,e~>e~>t) @ (X,e) @ (Y,e))), TTterm2),
	alpha_convert_tt( TTterm1, Z),
	Z =@= TTterm2.
test(c6) :-
	ttExp_to_ttTerm( abst((A,e), abst((A,e), (see,e~>e~>t) @ (A,e) )), TTterm1),
	ttExp_to_ttTerm( abst((_X,e), abst((Y,e), (see,e~>e~>t) @ (Y,e))), TTterm2),
	alpha_convert_tt( TTterm1, Z),
	Z =@= TTterm2.
test(c7a) :-
	ttExp_to_ttTerm( (and,(e~>t)~>(e~>t)~>e~>t) @ abst((A,e),(run,e~>t)@(A,e)) @ abst((A,e),(eat,e~>t)@(A,e)), TTterm1),
	ttExp_to_ttTerm( (and,(e~>t)~>(e~>t)~>e~>t) @ abst((X,e),(run,e~>t)@(X,e)) @ abst((Y,e),(eat,e~>t)@(Y,e)), TTterm2),
	alpha_convert_tt( TTterm1, Z),
	Z =@= TTterm2.
test(c7, [fail]) :-
	alpha_convert_tt( (abst((Y,e),(Y,e)), e~>e), X),
	X =@= (abst((_A,e),(_B,e)), e~>e) .
test(c8, [fail]) :-
	alpha_convert_tt( (john,e), X),
	X =@= (_Y,e).
test(c9, [fail]) :-
	ttExp_to_ttTerm( abst((X,e), (see,e~>e~>t) @ (john,e) @ (X,e)), TTterm1),
	ttExp_to_ttTerm( abst((_A,e), (see,e~>e~>t) @ (john,e) @ (_B,e)), TTterm2), 
	alpha_convert_tt( TTterm1, Z),
	Z =@= TTterm2.
test(c10, [fail]) :-
	ttExp_to_ttTerm( abst((Y,e), abst((X,e), (see,e~>e~>t) @ (Y,e) @ (X,e))), TTterm1),
	ttExp_to_ttTerm( abst((A,e), abst((B,e), (see,e~>e~>t) @ (B,e) @ (A,e))), TTterm2),
	alpha_convert_tt( TTterm1, Z),
	Z =@= TTterm2.
test(c11, [fail]) :-
	ttExp_to_ttTerm( abst((A,e), abst((B,e), (see,e~>e~>t) @ (A,e) @ (B,e))), TTterm1),
	ttExp_to_ttTerm( abst((X,e), abst((_Y,e), (see,e~>e~>t) @ (X,e) @ (X,e))), TTterm2),
	alpha_convert_tt( TTterm1, Z),
	Z =@= TTterm2.
test(c12, [fail]) :-
	ttExp_to_ttTerm( abst((A,e), abst((B,e), (see,e~>e~>t) @ (A,e) @ (B,e))), TTterm1),
	ttExp_to_ttTerm( abst((_X,e), abst((Y,e), (see,e~>e~>t) @ (Y,e) @ (Y,e))), TTterm2),
	alpha_convert_tt( TTterm1, Z),
	Z =@= TTterm2.
test(c13, [fail]) :-
	ttExp_to_ttTerm( abst((A,e), abst((A,e), (see,e~>e~>t) @ (A,e) )), TTterm1),
	ttExp_to_ttTerm( abst((Y,e), abst((_X,e), (see,e~>e~>t) @ (Y,e))), TTterm2),
	alpha_convert_tt( TTterm1, Z),
	Z =@= TTterm2.
test(c14, [fail]) :-
	ttExp_to_ttTerm( abst((A,e), abst((A,e), (see,e~>e~>t) @ (A,e) )), TTterm1),
	ttExp_to_ttTerm( abst((Y,e), abst((Y,e), (see,e~>e~>t) @ (_X,e))), TTterm2),
	alpha_convert_tt( TTterm1, Z),
	Z =@= TTterm2.
test(c15, [fail]) :-
	ttExp_to_ttTerm( abst((A,e), abst((A,e), (see,e~>e~>t) @ (A,e) )), TTterm1),
	ttExp_to_ttTerm( abst((Y,e), abst((Y,e), (see,e~>e~>t) @ (Y,e))), TTterm2),
	alpha_convert_tt( TTterm1, Z),
	Z =@= TTterm2.
test(c16, [fail]) :-
	ttExp_to_ttTerm( (and,(e~>t)~>(e~>t)~>e~>t) @ abst((A,e),(run,e~>t)@(A,e)) @ abst((A,e),(eat,e~>t)@(A,e)), TTterm1),
	ttExp_to_ttTerm( (and,(e~>t)~>(e~>t)~>e~>t) @ abst((X,e),(run,e~>t)@(X,e)) @ abst((X,e),(eat,e~>t)@(X,e)), TTterm2),
	alpha_convert_tt( TTterm1, Z),
	Z =@= TTterm2.

% beta
test(b1) :-
	beta_norm_tt((X,e), Z),
	Z == (X,e).
test(b2) :-
	beta_norm_tt((john,e), (john,e)).
test(b3) :-
	beta_norm_tt((abst((X,e),(X,e)),e~>e), (abst((A,e),(A,e)),e~>e)).
test(b4) :-
	beta_norm_tt((abst((X,e),(X,e)),e~>e), Z),
	Z == (abst((X,e),(X,e)),e~>e).
test(b5) :-
	ttExp_to_ttTerm( abst((Y,(e~>e)~>t), (Y,(e~>e)~>t) @ abst((X,e),(X,e))), TTterm),
	beta_norm_tt(TTterm, Z),
	Z == TTterm.
test(b6) :-
	ttExp_to_ttTerm( abst((X,e),(X,e)) @ (j,e), TTterm),
	beta_norm_tt(TTterm, Z),
	Z == (tlp(j,j,na,na,na), e). % tlp mod
test(b7) :-
	ttExp_to_ttTerm( abst((X,e), (and,t~>t~>t) @ ((run,e~>t)@(X,e)) @ ((eat,e~>t)@(X,e)) ) @ (j,e), TTterm),
	ttExp_to_ttTerm( (and,t~>t~>t) @ ((run,e~>t)@(j,e)) @ ((eat,e~>t)@(j,e)), Res),
	beta_norm_tt(TTterm, Z),
	Z == Res.	
test(b8) :-
	ttExp_to_ttTerm( abst((_Y,e), (and,t~>t~>t) @ ((run,e~>t)@(X,e)) @ ((eat,e~>t)@(X,e)) ) @ (j,e), TTterm),
	ttExp_to_ttTerm( (and,t~>t~>t) @ ((run,e~>t)@(X,e)) @ ((eat,e~>t)@(X,e)), Res),
	beta_norm_tt(TTterm, Z),
	Z == Res.
test(b10) :-
	ttExp_to_ttTerm( abst((_Y,e), (and,t~>t~>t) @ ((run,e~>t)@(m,e)) @ ((eat,e~>t)@(m,e)) ) @ (j,e), TTterm),
	ttExp_to_ttTerm( (and,t~>t~>t) @ ((run,e~>t)@(m,e)) @ ((eat,e~>t)@(m,e)), Res),
	beta_norm_tt(TTterm, Z),
	Z == Res.
test(b11) :-
	ttExp_to_ttTerm( abst((Y,e), abst((Y,e),(run,e~>t)@(Y,e))) @ (j,e), TTterm),
	ttExp_to_ttTerm( abst((Y,e),(run,e~>t)@(Y,e)), Res),
	beta_norm_tt(TTterm, Z),
	Z == Res.	
test(b12) :-
	ttExp_to_ttTerm( abst((Y,e~>t), (and,t~>t~>t)@((Y,e~>t)@(j,e))@((Y,e~>t)@(m,e))) @ abst((X,e),(love,e~>e~>t)@(X,e)@(b,e)), TTterm),
	ttExp_to_ttTerm( (and,t~>t~>t) @ ((love,e~>e~>t)@(j,e)@(b,e)) @ ((love,e~>e~>t)@(m,e)@(b,e)), Res),
	beta_norm_tt(TTterm, Z),
	Z == Res.

% free_tt
test(f1) :-
	free_tt((X,e),(X,e)).
test(f2, [fail]) :-
	free_tt((_X,e),(_Y,e)).
test(f3, [fail]) :-
	free_tt((_X,e),(j,e)).	
test(f4, [fail]) :-
	free_tt((X,e), (abst((X,e),(X,e)),e~>e)).
test(f5) :-
	free_tt((X,e), (abst((_Y,e),(X,e)),e~>e)).
test(f6, [fail]) :-
	free_tt((X,e), (abst((X,e),(_Y,e)),e~>e)).
test(f7, [fail]) :-
	free_tt((X,e), ((X,e~>t)@(_Y,e),e~>e)).
test(f8) :-
	free_tt((X,e~>t), ((X,e~>t)@(_Y,e),t)).
test(f9) :-
	free_tt((X,e), ((_Y,e~>t)@(X,e),e~>e)).
test(f10) :-
	free_tt((X,e), (abst((Y,e~>t), ((Y,e~>t)@(X,e),t)), (e~>t)~>t)).
test(f11, [fail]) :-
	free_tt((X,e), (abst((X,e~>t), ((X,e~>t)@(_Y,e),t)), (e~>t)~>t)).

% eta norm
test(e1) :-
	eta_norm_tt((X,e), Z),
	Z == (X,e).
test(e2) :-
	eta_norm_tt((j,e), Z),
	Z == (j,e).	
test(e3) :-
	eta_norm_tt( (abst((X,e),(X,e)),e~>e), Z ),
	Z == (abst((X,e),(X,e)),e~>e).
test(e4) :-
	eta_norm_tt( (abst((X,e), ((run,e~>t)@(X,e),t)), e~>t), Z ),
	Z == (run,e~>t).
test(e5) :-
	eta_norm_tt( ((abst((X,e),(run,e~>t)),e~>e~>t) @ (X,e), e~>t), Z ),
	Z == ((abst((X,e),(run,e~>t)),e~>e~>t) @ (X,e), e~>t). 
test(e6) :-
	eta_norm_tt( ((X,e~>t)@(Y,e),t), Z ),
	Z == ((X,e~>t)@(Y,e),t).

% nomalizing eta + beta
test(n1) :-
	ttExp_to_ttTerm( abst((Y,e), abst((X,e), (love,e~>e~>t)@(X,e)) @ (Y,e)), Term),
	ttExp_to_ttTerm( (love,e~>e~>t), NormTerm),
	norm_tt(Term, Norm),
	Norm == NormTerm.
test(n2) :-
	ttExp_to_ttTerm( abst((Y,e), abst((X,e), (love,e~>e~>t)@(Y,e)@(X,e))), Term),
	ttExp_to_ttTerm( (love,e~>e~>t), NormTerm),
	norm_tt(Term, Norm),
	Norm == NormTerm.

:- end_tests(lambda_tt).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- begin_tests(gqs).

%%%%%%%%%% VP and NP %%%%%%%%%% 
test(1) :- % Const_NP
	TTexp = run @ 'John',
	ttExp_to_ttTerm(TTexp, TT),
	gen_quant_tt(TTexp, [TT]).

test(2) :- % Quantified NP
	TTexp = run @ ((some,n~>np) @ girl),
	GQTTexp = some @ girl @ run,
	ttExp_to_ttTerm(GQTTexp, GQTT),
	gen_quant_tt(TTexp, [GQTT]).

%%%%%%%%%% Sentential conjunction %%%%%%%%%% 
test(3) :- % two Quantified NPs
	TTexp = and @ (run @ ((every,n~>np) @ boy)) @ (sleep @ ((some,n~>np) @ girl)),
	GQTTexp = and @ (every @ boy @ run) @ (some @ girl @ sleep),
	ttExp_to_ttTerm(GQTTexp, GQTT),
	gen_quant_tt(TTexp, [GQTT]).

test(4) :- % Quantified NP and Const_NP 
	TTexp = and @ (sleep @ 'John') @ (run @ ((every,n~>np) @ boy)),
	GQTTexp = and @ (sleep @ 'John') @ (every @ boy @ run),
	ttExp_to_ttTerm(GQTTexp, GQTT),
	gen_quant_tt(TTexp, [GQTT]).

test(5) :- % two Const_NPs
	TTexp = and @ (sleep @ 'John') @ (run @ 'Mary'),
	GQTTexp = and @ (sleep @ 'John') @ (run @ 'Mary'),
	ttExp_to_ttTerm(GQTTexp, GQTT),
	gen_quant_tt(TTexp, [GQTT]).

%%%%%%%%%% transitive VP %%%%%%%%%% 
test(6) :- % two Quantified NPs
	TTexp = like @ ((every,n~>np) @ girl) @ ((some,n~>np) @ boy),
	GQTTexp1 = (some @ boy) @ abst((Y,np:_), (every @ girl) @ abst((X,np:_), like @ (X,np:_) @ (Y,np:_))), 
	ttExp_to_ttTerm(GQTTexp1, GQTT1),
	GQTTexp2 = (every @ girl) @ abst((X,np:_), (some @ boy) @ (like @ (X,np:_))), 
	ttExp_to_ttTerm(GQTTexp2, GQTT2),
	gen_quant_tt(TTexp, [GQTT1, GQTT2]).

test(7) :- % Quant and Const NPs
	TTexp = like @ ((every,n~>np) @ girl) @ 'John',
	GQTTexp = (every @ girl) @ abst((X,np:_), (like @ (X,np:_) @ 'John')), 
	ttExp_to_ttTerm(GQTTexp, GQTT),
	gen_quant_tt(TTexp, [GQTT]).

test(8) :- % 2 Const NPs
	TTexp = like @ 'Mary' @ 'John',
	GQTTexp = like @ 'Mary' @ 'John',
	ttExp_to_ttTerm(GQTTexp, GQTT),
	gen_quant_tt(TTexp, [GQTT]).

%%%%%%%%%% Relative clause %%%%%%%%%% 
test(9) :- % relative clause: 2 Quant NPs
	TTexp = run @ ((every,n~>np) @ (who @ (like @ ((some,n~>np) @ girl)) @ boy)),
	GQTTexp1 = every @ (who @ abst((Y,np:_), some @ girl @ abst((X,np:_), like @ (X,np:_) @ (Y,np:_))) @ boy) @ run, 
	ttExp_to_ttTerm(GQTTexp1, GQTT1),
	GQTTexp2 = some @ girl @ abst((Y,np:_), every @ (who @ (like @ (Y,np:_)) @ boy) @ run), 
	ttExp_to_ttTerm(GQTTexp2, GQTT2),
	gen_quant_tt(TTexp, [GQTT1, GQTT2]).

test(10) :- % relative clause: Quant NP and Const NP
	TTexp = run @ ((every,n~>np) @ (who @ (like @ 'Mary') @ boy)),
	GQTTexp = every @ (who @ (like @ 'Mary') @ boy) @ run, 
	ttExp_to_ttTerm(GQTTexp, GQTT),
	gen_quant_tt(TTexp, [GQTT]).

test(11) :- % noun phrase with relative clause
	TTexp = (every,n~>np) @ (who @ (like @ ((a,n~>np) @ dog)) @ person), 
	GQTTexp1 = every @ (who @ abst((Y,np:_), a @ dog @ abst((X,np:_), like @ (X,np:_) @ (Y,np:_))) @ person),
	ttExp_to_ttTerm(GQTTexp1, GQTT1),
	GQTTexp2 = abst((V,np:_~>s:_), a @ dog @ abst((X,np:_), every @ (who @ (like @ (X,np:_)) @ person) @ (V,np:_~>s:_))),
	ttExp_to_ttTerm(GQTTexp2, GQTT2),
	gen_quant_tt(TTexp, [GQTT_1, GQTT_2]),
	GQTT_1 = GQTT1, GQTT_2 = GQTT2.

%%%%%%%%%% NP Conjunction %%%%%%%%%% 
test(12) :- % np conjunction
	TTexp = run @ (and @ ((every,n~>np) @ boy) @ ((some,n~>np) @ girl)),
	GQTTexp = (and @ (every @ boy) @ (some @ girl)) @ run,
	ttExp_to_ttTerm(GQTTexp, GQTT),
	gen_quant_tt(TTexp, [GQTT_1]),
	GQTT_1 = GQTT.
	

/*



NP conjunction
(run, np:_~>s:_) @ ((and,np:_~>np:_~>np:_) @ ((every,n:_~>np:_) @ (boy,n:_)) @ ((some,n:_~>np:_) @ (girl,n:_)))


propositional attitude verbs
(think,s:_~>np:_~>s:_) @ ((that,s:_~>s:_) @ ((run, np:_~>s:_) @ ((some,n:_~>np:_) @ (girl,n:_)))) @ ((every,n:_~>np:_) @ (boy,n:_)) 





[(run, np:_~>s:_) @ ('John', np:_),
(run, np:_~>s:_) @ ((some,n:_~>np:_) @ (girl,n:_)),
(run, np:_~>s:_) @ ((every,n:_~>np:_) @ ((who,(np:_~>s:_)~>n:_~>n:_) @ ((like,np:_~>np:_~>s:_) @ ((some,n:_~>np:_) @ (girl,n:_))) @ (boy,n:_))),
(and,s:_~>s:_~>s:_) @ ((run, np:_~>s:_) @ ((every,n:_~>np:_) @ (boy,n:_))) @ ((sleep, np:_~>s:_) @ ((some,n:_~>np:_) @ (girl,n:_))),
(run, np:_~>s:_) @ ((and,np:_~>np:_~>np:_) @ ((every,n:_~>np:_) @ (boy,n:_)) @ ((some,n:_~>np:_) @ (girl,n:_))),
(like,np:_~>np:_~>s:_) @ ((every,n:_~>np:_) @ (girl,n:_)) @ ((some,n:_~>np:_) @ (boy,n:_)),
(think,s:_~>np:_~>s:_) @ ((that,s:_~>s:_) @ ((run, np:_~>s:_) @ ((some,n:_~>np:_) @ (girl,n:_)))) @ ((every,n:_~>np:_) @ (boy,n:_)) ] 


(every,n:_~>np:_)@ (who @ ((quickly, (np:_~>s:_)~>np:_~>s:_) @ (touch @ ((a, n:_~>np:_) @ dog))) @ person)

*/


:- end_tests(gqs).











