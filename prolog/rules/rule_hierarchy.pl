%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module(rule_hierarchy,
	[
		sub_rule/2,
		set_rule_eff_order/0,
		rule_eff_order/1
	]).

:- use_module('../printer/reporting', [report/1]).
:- use_module('../rules/rules', [op(610, xfx, ===>), rule_priority/1]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Rule dependencies
% temporarily sub_rule is not transitive

sub_rule(A, B) :- % non reflexive
	prop_sub_rule(A, C),
	sub_rule_(C, [C], B).

sub_rule_(X, _, X).


sub_rule_(A, Path, B) :-
	prop_sub_rule(A, C),
	\+member(C, Path),
	sub_rule_(C, [C|Path], B).

% FIXME fill the _s in the rule schemmata

prop_sub_rule( 	h(up_mon_fun_some,	O, [T,F],	N, [[A,B,_]]),
				h(up_mon_fun, 	   	O, [T,F],	N, [[A,B]])
).
prop_sub_rule( 	h(dw_mon_fun_few,	O, [T,F], 	N, [[A,B,_]]),
				h(dw_mon_fun, 	   	O, [T,F], 	N, [[A,B]])
).

%---
prop_sub_rule( 	h(up_mon_fun_some, 	O, [T,_],	N, [[A,_,C]]),
			    h(tr_a, 		   	O, [T],		N, [[C,A]])
).

prop_sub_rule( 	h(up_mon_fun_some, 	[], [_,F],	N, [[_,B,C]]), %!!!exp
			    h(fl_a_c, 		   	N, [F,C],	[], [[B]]) % whatever variable needs there, hope dsoent block fl_a rules
).
prop_sub_rule( 	h(up_mon_fun_some, 	[], [_,F],	N, [[_,B,C]]), %!!!exp
			    h(fl_a_c, 		   	N, [F,B],	[], [[C]]) % whatever variable needs there, hope dsoent block fl_a rules
).

% verify below subsumption
prop_sub_rule( 	h(up_mon_fun_some, 	O, [_,F],	N, [[_,B,C]]),
			    h(fl_every,		   	O, [F],		N, [[C,B]])
).

prop_sub_rule( 	h(up_mon_fun_some, 	[],	[T,_],	N, [[A,_,C]]), %!!!exp
			    h(tr_every_c,	   	N,	[T,C],	[], [[A]]) % whatever variable needs there, hope dsoent block fl_a rules
).
%---
prop_sub_rule( 	h(dw_mon_fun_few, 	O,	[_,F],	N, [[_,B,C]]),
			    h(fl_no, 		   	O,	[F],	N, [[C,B]])
).

prop_sub_rule( 	h(dw_mon_fun_few, 	[],	[T,_],	N, [[A,_,C]]), %!!!exp
			    h(tr_no_c, 		   	N,	[T,A],	[], [[C]]) % whatever variable needs there, hope dsoent block fl_a rules
).
prop_sub_rule( 	h(dw_mon_fun_few, 	[],	[T,_],	N, [[A,_,C]]), %!!!exp
			    h(tr_no_c, 		   	N,	[T,C],	[], [[A]]) % whatever variable needs there, hope dsoent block fl_a rules
).

%prop_sub_rule(	h(up_mon_fun_some, 	[X,_],	[A,_,C]),
%			   	h(the_c, 			[X,_C],	[A])
%). % since up_mon_fun_some does not contain 'the'

% prop_sub_rule( [up_mon_fun_some, X, Y, AppInfo], [fl_a, Y, AppInf]).

/*prop_sub_rule( 	h(dw_mon_args,	[],	[X,Y],	[A,B]),
				h(dw_mon, 		[],	[X,Y],	[_,_,A,B])  %!!! before were x,
).*/

prop_sub_rule(  h(same_args_tf, O, [X,Y],	N, [[A,B]]),
				h(same_args_tf,	O, [Y,X],	N, [[B,A]])
).
prop_sub_rule(  h(same_args_xx, O, [X,Y],	N, [[A,B]]),
				h(same_args_xx,	O, [Y,X],	N, [[B,A]])
).
prop_sub_rule(  h(same_args_tf, O, [X,_],	N, [[A,_]]),
				h(push_arg,		O, [X],		N, [[A]])
).
prop_sub_rule(  h(same_args_tf, O, [_,Y],	N, [[_,B]]),
				h(push_arg,		O, [Y],		N, [[B]])
).
prop_sub_rule(  h(same_args_xx, O, [X,_],	N, [[A,_]]),
				h(push_arg,		O, [X],		N, [[A]])
).
prop_sub_rule(  h(same_args_xx, O, [_,Y],	N, [[_,B]]),
				h(push_arg,		O, [Y],		N, [[B]])
).
prop_sub_rule( 	h(same_args_tf,	[],	[X,Y],	[], [[A,B]]),
				h(dw_mon, 		[],	[X,Y],	_, [[_,_], [A,B]])  %!!! before were x,
).

/*prop_sub_rule(  h(up_mon_args, 	[],	[X,Y],	[A,B]),
				h(up_mon, 		[],	[X,Y],	[_,_,A,B])
).*/

prop_sub_rule(  h(same_args_tf, 	[],	[X,Y],	[], [[A,B]]),
				h(up_mon, 		[],	[X,Y],	_, [[_,_], [A,B]])
).

prop_sub_rule( 	h(dw_mon_fun, 	O, [X,Y],	N, [[A,B]]),
				h(dw_mon, 		O, [X,Y],	N, [[A,B], [_,_]])
).

prop_sub_rule( 	h(up_mon_fun, 	O, [X,Y], 	N, [[A,B]]),
				h(up_mon, 		O, [X,Y],	N, [[A,B], [_,_]])
).

prop_sub_rule( 	h(int_mod_tr, 	O, [X],		N, [[A,_]]),
				h(push_mod, 	O, [X],		N, [[A]])
).

prop_sub_rule( 	h(int_mod_tr, 	O, [X],		N, [[A,_]]),
				h(mod_n_tr, 	O, [X],		N, [[A]])
).
/*
prop_sub_rule( 	h(tr_conj_and, 	[X],	[_,B]),
				h(mod_tr, 		[X],	[B])
).

prop_sub_rule( 	h(tr_conj_who, 	[X], 	[_,B]),
				h(mod_tr, 		[X],	[B])
).

prop_sub_rule( 	h(tr_disj_or, 	[X], 	[_,B]),
				h(mod_tr, 		[X],	[B])
).

prop_sub_rule( 	h(tr_if, 		[X],	[_,B]),
				h(mod_tr, 		[X],	[B])
).
*/

%prop_sub_rule( 	h(fun_dist_np,		[],	[X],	[A]),
%				h(fun_dist, 		[],	[X],	[A])
%).

prop_sub_rule( 	h(pp_attach,	O, [X,_],	N, [[A]]), % deprecated tableau rule
				h(pp_attach, 	O, [X,A],	N, [[_]])
).

%prop_sub_rule( 	h(pp_attach,		[],	[_,_],	[A]), %added because of efficiency, sick-3626
%				h(mods_vp, 			[],	[A],	[_])		% actually vice versa
%).


prop_sub_rule( 	h(mod_vac, 		O, [X],		N, [[A]]),
				h(push_mod, 	O, [X],		N, [[A]])
).

prop_sub_rule( 	h(push_mod, 	O, [X],		N, [[A]]),
				h(mod_vac, 		O, [X],		N, [[A]])
).

prop_sub_rule( 	h(mod_n_tr, 	O, [X],		N, [[A]]),
				h(push_mod, 	O, [X],		N, [[A]])
).

prop_sub_rule( 	h(the_c, 		O, [X,A],	[], [[B]]),
				h(the, 			[],	[X],	O, [[B,A|_]])
).

prop_sub_rule( 	h(the, 			[],	[X], 	N, [[B,A|_]]), % may introduce more than 2 nodes
				h(the_c, 		N, [X,A],	[], [[B]])
).

prop_sub_rule( 	h(the_c, 		O, [X,A], 	N, [[B]]),
				h(fl_a, 		O,	[X],	N, [[_], [A,B]])
).

%prop_sub_rule( [the, X], 		[the_c, X, _]).  % removing this allows to assert VP on new constant of type N

%prop_sub_rule( h(the_c, 		[], [X,N], [V]),
%			   h(tr_a, 			[], [X,N], [V]).
%prop_sub_rule( [tr_a, X],       [the_c, X, _] ).

prop_sub_rule( 	h(tr_every_c, 	O, [X,_],	N, [[_]]),
				h(tr_every, 	O, [X],		N, [[_], [_,_]])   %why tr_every cannot apply to diff constant?
).

prop_sub_rule(	h(fl_a_c,	O, [X,_],	N, [[_]]),
				h(fl_a, 	O, [X], 	N, [[_], [_,_]])
).

prop_sub_rule(	h(tr_no_c,	O, [X,_],	N, [[_]]),
				h(tr_no, 	O, [X], 	N, [[_], [_,_]])
).

%fl_a -> the is not necessary since the-rule won't be applicapble, branch will close before that

prop_sub_rule(	h(equal1,	O, [E,A],	N, [[B]]),
				h(equal2, 	O, [E,B], 	N, [[A]])
).
prop_sub_rule(	h(equal2,	O, [E,A],	N, [[B]]),
				h(equal1, 	O, [E,B], 	N, [[A]])
).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% get an effciency order of rules

:- dynamic rule_eff_order/1.

set_rule_eff_order :-
	debMode(effCr(EffCr)),
	rule_priority(Rules),
	( atom(EffCr) ->
		EffRules = Rules
	; sort_rules_by_EffCr(Rules, EffCr, EffRules)
	),
	retractall(rule_eff_order(_)),
	assertz(rule_eff_order(EffRules)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% sort rules according to an effciency criterion
sort_rules_by_EffCr(Rules, EffCr, EffRules) :-
	reverse(Rules, RevRules),
	maplist(add_eff_vector(EffCr), RevRules, EffVecRs),
	keysort(EffVecRs, Sorted_EffVecRs),
	findall(R, member(_V-R, Sorted_EffVecRs), RevEffRules),
	reverse(RevEffRules, EffRules).


% add a efficiency vector based on an effciency criterion to a rule
add_eff_vector(EffCr, RuleID, EffVec-RuleID) :-
	maplist(calc_eff_feature(RuleID), EffCr, EffList),
	atomic_list_concat(EffList, EffVec).

% calculate a value of an effciency feature for a rule
calc_eff_feature(RuleID, EffFeat, Value) :-
	EffFeat = 'nonBr' ->
	  	( clause( r(RuleID, _, _, _, _, br(_H, _Sig) ===> br(_N, _S)),  _Cons ) -> Value = 1; Value = 0 )
	; EffFeat = 'nonProd' ->
	  	( clause( r(RuleID, _:'non', _, _, _, _),  _Cons ) -> Value = 1; Value = 0 )
	; EffFeat = 'equi' ->
	  	( clause( r(RuleID, 'equi':_, _, _, _, _),  _Cons ) -> Value = 1; Value = 0 )
	; EffFeat = 'nonCons' ->
	  	( clause( r(RuleID, RType:_, _, _, _, _),  _Cons ), RType \= 'gamma' -> Value = 1; Value = 0 )
	; report(['Error: unexpected effciency feature found!']).
