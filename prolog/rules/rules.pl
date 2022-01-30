%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: Tableau Rules
%     Version: 12.06.12
%      Author: lasha.abzianidze{at}gmail.com
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module(rules, [
		r/6,
		rule_priority/1,
		admissible_rules/1,
		op(610, xfx, ===>)
]).
%==================================

:- use_module('../lambda/lambda_tt', [
	norm_tt/2, op(605, xfy, ~>), op(605, yfx, @)
	]).
:- use_module('../printer/reporting', [report/1]).
:- use_module('../lambda/type_hierarchy', [
	cat_eq/2, final_value_of_type/2, sub_type/2, set_final_value_of_type/3
	]).
:- use_module('../utils/user_preds',
	[choose/3, const_ttTerm/1, no_isa_rel_const_ttTerms/3, tt_mon/2, tt_mon_up/1, neg/2]
	).
:- use_module('../llf/ttterm_to_term', [ttTerm_to_prettyTerm/2]).
:- use_module('../llf/ttterm_preds', [
	adjuncted_ttTerm/1, modList_node_to_modNode_list/2,
	tt_constant_to_tt_entity/2, modList_be_args_to_nodeList/3,
	match_ttTerms/3, match_list_ttTerms/3, proper_tt_isa/3, extract_const_ttTerm/2,
	set_type_for_tt/3, is_tlp/1, tlp_pos_in_list/2, tlp_lemma_in_list/2,
	tlp_pos_with_prefixes/2, cc_as_fun/1, wh_mod_np_to_nodes/3
	]).
:- use_module('../prover/tableau_utils', [
	genOldArgs/3, genFreshArgs/5
	]).
:- use_module('../knowledge/ling', [pos2s_feat/2]).

:- ensure_loaded([
	'closure_rules',
	'../knowledge/knowledge',
	'../knowledge/lexicon'
]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- multifile r/6.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

rule_priority([
	%cl_subcat, cl_ant,
	pull_arg, beta_red, type_drop,
	tr_conj_and, fl_conj_and, tr_conj_who, fl_conj_who, fl_disj_or, tr_disj_or, neg_not, fl_if, tr_if,
	there_trans, det_dist,
	empty_mod, ho_verb,
	poss_tr, cardinal_mod, not_quant,
	be_pp, be_a_s, be_a_obj, a_subj_be,
	vp_pass2, %vp_pass1,
	vp_pp,
	v_pr_v_pp, pr_v_v_pp, pr_v_v_pr, v__pr_v_pr,
	the_c, %the,
	fact_v_s_tr, fact_v_tr, fact_v_fl, it_is_tr_fl,
	tr_every_c, fl_a_c, tr_no_c,
	equal1, equal2,
	by_mod, %pp_mod_vp_fl, %pp_mod_vp_tr,
	mod_vac, int_mod_tr, int_mod_fl, mod_n_tr, push_mod,
	pp_mod_n_tr, pp_mod_n_fl, % put higher than just modifiers
	pp_com_n_tr, pp_com_n_fl,
	mods_noun, mods_vp, % ignore for mode(no_mod_set)
	%mods_be, %vpMod_to_argMod,
	%pp_attach, seems inefficenet for contradiction checking, so used as closure rule
	a_group_of, group_of,
	same_args_tf, same_args_xx, %up_mon_args, dw_mon_args,
	up_mon_fun_some, dw_mon_fun_few,
	up_mon_fun, dw_mon_fun, % doesn't matter order
	push_arg,
	arg_dist, abst_dist, fun_dist, % fun dist not good?
	%up_mon_args, dw_mon_args, up_mon_fun_some, up_mon_fun, dw_mon_fun,
	up_mon, dw_mon,
	tr_a, fl_a, tr_every, fl_every, tr_no, fl_no,
	the
]).


admissible_rules(
[up_mon_fun_some, dw_mon_fun_few, up_mon_fun, dw_mon_fun, tr_every_c, fl_a_c, tr_no_c, up_mon_args, dw_mon_args]
).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%		Linguistic Rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% remove "do", "will" modifying verb phrase
r(empty_mod,  equi:non,  ([], [], _), [['do'], ['will'], ['be'], ['become'], ['to'], ['that'], ['have'], ['there']], _,
		br([nd( M, ( (tlp(_,Aux,_,_,_), Type1~>Type2) @ TT1, _ ),
				Args, TF )],
		  Sig)
		===>
		br([nd( M, TT1, Args, TF)],
		  Sig) )
:-
		cat_eq(Type1, Type2),
		final_value_of_type(Type1, s:_),
		member(Aux, ['do', 'will', 'be', 'become', 'to', 'that', 'have', 'there']), !.
% 'there' is for NL:er:s~>s
% maybe "become" in false context is not correct
% it is true THAT ...



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% possessive determiner in true context
% sick-5003, %!!! what about 1781?
r(poss_tr, impl:new, ([], Args, Cids), [['\'s']], _,
		br([nd( M, (((( TLP_poss, np:_~>n:_~>(np:_~>s:_)~>s:_) @ TTnp, _) @ TTn, _) @ TTvp, _),
				[], true )],
		  Sig)
		===>
		br([nd( [], TTn, Args, true ),
			nd( M, TTvp, Args, true ),
			nd( [], (TLP_poss, np:_~>pp), [(NP,e)| Args], true )], % only semnatic terms
			%TODO use more general 'of' relation
		  Sig1) )
:-
		TLP_poss = tlp(_,'\'s','POS',_,_),
		TTvp = (_, Type1),
		TTn = (_, Type2),
		TTnp = (NP,_), %FIXME NP is tlp?
		sub_type(Type1, Type),
		sub_type(Type2, Type),
		genFreshArgs(Type, Args, Sig, Sig1, Cids), !.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% remove quantifier modifier not: not all A B :X -> all A B: -X
r(not_quant,  equi:non,  ([], [], _), [['not']], _,
		br([nd( M, ( (((tlp(_,'not',_,_,_), Type~>Type) @ Quant, Type) @ TTn, Ty1) @ TTv, Ty2 ),
				Args, TF1 )],
		  Sig)
		===>
		br([nd( M, ((Quant @ TTn, Ty1) @ TTv, Ty2), Args, TF2)],
		  Sig) )
:-
		neg(TF1, TF2).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% noun modifier in true context

% intersective noun modifier in true context
r(int_mod_tr, impl:non, ([], [], _), _Lexicon, _KB-XP, % equi
		br([nd( M,  ((TLP, n:_~>n:_) @ TTn, n:_),
				[(C,e)], true )],
		  Sig)
		===>
		br([nd( M,  TTn, [(C,e)], true ),
			nd( [], (TLP, Type), [(C,e)], true )],
		  Sig) )
:-
		TLP = tlp(_,Lem,POS,_,_),
		( debMode('allInt')  %3344:roof top->roof; 5552:toy phone->toy; 7957:court floor->court
		  %\+atom_prefix(POS, 'NN')   % train-4020 baby kangaroo
		; intersective(Lem) % what happens if all are intersective?
		%; (POS = 'JJ', \+privative(Lem)) % relaxing constraints
		; atom_prefix(POS, 'VB') % verbs are as intersective adjectives
		; TTn = ((tlp(_,Priv,_,_,_), n:_~>n:_) @ _, _), % successful former N -> successful fr-199
		  privative(Priv)
		),
		!, % detect a type
		( atom_prefix(POS, 'VB') ->
			Type = np:_~>s:_
		; atom_prefix(POS, 'NN') -> %6096 !!!bird@cage
			Type = n:_
		; atom_prefix(POS, 'JJ') ->
			Type = np:_~>s:_
		; Type = e~>t
		),
		ul_append(XP, [int(Lem)]).

% intersective noun modifier in false context
%branching could be in different way too
r(int_mod_fl, impl:non, ([], [], _), _Lexicon, _KB-XP,
	br([nd( M, ((TLP, n:_~>n:_) @ TTn, n:_),
			[(C,e)], false )],
	  Sig)
	===>
	[ 	br([nd( M, TTn, [(C,e)], false )],
		  Sig),
		% TODO: in gentail show terms with semantic types differently
		br([nd( [], (TLP, Ty), [(C,e)], false ), % Ty was e~>t
		    nd( M,  TTn, [(C,e)], true ) ],
		  Sig)
	] )
:-
	TLP = tlp(_,Lem,POS,_,_),
	( pos2s_feat(POS, SFeat) -> Ty = np:_~>s:SFeat
	; atom_prefix(POS, 'NN') -> Ty = n:_
	; Ty = e~>t ),
	% conditions that allow branching in F
	( intersective(Lem)
	; atom_prefix(POS, 'JJ'), debMode('allInt') % relaxing constraints sick-2791, 5671
	; atom_prefix(POS, 'VB') % verbs are as intersective adjectives sick-2722
	; TTn = ((tlp(_,Priv,_,_,_), n:_~>n:_) @ _, _), % successful former N -> successful fr-199
	  privative(Priv)
	), !,
	ul_append(XP, [int(Lem)]).


% non-intersective noun modifier in true context
r(mod_n_tr, impl:non, ([], [], _), _Lexicon, _KB-XP,
		br([nd( M, ((TTexp,n:F1~>n:F2) @ TT, n:_),    Args,    true )],    Sig)
		===>
		br([nd( M1, TT,    Args,    TF)],    Sig)
)  %!!! increase M list
:-
		%TTexp \= tlp(_,'not',_,_,_), not necessary
		\+(( TTexp = (tlp(_,Con,_,_,_),_) @ _,  member(Con, [if, and, or, who]) )), % can TTexp be compund? why not only tlp?
		( TTexp = tlp(_,Lemma,_,_,_),
		  privative(Lemma) ->
			TF = false,
			M1 = M % or M1 = []
		  ; ( adjuncted_ttTerm(TT) ->
			  	append(M, [(TTexp,n:F1~>n:F2)], M1)
		   	  ;	M1 = []
			),
			TF = true
		),
		ttTerm_to_prettyTerm(((TTexp,_)@TT,_), PrMN),
		ttTerm_to_prettyTerm(TT, PrN),
		ul_append(XP, [isa(PrMN, PrN)]).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% removes any modifier, except negeation
r(push_mod,  impl:non,  ([], [], _), _Lexicon, _, % why not equivalent?
		br([nd( M, ((TTexp,Ty1~>Ty1) @ TT, Ty),    Args,    TF )],    Sig)
		===>
		br([nd( M1, TT, Args, TF)],  %!!! increase M list
		  Sig) )
:-
			%TF = true, % for mode(no_mod_set)
			cat_eq(Ty1, Ty),  %cat_eq(Ty2, Ty),
			%TTexp \= tlp(_,'not',_,_,_),
			\+(( TTexp = (tlp(_,Con,_,_,_),_) @ _,  member(Con, [if, and, or, who]) )), % exclude 'not'?
			( ( adjuncted_ttTerm(TT)
			  ; memberchk(Ty1, [s:_, np:_~>s:_, np:_~>np:_~>s:_])
			  ) ->
				append(M, [(TTexp,Ty1~>Ty1)], M1)
			  ;	TF = true,
				M1 = []
			).




% removes vacuous modifiers in any context: e.g. now
r(mod_vac,  impl:non,  ([], [], _), [['either'], ['now'], ['at_least'], ['currently']], _, %!!! yet the same as push_mod, why not equivalent?
		br([nd( M, ((TTexp,Ty1~>Ty2) @ TT, Ty2),  %!!! memory added
				Args, TF )],
		  Sig)
		===>
		br([nd( M, TT, Args, TF)],
		  Sig) )
:-
			cat_eq(Ty1, Ty2),
			TTexp = tlp(_,Vacuous,_,_,_),
			member(Vacuous, ['either', 'now', 'at_least', 'currently']).
			% currently fracas-251, either fracas-346

% treats pp complement as an intersective modifier
% e.g. nobel: (prize (for c1)): c2: T ---> nobel: prize: c2: T,  0: for c1: c2: T
% sick-5003
r(pp_com_n_tr,  impl:non,  ([], [], _), [[ty(pp)]], _KB-_XP, % equi?
		br([nd( Mods, ((tlp(Tk,Lm,POS,F1,F2),pp~>n:F) @ (PP,pp), n:_),	 Args, true )],
		  Sig)
		===>
		br([nd( Mods, (tlp(Tk,Lm,POS,F1,F2),n:F), 	Args, true),
		    nd( [],   (PP,pp),         				Args, true)],
		  Sig) )
:-
			true.
			%ul_append(XP, ['AforY(X)>A(X)&XforY']).

r(pp_com_n_fl,  impl:non,  ([], [], _), [[ty(pp)]], _KB-_XP, % equi?
		br([nd( Mods, ((tlp(Tk,Lm,POS,F1,F2),pp~>n:F) @ (PP,pp), n:_),	 Args, false )],
		  Sig)
		===>
		[ br([nd( Mods, (tlp(Tk,Lm,POS,F1,F2),n:F), 	Args, false)],
			Sig),
		  br([nd( [],   (PP,pp),         				Args, false)], % semantic term
		    Sig)
		])
:-
			true.

% in @ NP @ man: c: T ===> in @ NP: c: T  AND   man: c: T
r(pp_mod_n_tr,  impl:non,  ([], [], _), [[pos('RP')], [pos('IN')], [pos('TO')], [pos('RB')]], _KB-_XP, % equi?
		br([nd( Mods, (( (tlp(Tk,Lm,'IN',F1,F2),np:_~>n:_~>n:_) @ NP, n:_~>n:_) @ Noun, n:_),  % relax by removing Pos=IN?
				Args, true )],
		  Sig)
		===>
		br([nd( Mods, Noun,  								Args, 			true),
		    nd( Mods, (tlp(Tk,Lm,'IN',F1,F2), np:_~>pp), 	[NP | Args], 	true)], % why not empty mod
		  Sig) )
:-
			%( Mods = [_|_] -> report(['!!!Non-empty mod for pp_mod_n rule']); true ),
			true.
			%TLP_Prep = tlp(_,_Prep,'IN',_,_),
			%report(TLP, ' pp_mod_n rule is used vs push_mod'),
			%( NP = (TLP_NP, np:_) -> C = (TLP_NP, e) ; C = NP).  % redundant

% in @ NP @ man: c: F ===> in @ NP: c: F  OR   man: c: F
r(pp_mod_n_fl,  impl:non,  ([], [], _), [[pos('RP')], [pos('IN')], [pos('TO')], [pos('RB')]], _KB-_XP, % equi?
		br([nd( Mods, (( (tlp(Tk,Lm,'IN',F1,F2),np:_~>n:_~>n:_) @ NP, n:_~>n:_) @ Noun, n:_), 	Args, false )],  %relax by removing Pos=IN?
		  Sig)
		===>
		[ br([nd( Mods, Noun, 							           Args, false)],
			Sig),
		  br([nd( Mods, (tlp(Tk,Lm,'IN',F1,F2), np:_~>pp), 	[NP | Args], false)], % why not empty mod
		    Sig)
		])
:-
			%( Mods = [_|_] -> report(['!!!Non-empty mod for pp_mod_n rule']); true ),
			true.
			%TLP_Prep = tlp(Tk,Lm,'IN',F1,F2),
			%report(TLP, ' pp_mod_n rule is used vs push_mod'),
			%( NP = (TLP_NP, np:_) -> C = (TLP_NP, e); C = NP).  % redundant


% use the modifier list
% e.g. [M1,M2]: N: c1: T ---> 0: M1 N: c1: T,  0: M2 N: c1: T
r(mods_noun,  impl:non,  ([], [], _), _Lexicon, _KB-_XP,
		br([nd( [M | Rest], (tlp(Tk,Lm,POS,F1,F2), n:F),  Args, true )],  % Args = [c]
		  Sig)
		===>
		br(Nodes, Sig) )
:-
			%NounTLP =.. [tlp | _],
			modList_node_to_modNode_list( nd([M | Rest], (tlp(Tk,Lm,POS,F1,F2), n:F), Args, true ),  Nodes  ),
			!, %!!! should work for empty too
			Nodes \= []%, (Rest = [_,_|_] -> report(['Memory set has 3 items for mods_noun']); true)
			%, ( M = ((tlp(_,_,'IN',_,_),_) @ _, _) -> report(['!!!Rule mods_noun for prep+np used']); true )
			.

%!!! sick-train 2205?   Mod @ Sentence
r(mods_vp,  impl:non,  ([], [], _), _Lexicon, _KB-_XP, % sick 1754, 8714, 4054, 3222, 2284=2286 uses it
		br([nd( [M | Rest], (VP, np:F~>TyVP), 	Args, true )],  % Args = [c] %! only for trues
		  Sig)
		===>
		br(Nodes, Sig) )
:-
			const_ttTerm((VP, np:F~>TyVP)), %not necessary anymore actually
			final_value_of_type(TyVP, s:_),
			modList_node_to_modNode_list( nd([M | Rest], (VP, np:F~>TyVP), Args, true ),  Nodes  ), %!!! should work for empty too
			Nodes \= []%, (Rest = [_,_|_]  -> report(['Memory set has 3 items for mods_vp']); true)
			.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Prep@NP@VP:NP:F ---> Prep@NP@NP:F  OR  VP@NP:F, sick-254
% maybe not really sound rule, for amboguity with PPs
r(pp_mod_vp_fl,  equi:non,  ([], [], _), [[pos('RP')], [pos('IN')], [pos('TO')], [pos('RB')]], _,
		br([nd( M, (((tlp(Tk,Lm,'IN',F1,F2), np:_~>_) @ NP, (np:_~>s:_)~>np:_~>s:_) @ TTvp, _), 	[(C,Ty)], false )],
		  Sig)
		===>
		[	br([nd(M, TTvp,                                   [(C,Ty)], false )], Sig),
            br([nd([], (tlp(Tk,Lm,'IN',F1,F2), np:_~>pp),  [NP, (C,e)], false )], Sig)
		] )
:-
			true.

% Prep@NP@VP:NP:T ---> Prep@NP@NP:T  AND  VP@NP:T,
% maybe not really sound rule, for amboguity with PPs
r(pp_mod_vp_tr,  equi:non,  ([], [], _), [[pos('RP')], [pos('IN')], [pos('TO')], [pos('RB')]], _,
		br([nd( M, (((tlp(Tk,Lm,'IN',F1,F2), np:_~>_) @ NP, (np:_~>s:_)~>np:_~>s:_) @ TTvp, _), 	[(C,Ty)], true )],
		  Sig)
		===>
		br([nd( M, TTvp, [(C,Ty)], true ),
            nd([], (tlp(Tk,Lm,'IN',F1,F2), np:_~>pp),  [NP, (C,e)], true )],
          Sig) )
:-
			true.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% move pp-attachment from noun to verb, to fix wrong pp-attachments by parsers
% into:[c2,c3]:T & drop:[c3,c1]:T -> [into c2]:drop:[c3,c1]:T
% note that introduced node subsumes one of the antecednets, so better subtract_nodes/4 is needed
r(pp_attach,  impl:non,  ([], [], _), [[ty(pp)]], _, % sick-3626
		br([nd( _,   (TLP, pp), [C3], true ),
			nd( Mod, (TLP_VP, TyVP), Args_C3, true ) ], % TLP because M:VP[args] -> M@VP[args] via mods_vp and the rule is applable to M@VP[args]
		  Sig)
		===>
		br([nd(	[M|Mod], (TLP_VP, TyVP), Args_C3, true )],
		  Sig) )
:-
			once(( TLP =.. [tlp|_]; atom(TLP) )),
			once(( TLP_VP =.. [tlp|_]; atom(TLP_VP) )),
			memberchk(C3, Args_C3),
			final_value_of_type(TyVP, s:_),
			M =  (TLP, TyVP~>TyVP).

r(pp_attach,  impl:non,  ([], [], _), [[ty(pp)]], _,
		br([nd( _, (TLP, np:_~>pp), [C2,C3], true ),
			nd( Mod, (TLP_VP, TyVP), Args_C3, true ) ],
		  Sig)
		===>
		br([nd(	[M|Mod], (TLP_VP, TyVP), Args_C3, true )],
		  Sig) )
:-
			once(( TLP =.. [tlp|_]; atom(TLP) )),
			once(( TLP_VP =.. [tlp|_]; atom(TLP_VP) )),
			memberchk(C3, Args_C3),
			final_value_of_type(TyVP, s:_),
			M =  ((TLP, np:_~>TyVP~>TyVP) @ C2, TyVP~>TyVP).


% pull a by-phrase from a modifier list and apply first
% when is this used interesting
r(by_mod,  equi:non,  ([], [], _), [['by']], _, % sick 2704
		br([nd( [M|R], (tlp(Tk,Lm,Pos,F1,F2), np:E~>s:F),   Args, TF )],  % Args = [c]
		  Sig)
		===>
		br([nd(	Mod, (By_NP @ (tlp(Tk,Lm,Pos,F1,F2), np:E~>s:F), np:E~>s:F),   Args, TF )],
		  Sig) )
:-
			By_NP = ((tlp(_,'by','IN',_,_), np:_~>(np:_~>s:_)~>(np:_~>s:_)) @ _NP, _Type),
			choose([M|R], By_NP, Mod),
			%VP = tlp(Tk,Lm,Pos,F1,F2),
			atom_chars(Pos, ['V','B'|_]),
			!.


%!!! uses Mod, What is this doing???
% check where it is used
/*
r(mods_be,  impl:non,  _, [['be']], _KB, % this rule is not used! I guess mods_noun does the job
		br([nd( [M | Rest], (tlp(_,'be',_,_,_), np:_~>np:_~>s:_),
				Args, true )],
		  Sig)
		===>
		br(Nodes, Sig) )
:-
			maplist(tt_constant_to_tt_entity, Args, Args),
			modList_be_args_to_nodeList( [M | Rest], Args, Nodes ), %!!! may generate empty node list
			report(M, ' used for mods_be rule !!! was not expected to be usefull'),
			Nodes \= [].
*/
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%		Rules for Boolean operators
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

r(tr_conj_and,	equi:non,  ([], [], _), [['and']], _,
		br([nd( [], ( ( (tlp(_,'and',_,_,_), Ty1~>Ty2~>Ty) @ TT1, _ ) @ TT2, _ ),
				Args, true )],
		  Sig)
		===>
		br([nd(	[], TT1, Args, true ),
			nd( [], TT2, Args, true )],
		  Sig) )
:-
			cat_eq(Ty1, Ty2),
			cat_eq(Ty1, Ty).

r(fl_conj_and, 	equi:non,  ([], [], _), [['and']], _,
		br([nd( [], ( ( (tlp(_,'and',_,_,_), Ty1~>Ty2~>Ty) @ TT1, _ ) @ TT2, _ ),
				Args, false )],
		  Sig)
		===>
		[	br([nd([], TT1, Args, false )], Sig),
		 	br([nd([], TT2, Args, false )], Sig)
		] )
:-
			cat_eq(Ty1, Ty2),
			cat_eq(Ty1, Ty).


r(tr_conj_who,	equi:non,  ([], [], _), [['who']], _,
		br([nd( [], ( ( (tlp(_,'who',_,_,_), (np:_~>s:_)~>n:_~>n:_) @ TT1, _ ) @ TT2, _ ),
				Args, true )],
		  Sig)
		===>
		br([nd(	[], TT1, Args, true ),
			nd( [], TT2, Args, true )],
		  Sig) )
:-
		true.


r(fl_conj_who, 	equi:non,  ([], [], _), [['who']], _,
		br([nd( [], ( ( (tlp(_,'who',_,_,_), (np:_~>s:_)~>n:_~>n:_) @ TT1, _ ) @ TT2, _ ),
				Args, false )],
		  Sig)
		===>
		[	br([nd( [], TT1, Args, false )], Sig),
		 	br([nd( [], TT2, Args, false )], Sig)
		] )
:-
		true.


r(fl_disj_or,	equi:non, ([], [], _), [['or']], _,
		br([nd( [], ( ( (tlp(_,'or',_,_,_), Ty1~>Ty2~>Ty) @ TT1, _ ) @ TT2, _ ),
				Args, false )],
		  Sig)
		===>
		br([nd( [], TT1, Args, false ),
			nd( [], TT2, Args, false )],
		  Sig) )
:-
			cat_eq(Ty1, Ty2),
			cat_eq(Ty1, Ty).


r(tr_disj_or,	equi:non, ([], [], _), [['or']], _,
		br([nd( [], ( ( (tlp(_,'or',_,_,_), Ty1~>Ty2~>Ty) @ TT1, _ ) @ TT2, _ ),
				Args, true )],
		  Sig)
		===>
		[	br([nd( [], TT1, Args, true )], Sig),
		 	br([nd( [], TT2, Args, true )], Sig)
		] )
:-
			cat_eq(Ty1, Ty2),
			cat_eq(Ty1, Ty).



r(neg_not,  equi:non,  ([], [], _), [['not']], _,
		br([nd( M,  ( (tlp(_,'not',_,_,_), Ty1~>Ty2) @ TT, _ ),  %!!! added nonempty modifier
				Args, X )],
		  Sig)
		===>
		br([nd( M, TT, Args, Y )], Sig) )
:-
			cat_eq(Ty1, Ty2),
			neg(X, Y).



r(fl_if,  equi:non,  ([], [], _), [['if']], _,
		br([nd( [], ( ( (tlp(_,'if',_,_,_), Ty1~>Ty2~>Ty) @ TT1, _ ) @ TT2, _ ),
				Args, false )],
		  Sig)
		===>
		br([nd( [], TT1, Args, true),
			nd( [], TT2, Args, false)],
		  Sig) )
:-
			cat_eq(Ty1, Ty2),
			cat_eq(Ty1, Ty).


r(tr_if,  equi:non,  ([], [], _), [['if']], _,
		br([nd( [], ( ( (tlp(_,'if',_,_,_), Ty1~>Ty2~>Ty) @ TT1, _ ) @ TT2, _ ),
				Args, true )],
		  Sig)
		===>
		[	br([nd( [], TT1, Args, false )], Sig),
		 	br([nd( [], TT2, Args, true )], Sig)
		] )
:-
			cat_eq(Ty1, Ty2),
			cat_eq(Ty1, Ty).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%		Rules for Shifting Arguments
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

r(pull_arg,	 equi:non,  ([], [], _), _Lexicon, _,
		br([nd( M, ( abst(TT_X, TT), Type ),
				[TT_Arg | Args], TF)],
		  Sig)
		===>
		br([nd( M, TT_Red, Args, TF)], Sig) )
:-
			TT_Arg = (_, Ty1),
			sub_type(Type, Ty1 ~> Ty2),
			TT_X = (X, _), var(X),
			norm_tt( ( (abst(TT_X, TT), Type) @ TT_Arg, Ty2 ), TT_Red ), !.

r(beta_red,	 equi:non,  ([], [], _), _Lexicon, _, % fixes case when term is type rised nad has dummy P1 as an argument !!!
		br([nd( M, ((abst(TT_X, TT), Type) @ TT1, Ty2),
				Args, TF)],
		  Sig)
		===>
		br([nd( M, TT_Red, Args, TF)], Sig) )
:-
			TT1 = (_, Ty1),
			sub_type(Type, Ty1 ~> Ty2),
			TT_X = (X, _), var(X),
			norm_tt( ( (abst(TT_X, TT), Type) @ TT1, Ty2 ), TT_Red ), !.

%r(eta_red,	 equi:non,  _,

r(push_arg, impl:non, ([], [], _), _Lexicon, _,  % should not introduce
		br([nd( M, (TT1 @ TT2, _),
				Args, TF )],
		  Sig)
		===>
		br([nd( M, TT1, [TT2 | Args], TF )
			| Rest],
		  Sig) )
:-
			TT2 = (Term, Type), nonvar(Term),
			once((Term =.. [tlp | _]; atom(Term); Type = pp)),
			( Type = np:Feat, Feat \== 'thr' -> %!!! excluded there:np
				Rest = [nd(M,  TT1, [(Term, e) | Args], TF )] % what if Term is complex?
				%add_new_elements_in_the_end([TT2, (Term,e)], Sig, Sig1) % no need to add
			; Type = np:thr -> Rest = [] % for there:np
			; TT2 = (_Term, e) -> Rest = [] %add_new_elements_in_the_end([TT2], Sig, Sig1)
			; Type = pp, Rest = [] %maybe introduce a constant in Sig?
			).
% const(B), not necesary. B is never unbound var, it is typed later, accepts only atoms

% Assumes apposition because WH-clause is NP-modifier
r(push_arg, equi:non, ([], [], _), [['who']], _,
		br([nd( M, (TT1 @ (Wh_VP @ NP, np:_), _),
				Args, TF )],
		  Sig)
		===>
		br([nd( M, (TT1 @ NP1, Ty2), Args, TF ),
			nd([], (VP @ NP2, TyVP2), [], true)],
		  Sig) )
:-
			nonvar(Wh_VP),
			NP = (NP_term, _),
			VP = (_, TyVP1~>TyVP2),
			TT1 = (_, Ty1~>Ty2),
			Wh_VP = ((tlp(_,'who',_,_,_),(np:_~>s:_)~>_) @ VP, np:_~>np:_),
			( TyVP1 = np:_  -> NP2 = NP; NP2 = (NP_term, e) ),
			( Ty1 = np:_    -> NP1 = NP; NP1 = (NP_term, e) ).




% John:NNP:(np~>s)~>s @ VP:np~>s ---> VP @ John,np
r(type_drop, equi:non, ([], [], _), [[pos('NNP')]], _, % doesnt work this info
		br([nd( M, ((tlp(Tk,Lm,'NNP',F1,F2), (np:_~>s:_)~>s:_) @ (VP, np:_~>s:_), s:_), [], TF )],
		  Sig)
		===>
		br([nd( M, ((VP,np:_~>s:_) @ (tlp(Tk,Lm,'NNP',F1,F2),np:_), s:_), [], TF )],
		  Sig) )
:-
			true.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%		Rules for Monotone Operators
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%
% simpler aligner rule that is more general than up and dw arg rules
% what about same_mods rule?
r(same_args_tf,  impl:non,  ([], [], _), _Lexicon, KB_xp,  % non-symetric
		br([nd( M1, (G @ A, _), Args, true ),
			nd( M2, (H @ B, _), Args, false ) ],
		  Sig)
		===>
		br([nd( M1, G, [Y | Args], true ),
			nd( M2, H, [Y | Args], false )],
		  Sig) )
:-
			match_ttTerms(A, B, KB_xp),
			%match_list_ttTerms(M1, M2, KB_xp), %why not?
			Y = A,
			A = (_, Type1),
			B = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type).


r(same_args_xx,  impl:non,  ([], [], _), _Lexicon, KB_xp,  % symetric
		br([nd( M1, (G @ A, _), Args, TF ),
			nd( M2, (H @ B, _), Args, TF ) ],
		  Sig)
		===>
		br([nd( M1, G, [Y | Args], TF ),
			nd( M2, H, [Y | Args], TF )],
		  Sig) )
:-
			G \= H,
			match_ttTerms(A, B, KB_xp),
			Y = A,
			A = (_, Type1),
			B = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type).


% Monotone rules when arguments are in ISA relation
% Non-branching rule
r(up_mon_args,  impl:non,  ([], [], _), _Lexicon, KB_xp,
		br([nd( [],  (G @ A, _), Args, true ),
			nd( [], (H @ B, _), Args, false ) ],
		  Sig)
		===>
		br([nd( [], G, [Y | Args], true ),
			nd( [], H, [Y | Args], false )],
		  Sig) )
:-
			( tt_mon(G, up), Y = B;
			  tt_mon(H, up), Y = A;
			  %\+tt_mon(G, dw), Y = B;
			  %\+tt_mon(H, dw), Y = A;
			  %tt_mon_up(G), Y = B; % waht about a, the, several etc
			  %tt_mon_up(H), Y = A;
			  match_ttTerms(A, B, KB_xp), Y = A
			),
			\+proper_tt_isa(H, G, KB_xp), % makes rule more specific
			A = (_, Type1),
			B = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			( isa(A, B, KB_xp); match_ttTerms(A, B, KB_xp) ), !.

r(dw_mon_args,  impl:non,  ([], [], _), _Lexicon, KB_xp,
		br([nd( [], (G @ A, _), Args, true),
			nd( [], (H @ B, _), Args, false) ],
		  Sig)
		===>
		br([nd( [], G, [Y | Args], true),
			nd( [], H, [Y | Args], false)],
		  Sig) )
:-
			( tt_mon(G, dw), Y = B;
			  tt_mon(H, dw), Y = A
			),
			\+proper_tt_isa(H, G, KB_xp), % makes rule more specific
			A = (_, Type1),
			B = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			( isa(A, B, KB_xp); match_ttTerms(A, B, KB_xp) ), !.


%%%%%%%%%%%%%%%%%%%%%%
% Monotone rules when Functors are the same
% Non-branching rule


r(up_mon_fun_some,  impl:new,  ([], ArgList, Cids), [['a'], ['several'], ['many'], ['every'], ['most'], ['a_few'], ['both'], ['s']], KB_xp,
		br([nd( [], ((Some @ X, _TyX) @ A, _), Args, true),
			nd( [], ((Some @ Y, _TyY) @ B, _), Args, false) ],
		  Sig)
		===>
		br([nd([], A, ArgList, true),
			nd([], B, ArgList, false),
			nd([], X, ArgList, true) ], % apply new constant to formulas 2 as an old one
		  Sig1) )
:-
			Some = (tlp(_,Lemma,_,_,_), n:_~>(np:_~>s:_)~>s:_),
			member(Lemma, ['a', 'several', 'many', 'most', 'a_few', 'both', 's', 'every']), % "the" is not ok since we claim about N, the&the_c rules do this for 'the' POS = CD?
			match_ttTerms(X, Y, KB_xp),
			%tt_mon((Some @ X, TyX), _Up2),  %not necessary since lemma is set
			%tt_mon((Some @ Y, TyY), _Up1),  %not necessary since lemma is set
			A = (_, Type1),
			B = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			genFreshArgs(Type, ArgList, Sig, Sig1, Cids), !.


r(dw_mon_fun_few,  impl:new,  ([], ArgList, Cids), [['few'], ['no']], KB_xp,  % not really necesary and sound
		br([nd( [], ((Few @ X, _TyX) @ A, _), Args, true),
			nd( [], ((Few @ Y, _TyY) @ B, _), Args, false) ],
		  Sig)
		===>
		br([nd([], A, ArgList, false),
			nd([], B, ArgList, true),
			nd([], X, ArgList, true) ], % apply new constant to formulas 2 as an old one
		  Sig1) )
:-
			Few = (tlp(_,Lemma,_,_,_), n:_~>(np:_~>s:_)~>s:_),
			member(Lemma, ['few', 'no', 'neither']), % "the" is not ok since we claim about N, the&the_c rules do this for 'the' POS = CD?
			match_ttTerms(X, Y, KB_xp),
			%tt_mon((Some @ X, TyX), _Up2),  %not necessary since lemma is set
			%tt_mon((Some @ Y, TyY), _Up1),  %not necessary since lemma is set
			A = (_, Type1),
			B = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			genFreshArgs(Type, ArgList, Sig, Sig1, Cids), !.


r(up_mon_fun,  impl:new,  ([], ArgList, Cids), _Lexicon, KB_xp,
		br([nd([], (G @ A, _), Args, true),
			nd([], (H @ B, _), Args, false) ],
		  Sig)
		===>
		br([nd([], A, ArgList, true),
			nd([], B, ArgList, false)],
		  Sig1) )
:-
			match_ttTerms(G, H, KB_xp),
			tt_mon_up(G),
			tt_mon_up(H),
		    %%tt_mon(G, up),
			%%tt_mon(H, up),
			%\+tt_mon(G, dw),
			%\+tt_mon(H, dw),
			\+no_isa_rel_const_ttTerms(A, B, KB_xp), %!!! added recently avoids introduction of fresh constants
			A = (_, Type1),
			B = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			genFreshArgs(Type, ArgList, Sig, Sig1, Cids), !.  % these arguments can be ignored for gamma rules?


r(dw_mon_fun,  impl:new,  ([], ArgList, Cids), _Lexicon, KB_xp,
		br([nd([], (G @ A, _), Args, true),
			nd([], (H @ B, _), Args, false) ],
		  Sig)
		===>
		br([nd([], A, ArgList, false),
			nd([], B, ArgList, true)],
		  Sig1) )
:-
			match_ttTerms(G, H, KB_xp),
			tt_mon(G, dw),
			tt_mon(H, dw),
			\+no_isa_rel_const_ttTerms(A, B, KB_xp), %!!! added recently avoids introduction of fresh constants
			A = (_, Type1),
			B = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			genFreshArgs(Type, ArgList, Sig, Sig1, Cids), !.


%%%%%%%%%%%%%%%%%%%%%%
% Ordinary branching monotone rules
r(up_mon,  impl:new,  ([], ArgList, Cids), _Lexicon, KB_xp,
		br([nd([], (G @ A, _), Args, true),
			nd([], (H @ B, _), Args, false) ],
		  Sig)
		===>
		[	br([nd([], A, ArgList, true),
				nd([], B, ArgList, false)],
			  Sig1),
		    br([nd([], G, [Y | Args], true),
			    nd([], H, [Y | Args], false)],
			  Sig)
		] )
:-
			( tt_mon(G, up), Y = B;
			  tt_mon(H, up), Y = A
			  %\+tt_mon(G, dw), Y = B;
			  %\+tt_mon(H, dw), Y = A
			),
			\+proper_tt_isa(H, G, KB_xp), % makes rule more specific
			\+no_isa_rel_const_ttTerms(A, B, KB_xp), %!!! avoids unnecsaary branching
			G = (_, Type_G),
			H = (_, Type_H),
			sub_type(Type_G, Type_Fun),
			sub_type(Type_H, Type_Fun),
			A = (_, Type1),
			B = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			genFreshArgs(Type, ArgList, Sig, Sig1, Cids), !.


r(dw_mon,  impl:new,  ([], ArgList, Cids), _Lexicon, KB_xp,
		br([nd([], (G @ A, _), Args, true),
			nd([], (H @ B, _), Args, false) ],
		  Sig)
		===>
		[	br([nd([], A, ArgList, false),
				nd([], B, ArgList, true)],
			  Sig1),
		    br([nd([], G, [Y | Args], true),
				nd([], H, [Y | Args], false)],
			  Sig)
		] )
:-
			( tt_mon(G, dw), Y = B;
			  tt_mon(H, dw), Y = A
			),
			\+proper_tt_isa(H, G, KB_xp), % makes rule more specific
			\+no_isa_rel_const_ttTerms(A, B, KB_xp), %!!! avoids unnecsaary branching
			G = (_, Type_G),
			H = (_, Type_H),
			sub_type(Type_G, Type_Fun),
			sub_type(Type_H, Type_Fun),
			A = (_, Type1),
			B = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			genFreshArgs(Type, ArgList, Sig, Sig1, Cids), !.





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%	Gamma and Delta rules for every and some
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

r(tr_a,	 impl:new,  ([], Args, Cids),  [[pos('CD')], ['a'], ['many'], ['several'], ['most'], ['a_few'], ['both'], ['s']], _,
		br([nd( M, ( ( (tlp(_,A,POS,_,_), n:_~>(np:_~>s:_)~>s:_) @ TT1, _) @ TT2, _ ),  %!!! uses Mod
				[], true )],
		  Sig)
		===>
		br([nd( [], TT1, Args, true ),
			nd( M, TT2, Args, true )], 													%!!! uses Mod
		  Sig1) )
:-
			( 	member(A, ['a', 'many', 'several', 'most', 'a_few', 'both', 's']) % 'the' is excluded due to the-rule
			; 	POS = 'CD', A \= 'null'
			),
			TT1 = (_, Type1),
			TT2 = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			genFreshArgs(Type, Args, Sig, Sig1, Cids), !.

% "one" is required by SICK-1663
r(fl_a,	 gamma:non,  (Args, [], _), [['a'], ['s'], ['a_few'], ['another'], ['the'], ['one']], _,  %old
		br([nd( M, ( ( (tlp(_,Lemma,_,_,_),_) @ TT1, _ ) @ TT2, _ ),  % intro of M due to sick-4650
				[], false )],
		  [H|T])
		===>
		[	br([nd([], TT1, Args, false) ],
			  [H|T]),
		    br([nd([], TT1, Args, true),            % extra info, but could be done in diff way
			    nd(M, TT2, Args, false) ],
  			  [H|T])
		] )
:-
			member(Lemma, ['a', 's', 'a_few', 'another', 'the', 'one']), % the is not done by the-rule
			( debMode('thE') -> Lemma \= 'the'; true ),
			%member(Lemma, ['a', 'another', 'the']), % more strict
			TT1 = (_, Type1),
			TT2 = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			extract_const_ttTerm(TT1, Const1),
			extract_const_ttTerm(TT2, Const2),
			append([Const1, Const2], Const),
			genOldArgs(Type, Args, [H|T]),    % no cut here, oldArg selection needs backtrack
			intersection(Args, Const, []). 	  %!!! to avoid something like saw@c1@c1
   % Free variable implementation?

% !!! sc-train 1661 peel@c@c
% a A B : F and  A:c : T  ---> B:c : F % fracas-107
r(fl_a_c,	 impl:non, ([C], [], _), [['a'], ['a_few'], ['one']], KB_xp,  %!!! ['s']  This is not a gamma rule but shoul rule out applocation of gamma rule, we need C as info
		br([ nd(M, ( ( (tlp(_,Lemma,_,_,_), n:_~>(np:_~>s:_)~>s:_) @ TT1, _ ) @ TT2, _ ),    [],    false ),
			 nd(_, TT,    [C],    true ) %non_empty modlist
		   ],
		  Sig)
		===>
		br([nd(M, Other_TT, [C], false) ], Sig) )
:-
			member(Lemma, ['a', 'a_few', 'one']), %not 's' could be 'the' but it is done by the-rule
			%member(Lemma, ['a']), %more strict
			TT1 = (_, Type1),
			TT2 = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			( 	match_ttTerms(TT, TT1, KB_xp),
				Other_TT = TT2
			  ; match_ttTerms(TT, TT2, KB_xp),
				Other_TT = TT1
			), !.




% EVERY A B : T, gamma rule
r(tr_every,	 gamma:non,  (Args, [], _), [['every'], ['both']], _,  %old
		br([nd(M, ( ( (tlp(_,Every,_,_,_), n:_~>(np:_~>s:_)~>s:_) @ TT1, _ ) @ TT2, _ ),
				[], true )],
		  [H|T])
		===>
		[	br([nd([], TT1, Args, false) ],
			  [H|T]),
		    br([nd([], TT1, Args, true), % added information
			    nd(M, TT2, Args, true) ],
			  [H|T])
		] )
:-
			% both as universal causes S-train-1022 to loop
			member(Every, ['every', 'both']), %fracas-90 for 's' but not 91,94,95,98, so 's' is removed
			TT1 = (_, Type1),
			TT2 = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			extract_const_ttTerm(TT1, Const1),
			extract_const_ttTerm(TT2, Const2),
			append([Const1, Const2], Const),
			genOldArgs(Type, Args, [H|T]),   % no cut here, oldArg selection needs backtrack
			intersection(Args, Const, []).	 %!!! to avoid something like saw@c1@c1

% EVERY A B : T  and  A:c : T ---> B:c : T
% EVERY A B : T  and  B:c : F ---> A:c : F
r(tr_every_c,	 impl:non,  ([C], [], _), [['every']], KB_xp,  %old This is not a gamma rule
		br([ nd(M, ( ( (tlp(_,'every',_,_,_), n:_~>(np:_~>s:_)~>s:_) @ TT1, _ ) @ TT2, _ ),    [],    true ),
			 nd(M1, TT,    [C],    TF ) % if C_e than allow
		   ],
		  Sig)
		===>
		br([nd(M2, Other_TT, [C], TF) ], Sig) )
:-         %!!! if C_e than allow  Other_TT, [C_np], too Fracas-103
			%member(Every, [every]), %not "both"
			%member(Every, ['every', 'both', 's']), %fracas-99 for s
			TT1 = (_, Type1),
			TT2 = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			( 	match_ttTerms(TT, TT1, KB_xp), % saves fracas-49 rule app, swede,nnp vs swede nn
				Other_TT = TT2,
				M1 = [], M2 = M,
				TF = true
			  ; match_ttTerms(TT, TT2, KB_xp),
				Other_TT = TT1,
				match_list_ttTerms(M1, M, KB_xp), M2 = [],
				TF = false
			), !.



% every false
r(fl_every,	 impl:new,  ([], Args, Cids), [['every']], _,
		br([nd( M, ( ( (tlp(_,'every',_,_,_),_) @ TT1, _ ) @ TT2, _ ),
				[], false )],
		  Sig)
		===>
		br([nd([], TT1, Args, true),
			nd(M, TT2, Args, false) ],
		  Sig1) )
:-
			TT1 = (_, Type1),
			TT2 = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			genFreshArgs(Type, Args, Sig, Sig1, Cids), !.


% no true
r(tr_no,  gamma:non,  (Args, [], _), [['no']], _,
		br([nd(  M, ( ( (tlp(_,'no',_,_,_),_) @ TT1, _ ) @ TT2, _ ),
				[], true )],
		  [H|T])
		===>
		[	br([nd([], TT1, Args, false) ],
			  [H|T]),
		    br([nd([], TT1, Args, true),    % added information
			    nd( M, TT2, Args, false) ],
			  [H|T])
		] )
:-
			TT1 = (_, Type1),
			TT2 = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			genOldArgs(Type, Args, [H|T]). % no cut here, oldArg selection needs backtrack


r(tr_no_c,	 impl:non,  ([C], [], _), [['no']], KB_xp,  %old this is not a gamma rule
		br([ nd( M, ( ( (tlp(_,'no',_,_,_), n:_~>(np:_~>s:_)~>s:_) @ TT1, _ ) @ TT2, _ ),    [],    true ),
			 nd(M1, TT,    [C],    true )
		   ],
		  Sig)
		===>
		br([nd(M2, Other_TT, [C], false) ], Sig) ) %!!! fixed, before was true
:-
			%member(Every, [every]), %not "both"
			TT1 = (_, Type1),
			TT2 = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			( 	match_ttTerms(TT, TT1, KB_xp),
				M = M2, M1 = [],
				Other_TT = TT2
			  ; match_ttTerms(TT, TT2, KB_xp),
				match_list_ttTerms(M, M1, KB_xp), M2 = [],
				Other_TT = TT1
			), !.


% no false
r(fl_no,  impl:new,  ([], Args, Cids), [['no']], _,
		br([nd(M, ( ( (tlp(_,'no',_,_,_),_) @ TT1, _ ) @ TT2, _ ),
				[], false )],
		  Sig)
		===>
		br([nd([], TT1, Args, true),
			nd(M, TT2, Args, true) ],
		  Sig1) )
:-
			TT1 = (_, Type1),
			TT2 = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			genFreshArgs(Type, Args, Sig, Sig1, Cids), !.


% s A B: []: F ---> a A B: []: F


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%	Simplification rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
r(be_a_obj,  equi:non, ([], [], _), [['be','a'], ['be','s']], _,    % obj_be
		br([nd( M, ( ( (TLP, _TLP_ty) @ TT_N, _Ty ) @ (abst((X,XType), (Is_X_C,_)), np:_~>s:_), s:_ ),
				[], TF )],
		  Sig)
		===>
		br([nd( M, TT_N,
				[Arg], TF )],
		  Sig) )
:-
			TLP = tlp(_,Lem,_,_,_),
			memberchk(Lem, ['a', 's']), %!!! the?
			Is_X_C = ((tlp(_,'be',_,_,_),_) @ (X,XType), _) @ TT_C,
			const_ttTerm(TT_C),
			TT_C = (_, NPE), %added !!!
			(NPE = np:_; NPE = e),
			var(X), % makes shure that not bind accidentally
			( TT_C = (Term, np:F1) ->
				F1 \== thr, F1 \== prp,
				Arg = (Term, e)
			  ; Arg = TT_C
			),  %writeln('be_a_obj used!!!'),
			!.

r(a_subj_be,  equi:non, ([], [], _), [['be','a']], _,   % there is no need for it, never used % it is duplicate of be_obj
		br([nd( M, ( ( (TLP, _TLP_ty) @ TT_N, _Ty ) @ (((tlp(_,'be',_,_,_),_) @ TT_NP), np:_~>s:_), s:_ ),
				[], TF )],
		  Sig)
		===>
		br([nd( M, TT_N, % M added
				[Arg], TF )],
		  Sig) )
:-
			const_ttTerm(TT_NP),
			TT_NP = (_, NPE), %added !!!
			(NPE = np:_; NPE = e),
			TLP = tlp(_,Lem,_,_,_),
			memberchk(Lem, ['a']),  %!!! the? s?
			( TT_NP = (Term, np:F1) ->
				F1 \== thr, F1 \== prp,
				Arg = (Term, e)
			  ; Arg = TT_NP
			), %writeln('a_subj_be used!!!'),
			!.

/*
r(be_obj,  equi:non,  _, _Lexicon,
		br([nd( [], ( ( (TLP, _TLP_ty) @ TT_N, _Ty ) @ (((tlp(_,'be',_,_,_),_) @ TT_NP), np:_~>s:_), s:_ ),
				[], TF )],
		  Sig)
		===>
		br([nd( [], TT_N,
				[Arg], TF )],
		  Sig) )
:-
			TLP = tlp(_,Lem,_,_,_),
			member(Lem, ['a']), writeln('be_obj used!!!'),
			( TT_NP = (Term, np:F1) ->
				F1 \== thr, F1 \== prp,
				Arg = (Term, e)
			  ; Arg = TT_NP
			),
			!.
*/

r(be_pp,  equi:non,  ([], [], _),  [['be',pos('IN')]], _,
		br([nd( Mods, ( (tlp(_,'be',_,_,_),pp~>np:_~>s:_) @ (TT_PP @ TT_C, pp), np:_~>s:_ ),
				Args, TF )], % singleton e-type!!!
		  Sig)
		===>
		br([nd( Mods, TT_PP, % not necessary, np~>pp can do the job, or put both
				[TT_Ent | Args], TF )],
		  Sig) )
:-
			TT_PP = (tlp(_,_,'IN',_,_), np:_~>pp),
			tt_constant_to_tt_entity(TT_C, TT_Ent).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% rule for the A B when there is a constant of A
r(the_c,  impl:non,  ([(Term, e)], [], _), [['the']], KB_xp,
		br([nd( M, ( ( (tlp(_,'the',_,_,_),_) @ TT_N, _) @ TT_VP, s:_ ),	[], 	TF ),
			nd( _, (Noun, n:F1), 	[(Term, e)], 	true )   ], % mod is allowed
		  Sig)
		===>
		br([nd( M, TT_VP,	[(Term, e)], 	TF )], %added memory
		  Sig) )
:-
			( match_ttTerms(TT_N, (Noun, n:F1), KB_xp)
			; Noun = tlp(_,N2,_,_,_), TT_N = (tlp(_,N1,_,_,_), _), isa(N2, N1, KB_xp)
			).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% rule for the A B when there is NO constant of A
% considers mod list
r(the,  impl:new,  ([], Args, Cids), [['the']], _,
		br([nd( M, ( ( (tlp(Tk,'the',POS,F1,F2),Type_The) @ TT_N, _) @ TT_VP, s:_ ),	[], 	TF )],	% fracas 92, 93?
		  Sig)
		===>
		%br([nd( M, TT_VP,	Args, 	true ) | NodeList],
		br([nd( M, TT_VP,	Args, 	TF ),  SrcNode ],
		  Sig1) )
:-
			( debMode('thE') -> true; TF = true ),
			TT_N = (_, Type),
			%( TF = false -> M =[]; true ), % general case is good for 3373 with the_mode, but proves 8500 wrongly
			_The = (tlp(Tk,'the',POS,F1,F2),Type_The),
			SrcNode = nd( [], TT_N,	Args, true),
			%noun_node_to_isa_node_list(SrcNode, NodeList, KB),  %sick-3038, 8501 difference, good for contradictions
			genFreshArgs(Type, Args, Sig, Sig1, Cids).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% conjunction rules
r(arg_dist,	equi:non,  ([], [], _), [[pos('CC')]], _,  %maybe impl?  this rule needed by sick-7889
		br([nd( M, ( ( ( (TLP_CC, Ty~>Ty~>Ty) @ TT1, _ ) @ TT2, _ ) @ TTArg, Type),
				Args, TF )],
		  Sig)
		===>
		br([nd(	M, (((TLP_CC, Ty2~>Ty2~>Ty2) @ (TT1 @ TTArg, Type), Type~>Type) @ (TT2 @ TTArg, Type), Type),
				Args, TF )],
		  Sig) )
:-
			tlp_pos_in_list(TLP_CC, ['CC']),
			\+cc_as_fun(TTArg),
			%TTArg = (_, _ArgType). % check typing!!!
			TT1 = (_, _Ty1~>Ty2).

% distribute function only over entity arguments, sleep (and John Sam) -> (sleep John) and (sleep Sam)
r(fun_dist,	equi:non,  ([], [], _), [[pos('CC')]], _,  %!!! equi
		br([nd( M, (Fun @ (((TLP_CC, Ty~>Ty~>Ty) @ Arg1, _Ty1) @ Arg2, _Ty2), Type),
				Args, TF )],
		  Sig)
		===>
		br([nd(	M, (((TLP_CC, Type~>Type~>Type) @ (Fun @ Arg1, Type), Type~>Type) @ (Fun @ Arg2, Type), Type),
				Args, TF )],
		  Sig) )
:-
			\+cc_as_fun(Fun),
			tlp_pos_in_list(TLP_CC, ['CC']),
			memberchk(Ty, [np:_, e]).

r(det_dist,	equi:non,  ([], [], _), [[pos('CC')]], KB_xp,  %!!! equi
		br([nd( M,
                ((Det @ (((TLP_CC,n:_~>n:_~>n:_) @ A, _) @ B, _), Ty) @ VP, Type),
				[], TF )],
		  Sig)
		===>
		br([nd(	M,
                (((TLP_CC,n:_~>n:_~>n:_) @ ((Det@A,Type)@VP,Ty), Type~>Type) @ ((Det@B,Ty)@VP,Type), Type),
				[], TF )],
		  Sig) )
:-
			tlp_lemma_in_list(A, [Lm_A]),
			tlp_lemma_in_list(B, [Lm_B]),
			disjoint(Lm_A, Lm_B, KB_xp), !,
			tlp_lemma_in_list(Det, ['a','the','s','a_few','many']),
			tlp_pos_in_list(TLP_CC, ['CC']).

%but not with disjunction! every A (C or D) =/=> every A C or every A D !!!

r(fun_dist,	impl:non,  ([], [], _), [[pos('CC')]], _,  %impl!!! every A and B =/always/= every A and Every B,  some man sleep and eat =/= some man eat and some man sleep
		br([nd( M, (Fun @ (((TLP_CC, Ty~>Ty~>Ty) @ Arg1, _Ty1) @ Arg2, _Ty2), Type),
				Args, TF )],
		  Sig)
		===>
		br([nd(	M, (((TLP_CC, Type~>Type~>Type) @ (Fun @ Arg1, Type), Type~>Type) @ (Fun @ Arg2, Type), Type),
				Args, TF )],
		  Sig) )
:-
			\+cc_as_fun(Fun),
			tlp_pos_in_list(TLP_CC, ['CC']),
			Fun \= ((tlp(_,'a',_,_,_),_) @ _B, _),
			\+memberchk(Ty, [np:_, e]).



r(abst_dist, 	equi:non,  ([], [], _), _Lexicon, _,  %maybe impl?
		br([nd( M, (abst(TTx, (((tlp(Tk,Conj,Pos,F1,F2), Ty1~>Ty1~>Ty1) @ TT1, _) @ TT2, _)), _),
				Args, TF )],
		  Sig)
		===>
		br([nd(	M, (((tlp(Tk,Conj,Pos,F1,F2), Ty2~>Ty2~>Ty2) @ (abst(TTx, TT1), Type~>Type1), Ty2~>Ty2) @ (abst(TTx, TT2), Type~>Type1), Ty2),
				Args, TF )],
		  Sig) )
:-
			TTx = (X,_), var(X),
			Ty2 = Type~>Type1,
			TTx = (_, Type),
			%TT2 = (_, Type2),
			TT1 = (_, Type1).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% verb phrase modifier and pp complement

% pp complement as modifier: VP@PP [Args] => PP@VP [Args]
% kick@(near@John) ~> (near@John)@kick, sick-1469,44 needs it
r(vp_pp, 	impl:non,  ([], [], _),  [[ty(pp)]], _,
		br([nd( M, ((VP,Ty) @ (PP, pp), Type), %!!! before was only np:_~>s:_
				Args, TF )],
		  Sig)
		===>
		br([nd(	M, (Prep_NP @ VP1, Type),
                Args, TF )],
		  Sig) )
:-
		final_value_of_type(Ty, s:_), % vp, not to coinced with noun cases
		set_type_for_tt((PP, pp), Type~>Type, Prep_NP),
		set_type_for_tt((VP,Ty), Type, VP1).	% change s:pss to s:dcl?


% Next two rules makes equivalence: (jump over) c1 <=> (over c1) jump
% VP@Prep [NP,Args] => (Prep@NP)@VP [Args]
% sick-150, 1480, 1483, 7755, 6045, wrong-1481
r(v_pr_v_pp, 	impl:non, ([], [], _), [[pos('RP')], [pos('IN')], [pos('TO')], [pos('RB')]], _,
		br([nd( M, ( VP @ (tlp(Tk,Over,POS,F1,F2),_), TyS), [C, D | Rest], TF )],
			Sig) % why C, D? why not only C?
		===>
		br([nd( M, ((Prep @ C, TyVP~>TyVP) @ VP1, TyVP), [D | Rest], TF )],
			Sig) )
:-
			memberchk(POS, ['RP','IN','TO','RB']),
			final_value_of_type(TyS, s:_),
			TyS = np:_~>TyVP,
			set_type_for_tt(VP, TyVP, VP1),
			Prep = ( tlp(Tk,Over,'IN',F1,F2), np:_~>TyVP~>TyVP ).

% sick-8091 accidentally
% Prep@VP [NP,Args] => Prep@NP@VP [Args]
r(pr_v_v_pp, 	impl:non, ([], [], _), [[pos('RP')], [pos('IN')], [pos('TO')], [pos('RB')]], _,
		br([nd( M, ( (tlp(Tk,Over,POS,F1,F2), (np:_~>_)~>np:_~>_) @ VP, TyS ),  [C, D | Rest], TF )],
			Sig)
		===>
		br([nd( M, ((Prep @ C, TyVP~>TyVP) @ VP1, TyVP), [D | Rest], TF )],
			Sig) )
:-
			memberchk(POS, ['RP','IN','TO','RB']),
			final_value_of_type(TyS, s:_),
			TyS = np:_~>TyVP,
			set_type_for_tt(VP, TyVP, VP1),
			Prep = ( tlp(Tk,Over,'IN',F1,F2), np:_~>TyVP~>TyVP ).

% sick-3561, 4117
% Prep@VP [C] => VP@Prep [C]  % TODO is this necessary?
r(pr_v_v_pr, 	impl:non, ([], [], _), [[pos('RP')], [pos('IN')], [pos('TO')], [pos('RB')]], _,
		br([nd( M, ( (tlp(Tk,Over,POS,F1,F2), (np:_~>s:_)~>np:_~>s:_) @ VP, TyVP),  [C], TF )],
			Sig)
		===>
		br([nd( M, (VP1 @ (tlp(Tk,Over,POS,F1,F2), pr), TyVP),  [C], TF )],
			Sig) )
:-
			memberchk(POS, ['RP','IN','TO','RB']),
			set_type_for_tt(VP, pr~>TyVP, VP1).

% sick-3702
% VP@NP@Prep [C] => VP@Prep@NP [C]
r(v__pr_v_pr, 	impl:non, ([], [], _), [[pos('RP')], [pos('IN')], [pos('TO')], [pos('RB')]], _,
		br([nd( M, ( (VP @ NP, _) @ (tlp(Tk,Over,POS,F1,F2),TyP), TyVP ), [C], TF )],
			Sig)
		===>
		br([nd( M, ((VP1 @ (tlp(Tk,Over,POS,F1,F2),TyP), np:_~>TyVP) @ NP, TyVP), [C], TF )],
			Sig) )
:-
			memberchk(TyP, [pp, pr]),
			memberchk(POS, ['RP','IN','TO','RB']),
			NP = (_, NP_Ty),
			memberchk(NP_Ty, [np:_, e]),
			final_value_of_type(TyVP, s:_),
			set_type_for_tt(VP, TyP~>np:_~>TyVP, VP1).





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Attaching VP modifier to the argument
% mainly introduced to fix parse errors
% along@c3@(ride@c1)@c2 vs along@c3@c1, sick-200
/* replaced by cl_pp_attach2 closure rule
r(vpMod_to_argMod, 	impl:non, _, _Lexicon, _,   % VpMod_ArgMod rule for false sign, branching?
		br([nd( _M1, ( ((PP,np:_~>_)@NP, (np:_~>Ty1)~>np:_~>Ty2) @ (tlp(_,_,_,_,_),_), _), %!!! dont get
				[C|_], true )], % not for both signs
		  Sig)
		===>
		br([nd(	[], ( (PP, np:_~>pp) @ NP, pp ),
                [D], true )],
		  Sig) )
:-
		cat_eq(Ty1, Ty2),
		PP \= tlp(_,'by',_,_,_),
		%(TF = false -> M1 = []; true),
		C = (TLP, _),
		D = (TLP, e).
*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Verb in passive % IN necessary?
r(vp_pass1, 	impl:non,  ([], [], _), [['by']], _,
		br([nd( M, ((VPpss, pp~>TypePss) @ ((tlp(_,'by','IN',_,_), np:_~>pp) @ NP, pp), _), % sick-1745 s:dcl "is beng played"
				Args, TF )],
		  Sig)
		===>
		br([nd(	M, Verb, New_Args, TF ) | Rest],
		  Sig) )
:-
		final_value_of_type(TypePss, s:_),
		append(Args, [NP], New_Args),
		( NP = (Tr,np:_) ->
			append(Args, [(Tr,e)], New_Args1),
		  	Rest = [nd(M, Verb, New_Args1, TF)]
		  ; Rest = []
		),
		set_final_value_of_type(TypePss, TypeDcl, s:dcl),
		set_type_for_tt((VPpss, pp~>TypePss), np:_~>TypeDcl, Verb).

% IN necessary?
r(vp_pass2, 	impl:non,  ([], [], _), [['by']], _,
		br([nd( M, (((tlp(_,'by','IN',_,_), np:_~>(np:_~>s:_)~>(np:_~>s:_)) @ NP, _) @ Verb_Pass, np:_~>s:_), % sick-1745 s:dcl "is beng played"
				Args, TF )],
		  Sig)
		===>
		br([nd(	M, Verb, Args_NP1, TF ) | Rest],
		  Sig) )
:-
		( wh_mod_np_to_nodes(NP, NP1, WH_Nodes) -> true
		; NP1 = NP, WH_Nodes = [] ),
		% move arg NP at the end of the arg list
		append(Args, [NP1], Args_NP1),
		% add a node for NP:e too
		( NP1 = (Tr,np:_) ->
			append(Args, [(Tr,e)], Args_NPe),
			Rest = [nd(M, Verb, Args_NPe, TF) | WH_Nodes]
		; Rest = WH_Nodes ),
		Verb_Pass = (_, TypePss),
		set_final_value_of_type(TypePss, TypeDcl, s:dcl),
		set_type_for_tt(Verb_Pass, np:_~>TypeDcl, Verb).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Rules related to "group of ..."

% Group(of C):[G]:T & VP:[G]:TF => VP:[C]:TF
% sick-410
r(group_of,	 impl:non,  ([C], [], _),
  [['of','group'], ['of','body'], ['of','piece'], ['of','slice'], ['of','crowd'], ['of','bunch'], ['of','herd'], ['of','pair']],
  _KB-_XP,
%old this is not a gamma rule, Why we put C here?
		br([ nd( _, ( (tlp(_,Group,_,_,_),pp~>n:_) @ ((tlp(_,'of',_,_,_),np:_~>pp)@C, pp), n:_ ),  [G],  true ),
			 nd(M, (VP, np:F1~>s:F2),    [D],    TF ) % TT should be of type VP, otherwise C will be group too, Play with it
		   ],
		  Sig)
		===>
		br([nd(M, (VP, np:F1~>s:F2), [B], TF) ], Sig) ) %!!! like equality, C = G
:-
		member(Group, ['group', 'body', 'piece', 'slice', 'crowd', 'bunch', 'herd', 'pair']),
		memberchk((D,B), [(G,C), (C,G)]).
		%add_heads((Group,pp~>n:_), (_,_,tlp(_,'group',_,_,_))).

r(group_of,	 impl:non,  ([C], [], _),
  [['of','group'], ['of','body'], ['of','piece'], ['of','slice'], ['of','crowd'], ['of','bunch'], ['of','herd'], ['of','pair']],
  _KB-_XP,
% for easyccg like analyses
		br([ nd( _, ( ((tlp(_,'of',_,_,_),np:_~>n:_~>n:_)@C, _) @ (tlp(_,Group,_,_,_),n:_), _ ),  [G],  true ),
			 nd(M, (VP, np:F1~>s:F2),    [D],    TF ) % TT should be of type VP, otherwise C will be group too, Play with it
		   ],
		  Sig)
		===>
		br([nd(M, (VP, np:F1~>s:F2), [B], TF) ], Sig) ) %!!! like equality, C = G
:-
		member(Group, ['group', 'body', 'piece', 'slice', 'crowd', 'bunch', 'herd', 'pair']),
		memberchk((D,B), [(G,C), (C,G)]).

% A@(Group(of C))@VP:[]:F => VP:[C]:F
% sick-2472
r(a_group_of,	 impl:non,  ([], [], _),
  [['of','group'], ['of','body'], ['of','piece'], ['of','slice'], ['of','crowd'], ['of','bunch'], ['of','herd'], ['of','pair']],
  _KB-_XP,
		br([ nd(M, ((A @ ((tlp(_,GR,_,_,_),pp~>n:_)@((tlp(_,'of',_,_,_),np:_~>pp)@C, pp), n:_), _) @ VP, s:_),  [],  false ) % could be true also ~group_of
		   ],
		  Sig)
		===>
		br([nd(M, VP, [C], false) ], Sig) )
:-
		A = (tlp(_,Lm,_,_,_), n:_~>(np:_~>s:_)~>s:_),
		member(Lm, ['a', 'the', 'this']),
		member(GR, ['group', 'body', 'piece', 'slice', 'crowd', 'bunch', 'herd', 'pair']).
		%add_heads((Group,pp~>n:_), (_,_,tlp(_,'group',_,_,_))).

% for easyccg style analyses sick-5264
r(a_group_of,	 impl:non,  ([], [], _),
  [['of','group'], ['of','body'], ['of','piece'], ['of','slice'], ['of','crowd'], ['of','bunch'], ['of','herd'], ['of','pair']],
  _KB-_XP,
		br([ nd(M, ((A @ (((tlp(_,'of',_,_,_),np:_~>n:_~>n:_)@C, _) @ (tlp(_,GR,_,_,_),n:_), _), _) @ VP, s:_),  [],  false )
		   ],
		  Sig)
		===>
		br([nd(M, VP, [C], false) ], Sig) )
:-
		A = (tlp(_,Lm,_,_,_), n:_~>(np:_~>s:_)~>s:_),
		member(Lm, ['a', 'the', 'this']),
		member(GR, ['group', 'body', 'piece', 'slice', 'crowd', 'bunch', 'herd', 'pair']).
		%add_heads((Group,pp~>n:_), (_,_,tlp(_,'group',_,_,_))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Rule for factive attitude verbs
r(fact_v_s_tr,	impl:non, ([], [], _), _Lexicon, _,  %fracas-334  % add constraint to lexicon
		br( [nd( _M, ( (tlp(_,FactV,_,_,_),s:_~>np:_~>s:_) @ Sen, np:_~>s:_),
				 _Args, true )],
		  Sig)
		===>
		br( [nd( [], Sen , [], true)],
		  Sig) )
:-
		factive(FactV).

r(fact_v_tr,	impl:non, ([], [], _), _Lexicon, _,  % fracas-342   % add constraint to lexicon
		br( [nd( _M, (( (tlp(_,FactV,_,_,_),_Ty1) @ (NP1,NPTy), _Ty2) @ (VP,np:F1~>s:F2), _Ty3),
				 _Args, true )],
		  Sig)
		===>
		br( [nd( [], ((VP,np:F1~>s:F2) @ (NP1,NPTy), s:F2) , [], true)],
		  Sig) )
:-
		%Fact_TLP = tlp(_,Lemma,_,_,_),
		(NPTy = np:_; NPTy = e),
		factive(FactV).

r(fact_v_fl,	impl:non, ([], [], _), _Lexicon, _,   % add constraint to lexicon
		br( [nd( _M, (( (tlp(_,FactV,_,_,_),_Ty1) @ (NP1,NPTy), _Ty2) @ (VP,np:F1~>s:F2), _Ty3),
				 _Args, false )],
		  Sig)
		===>
		[	br( [nd( [], ((VP,np:F1~>s:F2) @ (NP1,NPTy), s:F2) , [], true)],   Sig),
		    br( [nd( [], ((VP,np:F1~>s:F2) @ (NP1,NPTy), s:F2) , [], false)],  Sig)
		] )
:-
		(NPTy = np:_; NPTy = e),
		%Fact_TLP = tlp(_,Lemma,_,_,_),
		factive(FactV).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% rule for verbs like manage: manage VP NP ---> VP NP
r(ho_verb,	impl:non, ([], [], _), [['manage']], _,
		br( [nd( M, ((tlp(_Tk,Lm,POS,_,_), (np:_~>s:_)~>np:_~>s:_) @ VP, _), [Arg], TF )],
		  Sig)
		===>
		br( [nd( M, VP, [Arg], TF)],
		  Sig) )
:-
		atom_chars(POS,['V','B' | _]),
		memberchk(Lm, ['manage']).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% It is false, It is true
r(it_is_tr_fl,  equi:non,  ([], [], _), [['it']], _,
		br([nd( [],  ( (((tlp(_,'be',_,_,_), (np:_~>s:_)~>s:_~>np:expl~>s:_) @ TrueFalse, _Ty1) @ S_em, _Ty2) @ IT, _ ),
				[], X )],
		  Sig)
		===>
		br([nd( [], S_em, [], Y )], Sig) )
:-
			IT = (tlp(_,'it',_,_,_),_),
			TrueFalse = (tlp(_,Lemma,_,_,_),_),
			( Lemma = 'true' ->
				Y = X
			  ; neg(X, Y)
			).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Rules for Cradinals

% rule for cardinal modifiers: just N, exactly N
% fracas-105
r(cardinal_mod, 	impl:non, ([], [], _), [['exactly'], ['just']], _,
		br([nd( M, ((((tlp(_,Lm_RB,_,_,_), (n:_~>(np:_~>s:_)~>s:_)~>n:_~>(np:_~>s:_)~>s:_) @ TT_CD, _) @ TTn, _) @ TTvp, s:_),  Args, true )],
		  Sig)
		===>
		br([nd( M, ((TT_CD @ TTn, (np:_~>s:_)~>s:_) @ TTvp, s:_), Args, true )],
		  Sig) )
:-
			memberchk(Lm_RB, ['exactly', 'just']).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Transformation rules

% rule for transforming expletives to canonical form
% e.h there are few singers from Georgia -> few singers are from Georgia
% fracas-44
r(there_trans, 	equi:non, ([], [], _), [['there', pos('IN')]], _,
		br([nd( M, ((Q @ ((IN@NP,n:_~>n:_)@N,n:_), (np:_~>s:_)~>s:_) @ (abst(_X,((BE@A,np:_~>s:_)@B,s:_)),np:_~>s:_), s:F),  [], TF )],
		  Sig)
		===>
		br([nd( M, ((Q @ N, (np:_~>s:_)~>s:_) @ (IS @ PP, np:_~>s:_), s:F),  [], TF )],
		  Sig) )
:-
			IN = (tlp(Tk,Lm,'IN',F1,F2), np:_~>n:_~>n:_),
			PP = ((tlp(Tk,Lm,'IN',F1,F2), np:_~>pp) @ NP, pp),
			BE = (tlp(Tk1,'be',Pos1,F11,F21), _),
			IS = (tlp(Tk1,'be',Pos1,F11,F21), pp~>np:_~>s:_),
			( A = (_, np:thr);  B = (_, np:thr) ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Equality rules, restricted version
% e.g. fracas-343
r(equal1, 	impl:non, ([], [], _), [['be']], _,
		br([nd( M, (tlp(_,'be',_,_,_), np:_~>np:_~>s:_),  [A, B], true ),
			nd( M, P, [A], TF )
		   ],
		  Sig)
		===>
		br([nd( M, P, [B], TF )],
		  Sig) )
:-
			true.

r(equal2, 	impl:non, ([], [], _), [['be']], _,
		br([nd( M, (tlp(_,'be',_,_,_), np:_~>np:_~>s:_),  [A, B], true ),
			nd( M, P, [B], TF )
		   ],
		  Sig)
		===>
		br([nd( M, P, [A], TF )],
		  Sig) )
:-
			true.
