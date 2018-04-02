%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: Tableau Rules
%     Version: 12.06.12
%      Author: lasha.abzianidze{at}gmail.com 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- multifile r/4.

rule_priority([
	%cl_subcat, cl_ant,
	pull_arg, beta_red, type_drop,
	tr_conj_and, fl_conj_and, tr_conj_who, fl_conj_who, fl_disj_or, tr_disj_or, neg_not, fl_if, tr_if, 
	%contra_do_vp, contra_there, 
	aux_verb, ho_verb,
	poss_tr, cardinal_mod, not_quant,
	be_pp, be_a_s, be_a_obj, a_subj_be, vp_pass1, vp_pass2, vp_pp,
	the_c, %the, 
	fact_v_s_tr, fact_v_tr, fact_v_fl, it_is_tr_fl,
	tr_every_c, fl_a_c, tr_no_c, 
	mod_pull_by, pp_mod_vp_fl, 
	mod_vac, int_mod_tr, int_mod_fl, mod_n_tr, push_mod, 
	pp_mod_n_tr, pp_mod_n_fl,
	n_pp_mod, mods_noun, mods_vp, mods_be, vpMod_to_argMod,
	%up_mon_args, dw_mon_args, up_mon_fun_some, up_mon_fun, dw_mon_fun, % doesn't matter order
	push_arg,
	arg_dist, abst_dist, fun_dist, % fun dist not good?
	up_mon_args, dw_mon_args, up_mon_fun_some, up_mon_fun, dw_mon_fun, 
	up_mon, dw_mon,
	tr_a, fl_a, tr_every, fl_every, tr_no, fl_no,
	the
]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 		Rules introducing contradictions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/*
% closure related to verb subcategorization
r(cl_subcat, equi:non, _,  %sick-1881
		br([nd( _, (Tr1, Ty1), Args1, true ),
			nd( [], (Tr2, Ty2), Args2, false )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			( Tr1 =@= Tr2 % avoids matching variable to term, var(X) for variables can slove the global problem
			; Tr1 = tlp(_,Lm,_,_,_), Tr2 = tlp(_,Lm,_,_,_) 
			),
			Ty1 = np:_~>TyS1,
			final_value_of_type(TyS1, s:_),
			Ty2 = np:_~>TyS2,
			final_value_of_type(TyS2, s:_),
			append(_, Args2, Args1), !.

% closure related to antonym words
r(cl_ant, equi:non, _,  %sick-1881
		br([nd( _, (tlp(_,Lm1,_,_,_), Ty1), Args, true ),
			nd( _, (tlp(_,Lm2,_,_,_), Ty2), Args, true )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			cat_eq(Ty1, Ty2),
			ant_wn(Lm1, Lm2), !.

r(contra_there, equi:non, _, 
		br([nd( M, (((tlp(_,'be',_,_,_),_) @ _TT, _) @ (tlp(_,'there',_,_,_),np:thr), s:_) ,
				[], TF )],
		  Sig)
		===>
		br([nd( [], (true, t), [], TF )], % only semnatic terms
		  Sig) ) 
:-
			(TF = false -> M =[]; true).

% C1 did C2, Dance(C2) -> Danced(C1)
r(contra_do_vp, equi:non, _, 
		br([nd( M1, (tlp(_,'do',_,_,_), np:_~>np:_~>s:_), 	[C2, C1], 	TF1 ),
		    nd( _, (tlp(_,Dance,'NN',_,_), n:_),			[C2],		TF2 ),
			nd( M3, (tlp(_,Dance,_,_,_), np:_~>s:_),			[C1],		TF3 )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )], % only semnatic terms
		  Sig) ) 
:-
			(	(TF1, TF2, TF3) = (true, true, false), M3 = [] 
			;	(TF1, TF2, TF3) = (false, true, true), M1 =[]
			).
*/
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%		Linguistic Rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% remove "do", "will" modifying verb phrase
r(aux_verb,  equi:non,  _,
		br([nd( M, ( (tlp(_,Aux,_,_,_), Type1~>Type2) @ TT1, _ ), 
				Args, TF )], 
		  Sig) 
		===>
		br([nd( M, TT1, Args, TF)], 
		  Sig) )
:-
		cat_eq(Type1, Type2),
		final_value_of_type(Type1, s:_),					
		member(Aux, ['do', 'will', 'be', 'become', 'to', 'that', 'have']), !. 
% maybe "become" in false context is not correct 
% it is true THAT ...



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% possessive determiner in true context
% sick-5003
r(poss_tr, impl:new, (_, Cids), 
		br([nd( M, (((( TLP_poss, np:_~>n:_~>(np:_~>s:_)~>s:_) @ TTnp, _) @ TTn, _) @ TTnp_s, _),
				[], true )],
		  Sig)
		===>
		br([nd( [], TTn, Args, true ), 
			nd( M, TTnp_s, Args, true ),
			nd( [], (TLP_poss, np:_~>pp), [(NP,e)| Args], true )], % only semnatic terms % why not "of"?
		  Sig1) )
:-	 
		TLP_poss = tlp(_,'\'s','POS',_,_),
		TTnp_s = (_, Type1),
		TTn = (_, Type2),
		TTnp = (NP,_), % NP is tlp?
		sub_type(Type1, Type),
		sub_type(Type2, Type),
		genFreshArgs(Type, Args, Sig, Sig1, Cids), !.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% remove quantifier modifier not: not all A B :X -> all A B: -X
r(not_quant,  equi:non,  _,
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
r(int_mod_tr, impl:non, _, % equi
		br([nd( M,  ((TLP, n:_~>n:_) @ TTn, n:_),
				[(C,e)], true )],
		  Sig)
		===>
		br([nd( M,  TTn, [(C,e)], true ),
			nd( [], (TLP, e~>t), [(C,e)], true )],
		  Sig) )
:-
		TLP = tlp(_,Lemma,POS,_,_),
		( intersective(Lemma)
		%; (POS = 'JJ', \+privative(Lemma)) % relaxing constraints
		; atom_chars(POS, ['V','B'|_]) % verbs are as intersective adjectives
		), !.

% intersective noun modifier in false context 
%branching could be in different way too
r(int_mod_fl, impl:non, _, 
		br([nd( M, ((TLP, n:_~>n:_) @ TTn, n:_),
				[(C,e)], false )],
		  Sig)
		===>
		[ 	br([nd( M, TTn, [(C,e)], false )], 
			  Sig),
			br([nd( [], (TLP, e~>t), [(C,e)], false ),
			    nd( M,  TTn, [(C,e)], true ) ], 
			  Sig) 
		] )
:-
		
		TLP = tlp(_,Lemma,POS,_,_),
		( intersective(Lemma)
		%; POS = 'JJ' % relaxing constraints sick-2791
		; atom_chars(POS, ['V','B'|_]) % verbs are as intersective adjectives sick-2722
		), !.
	


% non-intersective noun modifier in true context
r(mod_n_tr, impl:non, _, 
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
		).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% removes any modifier, except negeation
r(push_mod,  impl:non,  _,
		br([nd( M, ((TTexp,Ty1~>Ty1) @ TT, Ty),    Args,    TF )],    Sig) 
		===>
		br([nd( M1, TT, Args, TF)],  %!!! increase M list
		  Sig) )
:-
			cat_eq(Ty1, Ty),  %cat_eq(Ty2, Ty),
			%TTexp \= tlp(_,'not',_,_,_),
			\+(( TTexp = (tlp(_,Con,_,_,_),_) @ _,  member(Con, [if, and, or, who]) )), % exclude 'not'?
			( ( adjuncted_ttTerm(TT)
			  ; Ty1 = np:_~>s:_
			  ; Ty1 = np:_~>np:_~>s:_
			  ) ->
				append(M, [(TTexp,Ty1~>Ty1)], M1)
			  ;	TF = true, 
				M1 = []
			).			
				



% removes vacuous modifiers in any context: e.g. now
r(mod_vac,  impl:non,  _, %!!! yet the same as push_mod
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
r(n_pp_mod,  impl:non,  _,
		br([nd( Mods, ((NounTLP,pp~>n:F) @ (PP,pp), n:_), 
				Args, true )], 
		  Sig) 
		===>
		br([nd( Mods, (NounTLP,n:F), 
				Args, true),
		    nd( [], (PP,pp), 
				Args, true)], 
		  Sig) )
:-
			NounTLP =.. [tlp | _].

% in @ NP @ man: c: T ===> in @ NP: c: T  AND   man: c: T
r(pp_mod_n_tr,  impl:non,  _,
		br([nd( Mods, (( (TLP_Prep,np:_~>n:_~>n:_) @ NP, n:_~>n:_) @ Noun, n:_), 
				Args, true )], 
		  Sig) 
		===>
		br([nd( Mods, Noun, 
				Args, true),
		    nd( Mods, (TLP_Prep, np:_~>pp), % could be a semantic term 
				[C | Args], true)], 
		  Sig) )
:-
			TLP_Prep = tlp(_,_Prep,'IN',_,_),
			%report(TLP, ' pp_mod_n rule is used vs push_mod'),	
			( NP = (TLP_NP, np:_) ->
				C = (TLP_NP, e)
			  ; C = NP
			). 

% in @ NP @ man: c: F ===> in @ NP: c: F  OR   man: c: F
r(pp_mod_n_fl,  impl:non,  _,
		br([nd( Mods, (( (TLP_Prep,np:_~>n:_~>n:_) @ NP, n:_~>n:_) @ Noun, n:_), 	Args, false )], 
		  Sig) 
		===>
		[ br([nd( Mods, Noun, 			Args, false)],
			Sig),
		  br([nd( Mods, (TLP_Prep, np:_~>pp), 	[C | Args], false)], % semantic term 
		    Sig)
		])
:-
			TLP_Prep = tlp(_,_Prep,'IN',_,_),
			%report(TLP, ' pp_mod_n rule is used vs push_mod'),	
			( NP = (TLP_NP, np:_) ->
				C = (TLP_NP, e)
			  ; C = NP
			). 


% use the modifier list
% e.g. [M1,M2]: N: c1: T ---> 0: M1 N: c1: T,  0: M2 N: c1: T 
r(mods_noun,  impl:non,  _,
		br([nd( [M | Rest], (NounTLP, n:F), 
				Args, true )],  % Args = [c]
		  Sig) 
		===>
		br(Nodes, Sig) )
:- 
			NounTLP =.. [tlp | _],
			modList_node_to_modNode_list( nd([M | Rest], (NounTLP, n:F), Args, true ),  Nodes  ), 
			!, %!!! should work for empty too
			Nodes \= []%, ( M = ((tlp(_,_,'IN',_,_),_) @ _, _) -> report(['!!!Rule mods_noun for prep+np used']); true )
			.

r(mods_vp,  impl:non,  _, % sick 1754, 8714, 4054, 3222, 2284=2286 uses it
		br([nd( [M | Rest], (VP, np:F~>TyVP), 
				Args, true )],  % Args = [c]
		  Sig) 
		===>
		br(Nodes, Sig) )
:- 
			const_ttTerm((VP, np:F~>TyVP)),
			final_value_of_type(TyVP, s:_), 
			modList_node_to_modNode_list( nd([M | Rest], (VP, np:F~>TyVP), Args, true ),  Nodes  ), %!!! should work for empty too
			Nodes \= []
			.

% Prep@NP@VP:NP:F ---> Prep@NP@NP:F  OR  VP@NP:F, sick-254
r(pp_mod_vp_fl,  equi:non,  _,
		br([nd( [], (((Prep, np:_~>_) @ NP1, (np:_~>s:_)~>np:_~>s:_) @ TTvp, _), 
				[C], false )],  % Args = [c]
		  Sig) 
		===>
		[	br([nd([], ((Prep,np:_~>pp) @ NP1, pp), 
					[Arg], false )], Sig), 
		 	br([nd([], (TTvp @ C, s:_), 
					[], false )], Sig)
		] )
:-
			Prep = tlp(_,_,'IN',_,_),
			C = (TLP, _Ty),
			Arg = (TLP, e).
			



% pull a by-phrase from a modifier list and apply first
r(mod_pull_by,  equi:non,  _, % sick 2704
		br([nd( [M|R], (VP, np:E~>s:F), Args, TF )],  % Args = [c]
		  Sig) 
		===>
		br([nd(	Mod, (By_NP @ (VP, np:E~>s:F), np:E~>s:F), Args, TF )],
		  Sig) )
:- 
			By_NP = ((tlp(_,'by','IN',_,_), np:_~>(np:_~>s:_)~>(np:_~>s:_)) @ _NP, _Type), 
			choose([M|R], By_NP, Mod),
			VP = tlp(_,_,Pos,_,_),
			atom_chars(Pos, ['V','B'|_]),
			!.
			

%!!! uses Mod, What is this doing???
r(mods_be,  impl:non,  _, % this rule is not used! I guess mods_noun does the job
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%		Rules for Boolean operators
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

r(tr_conj_and,	equi:non,  _,
		br([nd( [], ( ( (tlp(_,and,_,_,_), Ty1~>Ty2~>Ty) @ TT1, _ ) @ TT2, _ ), 
				Args, true )], 
		  Sig) 
		===> 
		br([nd(	[], TT1, Args, true ), 
			nd( [], TT2, Args, true )], 
		  Sig) )
:-
			cat_eq(Ty1, Ty2),
			cat_eq(Ty1, Ty).

r(fl_conj_and, 	equi:non,  _,
		br([nd( [], ( ( (tlp(_,and,_,_,_), Ty1~>Ty2~>Ty) @ TT1, _ ) @ TT2, _ ),
				Args, false )], 
		  Sig) 
		===> 
		[	br([nd([], TT1, Args, false )], Sig), 
		 	br([nd([], TT2, Args, false )], Sig)
		] )
:-
			cat_eq(Ty1, Ty2),
			cat_eq(Ty1, Ty).


r(tr_conj_who,	equi:non,  _,
		br([nd( [], ( ( (tlp(_,who,_,_,_), (np:_~>s:_)~>n:_~>n:_) @ TT1, _ ) @ TT2, _ ), 
				Args, true )], 
		  Sig) 
		===> 
		br([nd(	[], TT1, Args, true ), 
			nd( [], TT2, Args, true )], 
		  Sig) )
:-
		true.

	
r(fl_conj_who, 	equi:non,  _,
		br([nd( [], ( ( (tlp(_,'who',_,_,_), (np:_~>s:_)~>n:_~>n:_) @ TT1, _ ) @ TT2, _ ),
				Args, false )], 
		  Sig) 
		===> 
		[	br([nd( [], TT1, Args, false )], Sig), 
		 	br([nd( [], TT2, Args, false )], Sig)
		] )
:-
		true.


r(fl_disj_or,	equi:non, _,
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

		
r(tr_disj_or,	equi:non, _,
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


	
r(neg_not,  equi:non,  _,
		br([nd( M,  ( (tlp(_,'not',_,_,_), Ty1~>Ty2) @ TT, _ ),  %!!! added nonempty modifier
				Args, X )], 
		  Sig) 
		===>
		br([nd( M, TT, Args, Y )], Sig) )
:-
			cat_eq(Ty1, Ty2),		
			neg(X, Y).



r(fl_if,  equi:non,  _,
		br([nd( [], ( ( (tlp(_,if,_,_,_), Ty1~>Ty2~>Ty) @ TT1, _ ) @ TT2, _ ), 
				Args, false )], 
		  Sig) 
		===>
		br([nd( [], TT1, Args, true), 
			nd( [], TT2, Args, false)], 
		  Sig) )
:-
			cat_eq(Ty1, Ty2),
			cat_eq(Ty1, Ty).

		
r(tr_if,  equi:non,  _,
		br([nd( [], ( ( (tlp(_,if,_,_,_), Ty1~>Ty2~>Ty) @ TT1, _ ) @ TT2, _ ), 
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

r(pull_arg,	 equi:non,  _,
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

r(beta_red,	 equi:non,  _, % fixes case when term is type rised nad has dummy P1 as an argument !!!
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
 	
r(push_arg, impl:non, _, % but introduces
		br([nd( M, (TT1 @ TT2, _), 
				Args, TF )], 
		  Sig) 
		===> 
		br([nd( M, TT1, [TT2 | Args], TF ) 
			| Rest], 
		  Sig1) )
:-
			TT2 = (Term, Type),
			nonvar(Term),
			once((Term =.. [tlp | _]; atom(Term); Type = pp)),	
			( Type = np:Feat, Feat \== 'thr' -> %!!! excluded there:np
				Rest = [nd(M,  TT1, [(Term, e) | Args], TF )], % what if Term is complex?
				add_new_elements_in_the_end([TT2, (Term,e)], Sig, Sig1)
			; Type = np:thr -> % for there:np
				Rest = [],
				Sig1 = Sig	
			; TT2 = (_Term, e) ->
				Rest = [],
				add_new_elements_in_the_end([TT2], Sig, Sig1)
			; Type = pp, %maybe introduce a constant in Sig?
			  Rest = [],
			  Sig1 = Sig
			).
% const(B), not necesary. B is never unbound var, it is typed later, accepts only atoms
	
r(push_arg, equi:non, _, 
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
r(type_drop, equi:non, _,
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
% Monotone rules when arguments are in ISA relation
% Non-branching rule
r(up_mon_args,  impl:non,  _,
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
			  %tt_mon_up(G), Y = B; 
			  %tt_mon_up(H), Y = A;
			  match_ttTerms(A, B), Y = A 
			),
			\+proper_tt_isa(H, G), % makes rule more specific
			A = (_, Type1),
			B = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type), 
			( isa(A, B); match_ttTerms(A, B) ), !.

r(dw_mon_args,  impl:non,  _,
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
			\+proper_tt_isa(H, G), % makes rule more specific
			A = (_, Type1),
			B = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type), 
			( isa(A, B); match_ttTerms(A, B) ), !.


%%%%%%%%%%%%%%%%%%%%%%
% Monotone rules when Functors are the same
% Non-branching rule


r(up_mon_fun_some,  impl:new,  (_, Cids),
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
			member(Lemma, ['a', 'several', 'many', 'most', 'a_few', 'both', 's']), % "the" is not ok since we claim about N, the&the_c rules do this for 'the'
			match_ttTerms(X, Y),
			%tt_mon((Some @ X, TyX), _Up2),  %not necessary since lemma is set
			%tt_mon((Some @ Y, TyY), _Up1),  %not necessary since lemma is set
			A = (_, Type1),
			B = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			genFreshArgs(Type, ArgList, Sig, Sig1, Cids), !.


r(up_mon_fun,  impl:new,  (_, Cids),
		br([nd([], (G @ A, _), Args, true), 
			nd([], (H @ B, _), Args, false) ], 
		  Sig) 
		===> 
		br([nd([], A, ArgList, true), 
			nd([], B, ArgList, false)], 
		  Sig1) )
:-
			match_ttTerms(G, H),
			tt_mon_up(G), 
			tt_mon_up(H),
		    %%tt_mon(G, up), 
			%%tt_mon(H, up),
			%\+tt_mon(G, dw), 
			%\+tt_mon(H, dw),
			\+no_isa_rel_const_ttTerms(A, B), %!!! added recently avoids introduction of fresh constants
			A = (_, Type1),
			B = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			genFreshArgs(Type, ArgList, Sig, Sig1, Cids), !.  % these arguments can be ignored for gamma rules?


r(dw_mon_fun,  impl:new,  (_, Cids),
		br([nd([], (G @ A, _), Args, true), 
			nd([], (H @ B, _), Args, false) ], 
		  Sig) 
		===> 
		br([nd([], A, ArgList, false), 
			nd([], B, ArgList, true)], 
		  Sig1) )
:-
			match_ttTerms(G, H),
			tt_mon(G, dw), 
			tt_mon(H, dw),	
			\+no_isa_rel_const_ttTerms(A, B), %!!! added recently avoids introduction of fresh constants	
			A = (_, Type1),
			B = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			genFreshArgs(Type, ArgList, Sig, Sig1, Cids), !.


%%%%%%%%%%%%%%%%%%%%%%
% Ordinary branching monotone rules

r(up_mon,  impl:new,  (_, Cids),
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
			\+proper_tt_isa(H, G), % makes rule more specific
			\+no_isa_rel_const_ttTerms(A, B), %!!! avoids unnecsaary branching
			G = (_, Type_G),
			H = (_, Type_H),
			sub_type(Type_G, Type_Fun),
			sub_type(Type_H, Type_Fun),
			A = (_, Type1),
			B = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			genFreshArgs(Type, ArgList, Sig, Sig1, Cids), !.


r(dw_mon,  impl:new,  (_, Cids),
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
			\+proper_tt_isa(H, G), % makes rule more specific
			\+no_isa_rel_const_ttTerms(A, B), %!!! avoids unnecsaary branching
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

r(tr_a,	 impl:new,  (_, Cids),
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


r(fl_a,	 gamma:non,  (Args, _), %old
		br([nd( M, ( ( (tlp(_,Lemma,_,_,_),_) @ TT1, _ ) @ TT2, _ ),  % inro of M due to sick-4650
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
			member(Lemma, ['a', 's', 'a_few', 'another', 'the']), % the is not done by the-rule
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

% a A B : F and  A:c : T  ---> B:c : F % fracas-107
r(fl_a_c,	 impl:non, ([C], _), %old   This is not a gamma rule but shoul rule out applocation of gamma rule, we need C as info
		br([ nd(M, ( ( (tlp(_,Lemma,_,_,_), n:_~>(np:_~>s:_)~>s:_) @ TT1, _ ) @ TT2, _ ),    [],    false ),
			 nd(_, TT,    [C],    true ) %non_empty modlist
		   ], 
		  Sig) 
		===>
		br([nd(M, Other_TT, [C], false) ], Sig) )
:-
			member(Lemma, ['a', 'a_few']), %not 's' could be 'the' but it is done by the-rule
			%member(Lemma, ['a']), %more strict 
			TT1 = (_, Type1),
			TT2 = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			( 	match_ttTerms(TT, TT1), 
				Other_TT = TT2
			  ; match_ttTerms(TT, TT2),
				Other_TT = TT1	
			), !.


		

% EVERY A B : T, gamma rule
r(tr_every,	 gamma:non,  (Args, _), %old
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
			member(Every, [every, both]),
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
r(tr_every_c,	 impl:non,  ([C], _), %old This is not a gamma rule
		br([ nd(M, ( ( (tlp(_,'every',_,_,_), n:_~>(np:_~>s:_)~>s:_) @ TT1, _ ) @ TT2, _ ),    [],    true ),
			 nd(M1, TT,    [C],    TF ) % if C_e than allow
		   ], 
		  Sig) 
		===>
		br([nd(M2, Other_TT, [C], TF) ], Sig) )
:-         %!!! if C_e than allow  Other_TT, [C_np], too Fracas-103 
			%member(Every, [every]), %not "both"
			TT1 = (_, Type1),
			TT2 = (_, Type2),
			sub_type(Type1, Type),
			sub_type(Type2, Type),
			( 	match_ttTerms(TT, TT1), 
				Other_TT = TT2,
				M1 = [], M2 = M,
				TF = true
			  ; match_ttTerms(TT, TT2),
				Other_TT = TT1,
				match_list_ttTerms(M1, M), M2 = [], 
				TF = false 
			), !.



% every false
r(fl_every,	 impl:new,  (_, Cids),
		br([nd( M, ( ( (tlp(_,every,_,_,_),_) @ TT1, _ ) @ TT2, _ ), 
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
r(tr_no,  gamma:non,  (Args, _),
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


r(tr_no_c,	 impl:non,  ([C], _), %old this is not a gamma rule
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
			( 	match_ttTerms(TT, TT1),
				M = M2, M1 = [],
				Other_TT = TT2
			  ; match_ttTerms(TT, TT2),
				match_list_ttTerms(M, M1), M2 = [],
				Other_TT = TT1
			), !.


% no false
r(fl_no,  impl:new,  (_, Cids),
		br([nd(M, ( ( (tlp(_,no,_,_,_),_) @ TT1, _ ) @ TT2, _ ), 
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
r(be_a_obj,  equi:non,  _,   % obj_be
		br([nd( M, ( ( (TLP, _TLP_ty) @ TT_N, _Ty ) @ (abst((X,XType), (Is_X_C,_)), np:_~>s:_), s:_ ),
				[], TF )],
		  Sig)	 	
		===>
		br([nd( M, TT_N,
				[Arg], TF )],
		  Sig) )
:-
			TLP = tlp(_,Lem,_,_,_),
			member(Lem, ['a', 's']), %!!! the?
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

r(a_subj_be,  equi:non,  _,  % there is no need for it, never used % it is duplicate of be_obj
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
			member(Lem, ['a']),  %!!! the? s?
			( TT_NP = (Term, np:F1) -> 
				F1 \== thr, F1 \== prp,
				Arg = (Term, e)
			  ; Arg = TT_NP
			), %writeln('a_subj_be used!!!'),
			!. 

/*
r(be_obj,  equi:non,  _,  
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

r(be_pp,  equi:non,  _, 
		br([nd( Mods, ( (TLP_Be,pp~>np:_~>s:_) @ (TT_PP @ TT_C, pp), np:_~>s:_ ),
				Args, TF )], % singleton e-type!!!
		  Sig)	 	
		===>
		br([nd( Mods, TT_PP, % not necessary, np~>pp can do the job, or put both
				[TT_Ent | Args], TF )],
				%!!!  M : (TLP_PP, np:_~>pp) @ TT_C : Args? 	
		  Sig) )
:-
			TLP_Be = tlp(_,'be',_,_,_),
			TT_PP = (tlp(_,_,'IN',_,_), np:_~>pp),
			tt_constant_to_tt_entity(TT_C, TT_Ent).
			 
			 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% rule for the A B when there is a constant of A 
r(the_c,  impl:non,  _, 
		br([nd( M, ( ( (tlp(_,'the',_,_,_),_) @ TT_N, _) @ TT_VP, s:_ ),	[], 	TF ),
			nd( _, (Noun, n:F1), 	[(Term, e)], 	true )   ], % mod is allowed
		  Sig)	 	
		===>
		br([nd( M, TT_VP,	[(Term, e)], 	TF )], %added memory
		  Sig) )
:-
			match_ttTerms(TT_N, (Noun, n:F1)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% rule for the A B when there is NO constant of A
% considers mod list
r(the,  impl:new,  (_, Cids), 
		br([nd( M, ( ( (tlp(Tk,'the',POS,F1,F2),Type_The) @ TT_N, _) @ TT_VP, s:_ ),	[], 	true )],	  
		  Sig)	 	
		===>
		br([nd( M, TT_VP,	Args, 	true ) | NodeList],		
		  Sig1) )
:-
			TT_N = (_, Type),
			%( TF = false -> M =[]; true ), % added to deal with memory
			_The = (tlp(Tk,'the',POS,F1,F2),Type_The),
			SrcNode = nd( [], TT_N,	Args, true), 
			noun_node_to_isa_node_list(SrcNode, NodeList),
			genFreshArgs(Type, Args, Sig, Sig1, Cids).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% conjunction rules
r(arg_dist,	equi:non,  _, %maybe impl?  this rule needed by sick-7889
		br([nd( M, ( ( ( (tlp(Tk,Conj,Pos,F1,F2), Ty~>Ty~>Ty) @ TT1, _ ) @ TT2, _ ) @ TTArg, Type), 
				Args, TF )], 
		  Sig) 
		===> 
		br([nd(	M, (((tlp(Tk,Conj,Pos,F1,F2), Ty2~>Ty2~>Ty2) @ (TT1 @ TTArg, Type), Type~>Type) @ (TT2 @ TTArg, Type), Type), 
				Args, TF )], 
		  Sig) )
:-
			TTArg = (_, _ArgType). % check typing!!!
			%TT1 = (_, _Ty1~>Ty2).

% distribute function only over entity arguments, sleep (and John Sam) -> (sleep John) and (sleep Sam)
r(fun_dist,	equi:non,  _, %!!! equi
		br([nd( M, (Fun @ (((tlp(Tk,Conj,'CC',F1,F2), Ty~>Ty~>Ty) @ Arg1, _Ty1) @ Arg2, _Ty2), Type), 
				Args, TF )], 
		  Sig) 
		===> 
		br([nd(	M, (((tlp(Tk,Conj,'CC',F1,F2), Type~>Type~>Type) @ (Fun @ Arg1, Type), Type~>Type) @ (Fun @ Arg2, Type), Type), 
				Args, TF )], 
		  Sig) )
:-
			nonvar(Conj),
			memberchk(Ty, [np:_, e]).
			
%but not with disjunction! every A (C or D) =/=> every A C or every A D !!!

r(fun_dist,	impl:non,  _, %impl!!! every A and B =/always/= every A and Every B,  some man sleep and eat =/= some man eat and some man sleep
		br([nd( M, (Fun @ (((tlp(Tk,Conj,'CC',F1,F2), Ty~>Ty~>Ty) @ Arg1, _Ty1) @ Arg2, _Ty2), Type), 
				Args, TF )], 
		  Sig) 
		===> 
		br([nd(	M, (((tlp(Tk,Conj,'CC',F1,F2), Type~>Type~>Type) @ (Fun @ Arg1, Type), Type~>Type) @ (Fun @ Arg2, Type), Type), 
				Args, TF )], 
		  Sig) )
:-
			nonvar(Conj),
			Fun \= ((tlp(_,'a',_,_,_),_) @ _B, _),
			\+memberchk(Ty, [np:_, e]).
			


r(abst_dist, 	equi:non,  _, %maybe impl?
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

% pp complement as modifier: kick@(near@John) ~> (near@John)@kick, sick-1469,44 needs it
r(vp_pp, 	impl:non,  _,
		br([nd( M, (VP @ (PP, pp), Type), %!!! before was only np:_~>s:_
				Args, TF )], 
		  Sig) 
		===> 
		br([nd(	M, (Prep_NP @ VP1, Type), 
                Args, TF )],
		  Sig) )
:-
		set_type_for_tt((PP, pp), Type~>Type, Prep_NP),
		set_type_for_tt(VP, Type, VP1).	% change s:pss to s:dcl?	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Attaching VP modifier to the argument
% mainly introduced to fix parse errors
% along@c3@(ride@c1)@c2 vs along@c3@c1, sick-200
r(vpMod_to_argMod, 	impl:non, _,  % VpMod_ArgMod rule for false sign, branching?
		br([nd( _M1, ( ((PP,np:_~>_)@NP, (np:_~>Ty1)~>np:_~>Ty2) @ (tlp(_,_,_,_,_),_), _), 
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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Verb in passive % IN necessary?
r(vp_pass1, 	impl:non,  _,
		br([nd( M, (Verb_Pass @ ((tlp(_,'by','IN',_,_), np:_~>pp) @ NP, pp), np:_~>s:_), % sick-1745 s:dcl "is beng played"
				Args, TF )], 
		  Sig) 
		===> 
		br([nd(	M, Verb, New_Args, TF ) | Rest],
		  Sig) )
:-
		append(Args, [NP], New_Args),
		( NP = (Tr,np:_) ->
			append(Args, [(Tr,e)], New_Args1),
		  	Rest = [nd(M, Verb, New_Args1, TF)]
		  ; Rest = []
		),
		Verb_Pass = (_, pp~>Type),
		set_type_for_tt(Verb_Pass, np:_~>Type, Verb).	% change s:pss to s:dcl?		

% IN necessary?
r(vp_pass2, 	impl:non,  _,
		br([nd( M, (((tlp(_,'by','IN',_,_), np:_~>(np:_~>s:_)~>(np:_~>s:_)) @ NP, _) @ Verb_Pass, np:_~>s:_), % sick-1745 s:dcl "is beng played"
				Args, TF )], 
		  Sig) 
		===> 
		br([nd(	M, Verb, New_Args, TF ) | Rest],
		  Sig) )
:-
		append(Args, [NP], New_Args),
		( NP = (Tr,np:_) ->
			append(Args, [(Tr,e)], New_Args1),
		  	Rest = [nd(M, Verb, New_Args1, TF)]
		  ; Rest = []
		),
		Verb_Pass = (_, Type_Verb_Pass),
		set_type_for_tt(Verb_Pass, np:_~>Type_Verb_Pass, Verb).	% change s:pss to s:dcl?	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Rule for factive attitude verbs
r(fact_v_s_tr,	impl:non, _, %fracas-334
		br( [nd( _M, ( (tlp(_,FactV,_,_,_),s:_~>np:_~>s:_) @ Sen, np:_~>s:_),
				 _Args, true )], 
		  Sig)
		===>
		br( [nd( [], Sen , [], true)], 
		  Sig) )
:-
		factive(FactV).

r(fact_v_tr,	impl:non, _,
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

r(fact_v_fl,	impl:non, _,
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
r(ho_verb,	impl:non, _,
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
r(it_is_tr_fl,  equi:non,  _,
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
r(cardinal_mod, 	impl:non, _, 
		br([nd( M, ((((tlp(_,Lm_RB,_,_,_), (n:_~>(np:_~>s:_)~>s:_)~>n:_~>(np:_~>s:_)~>s:_) @ TT_CD, _) @ TTn, _) @ TTvp, s:_),  Args, true )],
		  Sig)
		===>
		br([nd( M, ((TT_CD @ TTn, (np:_~>s:_)~>s:_) @ TTvp, s:_), Args, true )],
		  Sig) ) 
:-
			member(Lm_RB, ['exactly', 'just']),
			!.

	







	
