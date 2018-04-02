

gen_quant_tt(TTexp, GQTTs) :-
	ttExp_to_ttTerm(TTexp, TT),
	%print_ttTerm_to_gqtTerms([TT]),
	ttTerm_to_subTerms(TT, NewTT, Vars, SubTerms),
	findall(NormGQTT, 
		( gq_join_terms(NewTT, Vars, [], SubTerms, GQTT), 
		  norm_tt(GQTT, NormGQTT)), 
		GQTTs).
	%once(gq_join_terms(NewTT, Vars, [], SubTerms, GQTT)), norm_tt(GQTT, NormGQTT), GQTTs = [NormGQTT].

once_gen_quant_tt(TTexp, NormGQTT) :-
	ttExp_to_ttTerm(TTexp, TT),
	ttTerm_to_subTerms(TT, NewTT, Vars, SubTerms),
	gq_join_terms(NewTT, Vars, [], SubTerms, GQTT) -> % first GQTT is NPs rised in narrow scopes
		%norm_tt(GQTT, NormGQTT),  
		norm_tt(GQTT, NormGQTT1),  np_const_to_e_const(NormGQTT1, NormGQTT)
	; writeln('Error in gen_quant_tt'), fail.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% For printing and testiong purposes
print_ttTerm_to_gqtTerms(List) :-
	(exists_directory('latex') -> true; make_directory('latex')),
	open('latex/gqttTerms.tex', write, S, [encoding(utf8), close_on_abort(true)]),	
	%asserta(latex_file_stream(S)),
	latex_ttTerm_preambule(S),
	write(S, '\\begin{document}\n'),
	maplist(print_subTerms_of_ttTerm(S), List),
	write(S, '\\end{document}'),
	close(S).

print_subTerms_of_ttTerm(S, TTexp) :-
	ttExp_to_ttTerm(TTexp, TT),
	latex_ttTerm_print_tree(S, 6, TT),
	ttTerm_to_subTerms(TT, NewTT, Vars, SubTerms),
	findall(SubTTterm,  member(subterm(SubTTterm,_,_), SubTerms), List_SubTerm),
	maplist(latex_ttTerm_print_tree(S, 6), List_SubTerm),
	findall(NormGQTT, (gq_join_terms(NewTT, Vars, [], SubTerms, GQTT), norm_tt(GQTT, NormGQTT)), GQTTs),
	maplist(latex_ttTerm_print_tree(S, 6), GQTTs).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ttTerm to independent subTerms
/*ttTerm_to_independent_subTerms(TT, TT_0, Ind_TTs) :-
	TT = (((Conj,X~>X~>X) @ TT1, _) @ TT2, _),
	TT_0 = (((Conj,X~>X~>X) @ TT1, _) @ TT2, _),
	Ind_TTs = [TT1, TT2]. 

ttTerm_to_independent_subTerms(TT, Ind_TTs) :-
*/
	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ttTerm_to_sub_Terms(TT, NewTT, Vars, SubTerms)
% takes ttTerm TT and returns its simplified version NewTT,
% where NP and S-category terms are substituted by variables;
% Vars contains variables immediatly existing in NewTT;
% SubTerms is a list of those subterms from TT, 
% which are substituted by variables  
ttTerm_to_subTerms(TT, TT, [], []) :-
	TT = (X,_),
	( var(X)
	; atom(X) %!!! added for term_atoms created by alignment procedure
	),
	!.

ttTerm_to_subTerms(TT, TT, [], []) :-
	TT = (tlp(_,_,_,_,_), _), !.

ttTerm_to_subTerms((Exp, T), (X,T), [(X,T)], Terms) :-
	( T=np:_, \+conj_of_const_NNPs((Exp, T)), \+np_mod_app_np((Exp, T)); 
	  T=s:_; 
	  T=_~>s:_
	), !, 
	ttTerm_to_subTerms((Exp,nil), (NewExp,nil), SubVars, SubTerms), 
	Terms = [subterm((NewExp,T), SubVars, X) | SubTerms].

ttTerm_to_subTerms( (((Conj,X~>X~>X) @ (Tr1,Type1), Ty1) @ (Tr2,Type2), Ty2), NewTT, Vars, Terms) :-
	nonvar(Conj),	
	Conj = tlp(_,Lm,POS,_,_), 
	once(( member(Lm, ['or', 'and']); member(POS, ['DT', 'CC'])  )), %cahnegs due to %sick-272 a:DT,n~>n~>n
	( (Type1, Type2) = (np:_, np:_) -> 
		(NewTy1, NewTy2) = (nil, nil)
	  ; (NewTy1, NewTy2) = (Type1, Type2)
	),  	
	!, ttTerm_to_subTerms((Tr1, NewTy1), (NewTr1,_), Vars1, Terms1),
	ttTerm_to_subTerms((Tr2, NewTy2), (NewTr2,_), Vars2, Terms2),
	append(Vars1, Vars2, Vars),
	append(Terms1, Terms2, Terms),
	NewTT = (((Conj,X~>X~>X) @ (NewTr1,Type1), Ty1) @ (NewTr2,Type2), Ty2). 

ttTerm_to_subTerms((TT1@TT2, Type), (NewTT1@NewTT2, Type), Vars, Terms) :-
	!, ttTerm_to_subTerms(TT1, NewTT1, Vars1, Terms1),
	ttTerm_to_subTerms(TT2, NewTT2, Vars2, Terms2),
	append(Vars1, Vars2, Vars),
	append(Terms1, Terms2, Terms).
	 
ttTerm_to_subTerms((abst(TTx,TT1), Type), NewTT, Vars, Terms) :-
	!, NewTT = (abst(TTx, NewTT1), Type),
	ttTerm_to_subTerms(TT1, NewTT1, Vars, Terms).

ttTerm_to_subTerms((TT,Type), (NewTT,Type), Vars, Terms) :-
	!, ttTerm_to_subTerms(TT, NewTT, Vars, Terms).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% member_subterm(X, SubTerms, SubTerm, RestSubterms)
% SubTerm is the first element of SubTerms that has a label identical to X;
% RestSubTerms = Subterms - SubTerm  
member_subterm(X, [subterm(TT,Vars,Lab) | Rest], subterm(TT,Vars,X), Rest) :-
	X == Lab, !.

member_subterm(X, [Head | Rest], SubTerm, [Head | SubTerms]) :-
	member_subterm(X, Rest, SubTerm, SubTerms). 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% gq_join_terms(TT, TTvars, TTscope, SubTerms, GQTT)
% Substitutes TTvars in TT for SubTerms TTvars are pointing at; 
% Substitution is done with type-rising of NP
% Choice points: which NP siblings to rise first, and rise NP in wide or narrow scope 
gq_join_terms(TT, Vars, Scope, SubTerms, GQTT) :-
	TT = (_, np:F1), !,
	TTverb = (_, np:F1 ~> s:F2),
	TTsen = (TTverb @ TT, s:F2),
	gq_join_terms_sen(TTsen, Vars, Scope, SubTerms, GQTT1),
	GQTT = (abst(TTverb, GQTT1), (np:F1 ~> s:F2) ~> s:F2).	

% TT is a variable with sentential value
gq_join_terms(TT, [TTx], Scope, SubTerms, GQTT) :-
	TT == TTx, !,
	TTx = (X, _),
	member_subterm(X, SubTerms, subterm(TT, Vars, X), NewSubTerms),
	gq_join_terms_sen(TT, Vars, Scope, NewSubTerms, GQTT).

gq_join_terms(TT, Vars, Scope, SubTerms, GQTT) :-
	gq_join_terms_sen(TT, Vars, Scope, SubTerms, GQTT).	




% TT is free from variables
gq_join_terms_sen(TT, [], _, _, TT) :-
	!. 

% TT has a variable with a category NP
gq_join_terms_sen(TT, Vars, Scope, SubTerms, GQTT) :-
	member((_,np:_), Vars), !, 
	TT = (_, Ty),
	final_value_of_type(Ty, s:F1),
	choose(Vars, (X,np:F2), RestVars), % makes choice point in choosing NPs 
	member_subterm(X, SubTerms, subterm(TTnp,Vars1,X), RestSubTerms),
	%type_rise_np(X, s:F1, SubTerms, RestSubTerms, Vars, TR_TTnp),
	set_type_for_tt(TTnp, (np:F2~>s:F1)~>s:F1, TR_TTnp),
	feed_ttTerm_with_ttArgs(TT, FedTT, Args), 
	GQTT1 = (TR_TTnp @ (abst((X,np:F2), FedTT), np:F2~>s:F1), s:F1),
	abst_ttTerm_with_ttArgs(GQTT1, GQTT2, Args),
	append(RestVars, Vars1, NewVars),
	append(NewVars, Scope, NewScope),
	gq_join_terms(GQTT2, NewVars, NewScope, RestSubTerms, GQTT). 

% TT has no variable with NP category
gq_join_terms_sen(TT, Vars, Scope, SubTerms, GQTT) :-
	TT = (_, Ty),
	final_value_of_type(Ty, s:_),	
	%\+(member((_,np:_), Vars),
	choose(Vars, (X,S), RestVars),
	(S = s:_; S = _~>s:_),
	%TTx = (X, S), 	
	member_subterm(X, SubTerms, subterm((Exp,S), Vars1, X), RestSubTerms),
	true_remove(X, Scope, Scope1),
	append(Scope1, Vars1, NewScope),
	append(RestVars, Vars1, NewVars), !,
	(\+member((_,np:_), Vars1) -> % if there is no NP in Vars1
		X = Exp,
		(true_member((X,S), Scope) -> % if SubTerm is under quantifier's scope 
			gq_join_terms_sen(TT, NewVars, NewScope, RestSubTerms, GQTT) % inside scope
		;	gq_join_terms_sen(TT, NewVars, Scope1, RestSubTerms, GQTT) ) % outside scope
	% there is NP in Vars1 
	; ( gq_join_terms_sen((Exp,S), Vars1, [], RestSubTerms, (X,_)), % NP rise in narrow scope
	    gq_join_terms_sen(TT, RestVars, Scope1, RestSubTerms, GQTT)
	  ; true_member((X,S), Scope), % NP rise in wides scope, required to be inside scope
		X = Exp,
		gq_join_terms_sen(TT, NewVars, NewScope, RestSubTerms, GQTT) ) ).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% combines subTerms
/*combine_subTerms(Init, Vars, SubTerms, GQTTs) :-
	maplist(type_raise_subterm, SubTerms, TR_subTerms).


% constant NP stays unchanged
%type_raise_of_ttTerm( (tlp(Tk,Lm,POS,F1,F2), np:F), (tlp(Tk,Lm,POS,F1,F2), np:F) ).

% Var ---> Var
type_raise_of_ttTerm( (Var,Type), (Var,Type) ) :-
	var(Var),
	!.

% Quant + Noun ---> Raised_Quant + Noun
type_raise_of_ttTerm( ((Quant_TLP, n:_~>np:_) @ TT_N, np:_), TR_TT ) :-
	Quant_TLP =.. [tlp | _],
	!,
	TR_TT = ((Quant_TLP, n:_~>(np:F1~>s:F2_)~>s:F3) @ TT_N, (np:F1~>s:F2_)~>s:F3). 

% if NP is constant than everything stays as it is
type_raise_of_ttTerm(TT, TT).

% intr_verb + NP ---> Raised_NP + intr_verb
type_raise_of_ttTerm( ((VP_TLP, np:F1~>s:F2) @ (NP_var, np:_), s:_), TR_TT) :-
	VP_TLP =.. [tlp | _],
	var(NP_var),
	TR_TT = ((NP_var, (np:_~>s:_)~>s:F3) @ (VP_TLP, np:F1~>s:F2), s:F3). 

% Var_VP + Var_NP ---> Tr_Var_NP + Var_VP  |  Tr_Var_VP + Tr_Var_NP 
type_raise_of_ttTerm( ((VP_var, np:F1~>s:F2) @ (NP_var, np:_), s:_), TR_TT) :-
	var(VP_var),
	var(NP_var).
	*/

	



	
	
