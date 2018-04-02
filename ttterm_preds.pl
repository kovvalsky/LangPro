%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TTterm to expressive, informative atom
ttTerm_to_informative_tt((TLP,Type), (Tr,Ty)) :-
	nonvar(TLP),
	TLP =  tlp(_,Lemma,POS,_,_),
	!,
	( POS = 'CD', Lemma \= 'null' -> 
		%Tr = POS
		Tr = Lemma  
	;	Tr = Lemma
	),
	general_cat(Type, Ty).

ttTerm_to_informative_tt( ((TLP1,_)@(TLP2,_), Type),  (Tr, Ty) ) :-
	nonvar(TLP1),
	nonvar(TLP2),
	TLP1 = tlp(_,Lm1,_Pos1,_,_), 
	TLP2 = tlp(_,Lm2,_Pos2,_,_),
	atomic_list_concat([Lm1, Lm2], ' ', Tr),
	general_cat(Type, Ty).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TTterm to Natural Text, order preserved
/*ttTerm_to_text(TT, Text) :- 
	!.
*/	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checks if TTterm = Adjunct @ Head with Head of type Type
adjuncted_ttTerm((Term, _Type)) :-
	nonvar(Term),
	Term = (_Adj, Ty1~>Ty2) @ _H,
	cat_eq(Ty1, Ty2),
	!.

adjuncted_ttTerm((Term, n:_)) :-
	nonvar(Term),
	Term = (_H, pp~>n:_) @ _PP,
	!.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% takes a node with (Term, n) : Args and creates a list of nodes
% [ nd([],Noun,Args,TF) ... ] where Nouns are such that isa_wn(Term, Noun) 
noun_node_to_isa_node_list(SrcNode, [SrcNode | Nodes]) :-
	SrcNode = nd([], TTn, Args, TF),
	TTn = (tlp(_,Lm,'NN',_,_), n:_),
	!,
	(bagof(Node, 
		 Lm^( %isa_wn(Lm, Lemma),
			  isa(Lm, Lemma),	
			  Node = nd([], (tlp(Lemma,Lemma,'NN',_,_), n:_), Args, TF)	
			),
			Nodes)	-> true
	; Nodes = []
	).

noun_node_to_isa_node_list(SrcNode, [SrcNode]) :-
	SrcNode = nd([], (_, n:_), _Args, _TF).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% takes a node with non-empty modList and returns a list of nodes with elements of modList applied to a head
% ModList: TTterm: Args: TF ---> [M1: TTterm: Args: TF, ..., Mn: LLF: Args: TF]
modList_node_to_modNode_list(nd([], _TT, _Args, _TF),  []) :-
	!.

modList_node_to_modNode_list( nd([Mod | Rest], TT, Args, TF), NewNdoes ) :-
	findall(NewNode,  mod_node_to_node(Mod, TT, Args, TF, NewNode), NewNodes1),
	modList_node_to_modNode_list( nd(Rest, TT, Args, TF),  NewNodes2 ),
	append(NewNodes1, NewNodes2, NewNdoes).

/*modList_node_to_modNode_list( nd([M|Rest], TT, Args, TF),  [H|List] ) :-
	M = (_, Mty1~>Mty2),
	TT = (_, Type),
	cat_eq(Mty1, Type),
	cat_eq(Mty2, Type), !,
	H = nd( [], (M@TT, Mty2), Args, TF ),
	modList_node_to_modNode_list( nd(Rest, TT, Args, TF),  List ). 

modList_node_to_modNode_list( nd([M|Rest], TT_N, [Arg], TF),  NodeList ) :-
	TT_N = (_, n:_), 
	mod_to_entity_property(M, Prop),
	tt_constant_to_tt_entity(Arg, C),
	H = nd( [], Prop, [C], TF ), !,
	modList_node_to_modNode_list( nd(Rest, TT_N, [Arg], TF),  RestNodeList ). 

modList_node_to_modNode_list( nd([M|Rest], TT_N, [Arg], TF),  [H|List] ) :-
	mod_to_n_modifier(M, N_Mod), !,
	TT_N = (_, n:_), 
	H = nd( [], (N_Mod@TT_N, n:_), [Arg], TF ), !,
	modList_node_to_modNode_list( nd(Rest, TT_N, [Arg], TF),  List ).

modList_node_to_modNode_list( nd([_|Rest], TT, Args, TF),  List ) :-
	modList_node_to_modNode_list( nd(Rest, TT, Args, TF),  List ).*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% takes mod and a node and generates newNodes by attributing Mod to a node
mod_node_to_node(Mod, TT, Args, TF, NewNode) :-
	Mod = (_, Mty1~>Mty2),
	TT = (_, Type),
	cat_eq(Mty1, Type),
	cat_eq(Mty2, Type),
	NewNode = nd( [], (Mod@TT, Mty2), Args, TF ).

mod_node_to_node(Mod, TT_N, [Arg], TF, NewNode) :-
	TT_N = (_, n:_), 
	mod_to_entity_property(Mod, Prop),
	tt_constant_to_tt_entity(Arg, C), % not necessary
	NewNode = nd( [], Prop, [C], TF ).

mod_node_to_node(Mod, TT_N, [Arg], TF, NewNode) :-
	mod_to_n_modifier(Mod, N_Mod),
	TT_N = (_, n:_), 
	NewNode = nd( [], (N_Mod@TT_N, n:_), [Arg], TF ).

% takes modifier and attaches to VP
mod_node_to_node(Mod, TT_VP, Args, TF, NewNode) :-
	Mod = (_, (np:_~>s:_)~>np:_~>s:_),
	TT_VP = (_, Type),
	final_value_of_type(Type, s:_),
	set_type_for_tt(Mod, Type~>Type, NewMod),
	NewNode = nd( [], (NewMod@TT_VP, Type), Args, TF ).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%
% Converts Modifier into e->t Property
mod_to_entity_property(Mod, Prop) :-
	Mod = ((tlp(_,Lm,'IN',_,F2), np:_~>_) @ TT_NP, _),
	\+atom_chars(F2, [_,_,'D','A','T']),
	tt_constant_to_tt_entity(TT_NP, C),
	%report(Mod, 'this modifier is converted in property'),
	Prop = ((Lm,e~>e~>t)@C, e~>t).

% Converts Modifier into noun modifier
mod_to_n_modifier(Mod, N_Mod) :-
	Mod = ((tlp(Tk,Lm,'IN',F1,F2), np:F0~>Ty1~>Ty2) @ TT_NP, _),
	cat_eq(Ty1, Ty2),
	\+atom_chars(F2, [_,_,'D','A','T']),
	%report(Mod, 'this modifier is converted in noun modifier'),
	N_Mod = ((tlp(Tk,Lm,'IN',F1,F2), np:F0~>n:F3~>n:F4) @ TT_NP, n:F3~>n:F4). 	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checks modifier and attributes it to args
modList_be_args_to_nodeList( [], _Args, [] ) :-
	!.

modList_be_args_to_nodeList( [M | Mods], [Arg1, Arg2], Nodes ) :-
	mod_to_entity_property(M, Prop), !,
	Nodes = [ nd([], Prop, [Arg1], true), nd([], Prop, [Arg2], true) | Rest],
	modList_be_args_to_nodeList( Mods, [Arg1, Arg2], Rest).

modList_be_args_to_nodeList( [_ | Mods], [Arg1, Arg2], Nodes ) :- 
	modList_be_args_to_nodeList( Mods, [Arg1, Arg2], Nodes). 
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Unpacks ttTerm from the sequence of type changing rules
unpack_ttTerm((Term, Ty), TTterm) :-
	nonvar(Term),
	( Term = (_, _) ->
		unpack_ttTerm(Term, TTterm)
	;	TTterm = (Term, Ty)
	). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Matching of ttTerms in the tableau
% necessary to match ttTerms with equivalent types

match_ttTerms(X, Y) :-  % variants, only matching Abst(X,X@const) = Abst(Y,const@Y) causes error
	X =@= Y,
	X = Y, !.

match_ttTerms((TTexp1, Type1, _), (TTexp2, Type2, _)) :- % are we using it?
	%cat_eq(Type1, Type2), %ignoring features
	luc(Type1, Type2, _), % sick-2722
	match_ttExp(TTexp1, TTexp2), !.

match_ttTerms((TTexp1, Type1), (TTexp2, Type2)) :- % ignoring types?
	%cat_eq(Type1, Type2), %ignoring features
	luc(Type1, Type2, _), % sick-2722
	match_ttExp(TTexp1, TTexp2), !.
	
% Matching of ttExpressions in the tableau
match_ttExp(X, Y) :-  % variants, only matching Abst(X,X@const) = Abst(Y,const@Y) causes error
	X =@= Y,
	X = Y, !.

match_ttExp(FunTT1 @ ArgTT1, FunTT2 @ ArgTT2) :-
	match_ttTerms(FunTT1, FunTT2),
	match_ttTerms(ArgTT1, ArgTT2).
	
match_ttExp(abst(_,TT1), abst(_,TT2)) :-
	match_ttTerms(TT1, TT2).

match_ttExp((TTexp1, Type1), (TTexp2, Type2)) :-
	%cat_eq(Type1, Type2), %ignoring features
	luc(Type1, Type2, _), % sick-2722
	match_ttExp(TTexp1, TTexp2).

match_ttExp(TT1, TT2) :- % ignoring everything except lemmas
	TT1 = tlp(_Tk1, Lemma1, _Pos1, _F11, _F12),
	TT2 = tlp(_Tk2, Lemma2, _Pos2, _F21, _F22),
	( Lemma1 = Lemma2
	; word_synonyms(Lemma1, Lemma2) % Slows down the mathcing process
	).

	
	 
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Matching of list of ttTerms in the tableau
match_list_ttTerms([Head1 | Rest1], [Head2 | Rest2]) :-
	match_ttTerms(Head1, Head2),
	match_list_ttTerms(Rest1, Rest2).
	
match_list_ttTerms([], []).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Matching only terms ignoring types
match_only_terms(TT1, TT2) :-
	ttTerm_to_prettyTerm(TT1, PrettyTr),
	ttTerm_to_prettyTerm(TT2, PrettyTr).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Matching only terms of list of ttTerms in the tableau
match_list_only_terms([Head1 | Rest1], [Head2 | Rest2]) :-
	match_only_terms(Head1, Head2),
	match_list_only_terms(Rest1, Rest2).
	
match_list_only_terms([], []).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 
% Print ttTerms in latex file
print_ttTerms_in_latex(List) :-
	open('latex/ttTerms.tex', write, S, [encoding(utf8), close_on_abort(true)]),	
	%asserta(latex_file_stream(S)),
	latex_ttTerm_preambule(S),
	write(S, '\\begin{document}\n'),
	maplist(latex_ttTerm_print_tree(S, 6), List),
	write(S, '\\end{document}'),
	close(S).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TTterm is a possible collocation, return a collcoation and POS
maybe_2_collocation(((TTexp1, Ty1)@(TTexp2, Ty2), _Type),  (Lemma, POS)) :-
	nonvar(TTexp1),
	nonvar(TTexp2),
	TTexp1 = tlp(_,Lm1,_Pos1,_,_), %-ing?
	TTexp2 = tlp(_,Lm2,_Pos2,_,_),
	memberchk((Ty1, Ty2, POS),  [(n:_~>n:_, n:_, 'NN'), (_, pr, 'VB')]), %!!! adverbs, adjectives?
	atomic_list_concat([Lm1, Lm2], ' ', Lemma).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Extract lexical items from a ttTerm
extract_LemPos_ttNNP_ttTerm((Term,_), Lex, Lex, NNPs, NNPs) :-
	var(Term),
	!.

extract_LemPos_ttNNP_ttTerm((TT1@TT2,Type), Old_Lex, New_Lex, Old_NNPs, New_NNPs) :-
	!,
	( maybe_2_collocation((TT1@TT2,Type), LemPos) ->
		Lex0 = [LemPos | Old_Lex]
	  ; Lex0 = Old_Lex
	),
	extract_LemPos_ttNNP_ttTerm(TT1, Lex0, Lex1, Old_NNPs, NNPs1),
	extract_LemPos_ttNNP_ttTerm(TT2, Lex1, New_Lex, NNPs1, New_NNPs).
	%append([Lex1, Lex2, Old_Lex], New_Lex),
	%append([NNPs1, NNPs2, Old_NNPs], New_NNPs).

extract_LemPos_ttNNP_ttTerm((Term,Type), Old_Lex, New_Lex, Old_NNPs, New_NNPs) :-
	Term = tlp(_,Lemma,POS,_,_), 
	!,
	New_Lex = [(Lemma,POS) | Old_Lex],
	(Type = np:F, F \= thr ->
		New_NNPs = [(Term,Type), (Lemma,e) | Old_NNPs]
	;	New_NNPs = Old_NNPs
	).

extract_LemPos_ttNNP_ttTerm((abst(_, TT),_), Old_Lex, New_Lex, Old_NNPs, New_NNPs) :-
	!,
	extract_LemPos_ttNNP_ttTerm(TT, [], Lex, [], NNPs),
	append(Lex, Old_Lex, New_Lex),
	append(NNPs, Old_NNPs, New_NNPs).
	
extract_LemPos_ttNNP_ttTerm(((Term,Type),_), Old_Lex, New_Lex, Old_NNPs, New_NNPs) :-
	!,
	extract_LemPos_ttNNP_ttTerm((Term,Type), [], Lex, [], NNPs),
	append(Lex, Old_Lex, New_Lex),
	append(NNPs, Old_NNPs, New_NNPs).

extract_LemPos_ttNNP_ttTerm(_, Lex, Lex, NNPs, NNPs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Extract lexical items from a ttTerm List
extract_lex_NNPs_ttTerms(Nodes, Lexicon, Names) :-
	extract_lex_NNPs_ttTerms(Nodes, [], Lex, [], NNPs),
	list_to_set(Lex, Lexicon),
	list_to_set(NNPs, Names).

extract_lex_NNPs_ttTerms([Head|Rest], Old_Lex, New_Lex, Old_NNPs, New_NNPs) :-
	!, 
	once( (Head = nd(_, TT, _, _);  Head = TT) ),
	extract_LemPos_ttNNP_ttTerm(TT, Old_Lex, Lex, Old_NNPs, NNPs),
	extract_lex_NNPs_ttTerms(Rest, Lex, New_Lex, NNPs, New_NNPs).
	
extract_lex_NNPs_ttTerms([], Lex, Lex, NNPs, NNPs).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Extract (const,type)s from a ttTerm
extract_const_ttTerm(TTterm, Const) :-
	extract_const_ttTerm(TTterm, [], Const).

extract_const_ttTerm((Term,_), Old_Const, New_Const) :-
	nonvar(Term),
	Term = TT1 @ TT2, !,
	extract_const_ttTerm(TT1, [], Const1),
	extract_const_ttTerm(TT2, [], Const2),
	append([Const1, Const2, Old_Const], New_Const).	

extract_const_ttTerm((Term,Type), Old_Const, New_Const) :-
	nonvar(Term),
	Term = tlp(_,Lemma,_,_,_), !,
	New_Const = [(Lemma,Type) | Old_Const].

extract_const_ttTerm((Term,_), Old_Const, New_Const) :-
	nonvar(Term),
	Term = abst(_, TT), !,
	extract_const_ttTerm(TT, [], Const),
	append(Const, Old_Const, New_Const).

extract_const_ttTerm((Term,Type), Old_Const, New_Const) :-
	atom(Term), !,
	New_Const = [(Term,Type) | Old_Const].
	
extract_const_ttTerm((Term,_), Old_Const, New_Const) :-
	nonvar(Term),
	Term = (_, _), !,
	extract_const_ttTerm(Term, [], Const),
	append(Const, Old_Const, New_Const).

extract_const_ttTerm(_, Const, Const).

	  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% feed_ttTerm_with_ttArgs(TT, newTT, ttArgs)
% takes TT term and returns newTT which is a rsult of
% feeding TT with argument list ttArgs;
% feeding order complies with ttArgs list order;
% TT have to be S-category returning functor 
feed_ttTerm_with_ttArgs((Exp, A~>B), NewTT, [TTarg | Rest]) :-
	!,
	TTarg = (_, A), %sub_type(Ty, A), !, % for some reasons
	TT = ((Exp, A~>B) @ TTarg, B),
	feed_ttTerm_with_ttArgs(TT, NewTT, Rest).

feed_ttTerm_with_ttArgs((Exp, s:F), (Exp, s:F), []).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% abst_ttTerm_with_ttArgs(TT, NewTT, ttArgs)
% NewTT is a result of abstracting TT with the list ttArgs;
% the first element of ttArgs is abstracted last
abst_ttTerm_with_ttArgs((Exp,Ty), NewTT, [(Arg,Ty1) | Rest]) :-
	!,
	NewTT = (abst((Arg,Ty1), SubTT), Ty1~>Ty),
	abst_ttTerm_with_ttArgs((Exp,Ty), SubTT, Rest).

abst_ttTerm_with_ttArgs(TT, TT, []).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ttTerms_same_type(List, Type)
% all ttTerm members of List has a type matching to Type 
ttTerms_same_type(List, Type) :-
	ttTerms_same_type(List, _, Type).

ttTerms_same_type([], Type, Type) :-
	nonvar(Type), 
	!.

ttTerms_same_type([(_,Type1) | Rest], Type2, Type) :-
	var(Type2) -> 
		ttTerms_same_type(Rest, Type1, Type2)
	; nonvar(Type1),
	  luc(Type1, Type2, Type3),	
	  ttTerms_same_type(Rest, Type3, Type).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% set type for TTterm
set_type_for_tt( (Var, Ty), Type, (Var, Type) ) :-
	var(Var), 
	Ty = np:_,  % to block type raising of variables that are possibly bind by abtracted variables
	Type = (np:_~>s:_)~>s:_,
	!, 
	fail.

set_type_for_tt( (Var, _Ty), Type, (Var, Type) ) :-
	( var(Var)
	; atom(Var) % due to atoms introduced by alignment process
	), !. 

set_type_for_tt( (TLP, _Ty), Type, (TLP, Type) ) :-
	TLP =.. [tlp|_], !.

set_type_for_tt( ((ConjTT @ TT1, Ty~>Ty) @ TT2, Ty), Type, (NewExp, Type) ) :- %!!! inserted
	ConjTT = (TLP, Ty~>Ty~>Ty),
	TLP = tlp(_,Lm,POS,_,_),
	( POS = 'CC'; member(Lm, [and, or]); POS = 'DT', report([Lm, ':', POS, ' as conjunction']) ), !, %sick-272 treats a:DT,n~>n~>n
	set_type_for_tt(TT1, Type, NewTT1),
	set_type_for_tt(TT2, Type, NewTT2),
	NewExp = ((TLP, Type~>Type~>Type) @ NewTT1, Type~>Type) @ NewTT2. 

% case for modifier: MOD @ HEAD -> change type of HEAD
set_type_for_tt( (TT_Mod @ TT_Head, _), Type, (NewExp, Type) ) :- 
	TT_Mod = (_, Type1 ~> Type2),
	cat_eq(Type1, Type2), %!, may backtrack if TT_Head is np variable that needs to be type raised
	set_type_for_tt(TT_Head, Type, New_TT_Head),
	set_type_for_tt(TT_Mod, Type~>Type, New_TT_Mod),
	!, 
	NewExp = New_TT_Mod @ New_TT_Head.
	 
set_type_for_tt( (A @ B, _Ty), Type, (TempTT @ B, Type) ) :-
	A = (_, TyB ~> _),
	set_type_for_tt(A, TyB~>Type, TempTT), !.

set_type_for_tt( (TT, _Ty), Type, (TT, Type) ) :-
	TT = (_, _).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% applies tt function to list of tt arguments
apply_ttFun_to_ttArgs([], TTFun, TTFun).

apply_ttFun_to_ttArgs([(H,Ty1) | TTRest], (Fun,Ty1~>Ty2), TTApp) :-
	TT = ((Fun,Ty1~>Ty2) @ (H,Ty1), Ty2), 
	apply_ttFun_to_ttArgs(TTRest, TT, TTApp).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% true when TT1 is properly subsumed by TT2
proper_tt_isa((tlp(_,Lem1,_,_,_), _),  (tlp(_,Lem2,_,_,_), _)) :-
	Lem1 \= Lem2, 
	isa(Lem1, Lem2).

proper_tt_isa((TT1_fun @ _, _),  (TT2_fun @ _, _)) :-
	proper_tt_isa(TT1_fun, TT2_fun). % not sufficeint condition but necessary
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% true if TTterm is a conjunction of several constant NNPs
conj_of_const_NNPs( (((Conj, np:_~>np:_~>np:_) @ TT1, _) @ TT2, _) ) :-
	!,
	Conj = tlp(_, Lemma, _CC, _, _),
	member(Lemma, ['or', 'and']),
	conj_of_const_NNPs(TT1),
	conj_of_const_NNPs(TT2).
		
conj_of_const_NNPs( (tlp(_,_,'NNP',_,_), np:_) ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% true if TTterm is a Mod:NP~>NP @ Head:NP, where Mod is not conj@NP
np_mod_app_np( ((Mod,np:_~>np:_) @ _TT2, np:_) ) :-
	\+(	(Mod = (tlp(_,Lemma,_CC,_,_),np:_~>np:_~>np:_) @ _, 
		member(Lemma, ['or', 'and']))
	  ).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Convert constant (either NP or e-type) to e-type
tt_constant_to_tt_entity((C, Type), (C, e)) :-
	member(Type, [np:_, e]),
	!.
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Checks if ttTerm is A:n~>np @ N:n where A=a, or is antitone for 2nd argument
% this kind of ttTerms are not good for treating as constants in aligned settings
% e.g. a man sleeps =T, a man doesn't sleep=T can be forced to be inconsistent
npTTterm_unlike_constant((TTdet @ _, np:_)) :- 
	TTdet = (tlp(_,Lm,'DT',_,_), n:_~>np:_),
	nonvar(Lm),
	( member(Lm, ['a']) %!!! add more details: no, every, two, s
	;  Lm :: _ :: [_, dw | _]
	).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Checks if ttTerm is Conj @ Term
% this kind of ttTerms are not good for treating as constants in aligned settings
modTTterm_with_conj_sent_head((TTconj @ _, Ty~>Ty)) :- 
	TTconj = (tlp(_,Lm,'CC',_,_), Ty~>Ty~>Ty),
	final_value_of_type(Ty, s:_),
	nonvar(Lm).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% treat all constant:NP as constant:e 
np_const_to_e_const((Var, Type), (Var, Type)) :-
	var(Var), 
	!.

np_const_to_e_const((TT1 @ TT2, Type), (SimTT1 @ SimTT2, Type)) :-
	!, 
	np_const_to_e_const(TT1, SimTT1),
	np_const_to_e_const(TT2, SimTT2).

np_const_to_e_const( (abst(TTx, TT), Type), (abst(TTx, SimTT), Type) ) :-
	!, 
	np_const_to_e_const(TT, SimTT).	

% treats all constant:np as constant:e
np_const_to_e_const( (TLP, Type1),  (TLP, Type2)) :-
	(TLP =.. [tlp | _]; atom(TLP)),
	!,
	( Type1 = np:X, X \== 'thr' ->
		Type2 = e
	; Type2 = Type1
	).

np_const_to_e_const( (TT, Type), (SimTT, Type) ) :-
	!, 
	np_const_to_e_const(TT, SimTT). 












