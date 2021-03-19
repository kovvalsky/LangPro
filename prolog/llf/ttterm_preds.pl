%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module('ttterm_preds',
	[
		abst_ttTerm_with_ttArgs/3,
		add_heads/2,
		adjuncted_ttTerm/1,
		apply_ttFun_to_ttArgs/3,
		apply_ttMods_to_ttArg/3,
		cc_as_fun/1,
		conj_of_const_NNPs/1,
		extract_const_ttTerm/2,
		extract_lex_NNPs_ttTerms/3,
		feed_ttTerm_with_ttArgs/3,
		is_tlp/1,
		match_list_ttTerms/3,
		match_list_only_terms/2,
		match_ttTerms/3,
		modList_be_args_to_nodeList/3,
		modList_node_to_modNode_list/2,
		modTTterm_with_conj_sent_head/1,
		normalize_lexicon/2,
		np_const_to_e_const/2,
		np_mod_app_np/1,
		npTTterm_as_constant/1,
		npTTterm_unlike_constant/1,
		proper_tt_isa/3,
		pretty_vars_in_ttterm/4,
		print_ttTerms_in_latex/1,
		right_branch_tt_search/4,
		rel_clause_ttterm/1,
		red_rel_clause_ttterm/1,
		set_type_for_tt/3,
		set_type_for_tt/5,
		subset_only_terms/2,
		tlp_lemma_in_list/2,
		tlp_pos_in_list/2,
		tlp_pos_with_prefixes/2,
		token_norm_ttTerm/3,
		ttTerm_to_informative_tt/2,
		ttTerms_same_type/2,
		tt_constant_to_tt_entity/2,
		unpack_ttTerm/2,
		wh_mod_np_to_nodes/3
	]).


:- use_module('../latex/latex_ttterm', [latex_ttTerm_print_tree/3, latex_ttTerm_preambule/1]).
:- use_module('../printer/reporting', [report/1]).
:- use_module('ttterm_to_term', [ttTerm_to_prettyTerm/2]).
:- use_module('../lambda/lambda_tt', [op(605, yfx, @), op(605, xfy, ~>)]).
:- use_module('../knowledge/lexicon', [op(640, xfy, ::), '::'/2]).
:- use_module('../knowledge/knowledge', [disjoint/3, word_synonyms/3, isa/3]).
:- use_module('../lambda/type_hierarchy', [
	cat_eq/2, final_value_of_type/2, luc/3, general_cat/2
	]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Right branch search a TT
right_branch_tt_search(F, (F@B,_), [], B).

right_branch_tt_search(F, (A@B,_), [A|L], R) :-
	right_branch_tt_search(F, B, L, R).



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
noun_node_to_isa_node_list(SrcNode, [SrcNode | Nodes], KB) :-
	SrcNode = nd([], TTn, Args, TF),
	TTn = (tlp(_,Lm,'NN',_,_), n:_),
	!,
	(bagof(Node,
		 Lm^( %isa_wn(Lm, Lemma),
			  isa(Lm, Lemma, KB), \+disjoint(Lm, Lemma, KB),
			  Node = nd([], (tlp(Lemma,Lemma,'NN',_,_), n:_), Args, TF)
			),
			Nodes)	-> true
	; Nodes = []
	).

noun_node_to_isa_node_list(SrcNode, [SrcNode], _) :-
	SrcNode = nd([], (_, n:_), _Args, _TF).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% takes a node with non-empty modList and returns a list of nodes with elements of modList applied to a head
% ModList: TTterm: Args: TF ---> [M1: TTterm: Args: TF, ..., Mn: LLF: Args: TF]
modList_node_to_modNode_list(nd([], _TT, _Args, _TF),  []) :-
	!.

modList_node_to_modNode_list( nd([Mod | Rest], TT, Args, TF), NewNdoes ) :-
	findall(NewNode,  mod_node_to_node(Mod, TT, Args, TF, NewNode), NewNodes1), %!!! why findall here?
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
	NewNode = nd( [], (Mod@TT, Mty2), Args, TF ),
	!. % otherwise [into@C]:drop:C succeds two times, sick-3626

mod_node_to_node(Mod, TT_N, [Arg], TF, NewNode) :-
	TT_N = (_, n:_),
	mod_to_entity_property(Mod, Prop),
	tt_constant_to_tt_entity(Arg, C), % not necessary
	NewNode = nd( [], Prop, [C], TF ).

mod_node_to_node(Mod, TT_N, [Arg], TF, NewNode) :-
	TT_N = (_, n:_),
	mod_to_n_modifier(Mod, N_Mod),
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

match_ttTerms(X, Y, _) :-  % variants, only matching Abst(X,X@const) = Abst(Y,const@Y) causes error
	(var(X); var(Y)),  % added later
	!, fail.

match_ttTerms(X, Y, _KB_XP) :-  % variants, only matching Abst(X,X@const) = Abst(Y,const@Y) causes error
	( X =@= Y, X = Y  % avoids matching var to term
	; X = (_,Ty),
	  Y = (_,Ty),
	  ttTerm_to_prettyTerm(X, PrX),
	  ttTerm_to_prettyTerm(Y, PrY), % added
	  PrX =@= PrY,
	  PrX = PrY
	), !.

match_ttTerms((TTexp1, Type1, _), (TTexp2, Type2, _), KB_XP) :- % are we using it?
	%cat_eq(Type1, Type2), %ignoring features
	luc(Type1, Type2, _), % sick-2722
	match_ttExp(TTexp1, TTexp2, KB_XP), !.

match_ttTerms((TTexp1, Type1), (TTexp2, Type2), KB_XP) :- % ignoring types?
	%cat_eq(Type1, Type2), %ignoring features
	luc(Type1, Type2, _), % sick-2722
	match_ttExp(TTexp1, TTexp2, KB_XP), !.

% Matching of ttExpressions in the tableau
match_ttExp(X, Y, _KB_XP) :-  % variants, only matching Abst(X,X@const) = Abst(Y,const@Y) causes error
	X =@= Y, % avoids matching var to term
	X = Y,
	!.

%-------------------------------------------------------
match_ttExp(X, Y, _) :-
	(var(X); var(Y)),
	!, fail.

match_ttExp(FunTT1 @ ArgTT1, FunTT2 @ ArgTT2, KB-XP) :-
	match_ttTerms(FunTT1, FunTT2, KB-XP),
	match_ttTerms(ArgTT1, ArgTT2, KB-XP).

match_ttExp(abst(_,TT1), abst(_,TT2), KB_XP) :-
	match_ttTerms(TT1, TT2, KB_XP).

match_ttExp((TTexp1, Type1), (TTexp2, Type2), KB_XP) :-
	%cat_eq(Type1, Type2), %ignoring features
	luc(Type1, Type2, _), % sick-2722
	match_ttExp(TTexp1, TTexp2, KB_XP).

match_ttExp(TT1, TT2, KB_XP) :- % ignoring everything except lemmas
	TT1 = tlp(_Tk1, Lemma1, _Pos1, _F11, _F12),
	TT2 = tlp(_Tk2, Lemma2, _Pos2, _F21, _F22),
	( Lemma1 = Lemma2
	; word_synonyms(Lemma1, Lemma2, KB_XP) % Slows the mathcing process
	), !.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Matching of list of ttTerms in the tableau
match_list_ttTerms([], [], _KB_XP) :- !.

match_list_ttTerms([Head1 | Rest1], [Head2 | Rest2], KB-XP) :-
	match_ttTerms(Head1, Head2, KB-XP),
	match_list_ttTerms(Rest1, Rest2, KB-XP).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% !!! no KB?
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% subset over lists with pretty terms
subset_only_terms(List1, List2) :-
	maplist(ttTerm_to_prettyTerm, List1, L1),
	maplist(ttTerm_to_prettyTerm, List2, L2),
	subset(L1, L2).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Print ttTerms in latex file
print_ttTerms_in_latex(List) :-
	open('latex/ttTerms.tex', write, S, [encoding(utf8), close_on_abort(true)]),
	%asserta(latex_file_stream(S)),
	latex_ttTerm_preambule(S),
	write(S, '\\begin{document}\n'),
	maplist(latex_ttTerm_print_tree(S, 0), List),
	write(S, '\\end{document}'),
	close(S).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TTterm is a possible collocation, return a collcoation and POS
% !!! how to extract from "young tall woman" a "young woman"??? all combinations?
maybe_2_collocation( ((tlp(_,Lm1,Pos1,_,_), Ty1) @ (tlp(_,Lm2,Pos2,_,_), Ty2), _Type),  (Lemma, POS) ) :-
	!,
	nonvar(Lm1),
	nonvar(Lm2),
	( memberchk((Ty1, Ty2, POS),  [(n:_~>n:_, n:_, 'NN'), (_, pr, 'VB')]) %!!! adverbs, adjectives?
    ; atom_chars(Pos1, ['N','N'| _]), atom_chars(Pos2, ['N','N'| _]), POS = 'NN'
	; atom_chars(Pos1, ['V','B'| _]), memberchk(Pos2, ['RB', 'RP', 'IN']), POS = 'VB'
	),
	!,
	atomic_list_concat([Lm1, Lm2], ' ', Lemma).

% TTterm includes a possible collocation on the upper level
maybe_2_collocation( ((tlp(_,Lm1,Pos1,_,_), _Ty1) @ ((tlp(_,Lm3,Pos3,_,_), _Ty3) @ _, _Ty2), _Type),  (Lemma, POS) ) :-
	nonvar(Lm1),
	nonvar(Lm3),
	( atom_chars(Pos1, ['V','B'| _]), memberchk(Pos3, ['RB', 'RP', 'IN']), POS = 'VB'
	),
	!,
	atomic_list_concat([Lm1, Lm3], ' ', Lemma).


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
	Term = tlp(_,Lemma,POS,_,_), % Lexical case
	!,
	Temp_Lex = [(Lemma,POS) | Old_Lex],
	( Type = n:_~>n:_, \+atom_chars(POS, ['J','J'|_]) -> % sick-9067: dirty:NN:n->n
		New_Lex = [(Lemma,'JJ') | Temp_Lex]
	; New_Lex = Temp_Lex
	),
	( ((Type = np:F, F \= thr); Type = e) -> %possessives are not captured
		New_NNPs = [(Lemma,e) | Old_NNPs] % keep named entities as of type e only; optimizes aligned NPs too
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
% TT have to be S-category returning functor ? %!!!why?
feed_ttTerm_with_ttArgs((Term,Ty), NewTT, TTArgs) :-
	apply_ttFun_to_ttArgs((Term,Ty), TTArgs, NewTT),
	NewTT = (_, s:_).
% 	!,
% 	TTarg = (_, A), %sub_type(Ty, A), !, % for some reasons
% 	TT = ((Exp, A~>B) @ TTarg, B),
% 	feed_ttTerm_with_ttArgs(TT, NewTT, Rest).
%
% feed_ttTerm_with_ttArgs((Exp, s:F), (Exp, s:F), []).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% abst_ttTerm_with_ttArgs(TT, NewTT, ttArgs)
% NewTT is a result of abstracting TT with the list ttArgs;
% the first element of ttArgs is abstracted last
abst_ttTerm_with_ttArgs((Exp,Ty), NewTT, [(Arg,Type) | Rest]) :-
	!,
	NewTT = (abst((Arg,Type), (Exp1,Ty1)), Type~>Ty1),
	abst_ttTerm_with_ttArgs((Exp,Ty), (Exp1,Ty1), Rest).

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
	( var(Type2)
	->	ttTerms_same_type(Rest, Type1, Type)
	; 	nonvar(Type1),
		luc(Type1, Type2, Type3),
		ttTerms_same_type(Rest, Type3, Type)
	).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% set type for TTterm
set_type_for_tt( TT, Type, NewTT) :-
	set_type_for_tt( TT, Type, NewTT, [], _Changed_Vars).

set_type_for_tt( (Var, Ty), Type, (Var, Type), Vars, [(Var, Type)]) :- %adds the changed variable
	var(Var), !,
	( member((X,TyX), Vars), X==Var, TyX\=Ty ->
		fail
	; true
	), !.
	%Ty = np:_,  % to block type raising of variables that are possibly bind by abtracted variables
	%Type = (np:_~>s:_)~>s:_,
	%!,
	%fail.

set_type_for_tt( (Atom, _Ty), Type, (Atom, Type), _Vars, []) :-
	atom(Atom), % due to atoms introduced by alignment process
	!.

set_type_for_tt( (TLP, _Ty), Type, (TLP, Type), _Vars, []) :-
	TLP =.. [tlp|_], !.

set_type_for_tt( ((ConjTT @ TT1, Ty~>Ty) @ TT2, Ty), Type, (NewExp, Type), Vars, ChVars ) :- %!!! inserted
	ConjTT = (TLP, Ty~>Ty~>Ty),
	TLP = tlp(_,Lm,POS,_,_),
	( POS = 'CC'; member(Lm, [and, or]); POS = 'DT', report([Lm, ':', POS, ' as conjunction']) ), !, %sick-272 treats a:DT,n~>n~>n
	set_type_for_tt(TT1, Type, NewTT1, Vars, ChVars1),
	set_type_for_tt(TT2, Type, NewTT2, Vars, ChVars2),
	append(ChVars1, ChVars2, ChVars),
	NewExp = ((TLP, Type~>Type~>Type) @ NewTT1, Type~>Type) @ NewTT2.

% case for modifier: MOD @ HEAD -> change type of HEAD
set_type_for_tt( (TT_Mod @ TT_Head, _), Type, (NewExp, Type), Vars, ChVars) :-
	TT_Mod = (_, Type1 ~> Type2),
	cat_eq(Type1, Type2), %!, may backtrack if TT_Head is np variable that needs to be type raised
	set_type_for_tt(TT_Head, Type, New_TT_Head, Vars, ChVars1),
	set_type_for_tt(TT_Mod, Type~>Type, New_TT_Mod, Vars, ChVars2),
	append(ChVars1, ChVars2, ChVars),
	!,
	NewExp = New_TT_Mod @ New_TT_Head.

set_type_for_tt( (A @ B, _Ty), Type, (TempTT @ B, Type), Vars, ChVars) :-
	A = (_, TyB ~> _),
	set_type_for_tt(A, TyB~>Type, TempTT, Vars, ChVars), !.

% For Abstraction
%the type should be consistent with the abstracted variable
set_type_for_tt( (abst((X,TyX), TT), _Ty), Type,  (abst((X,TyX), NewTT), Type), Vars, ChVars) :-
	var(X),
	Type = TyX ~> TyVal,
	set_type_for_tt(TT, TyVal, NewTT, [(X,TyX)|Vars], ChVars), !. %!!! but this can change a bound variable type

set_type_for_tt( (TT, _Ty), Type, (TT, Type), _, []) :- %!!! changed variables are empty by default
	TT = (_, _).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% applies tt function to list of tt arguments
apply_ttFun_to_ttArgs(TTFun, [], TTFun).

apply_ttFun_to_ttArgs((Fun,Ty1~>Ty2), [(H,Ty1) | TTRest], TTApp) :-
	TT = ((Fun,Ty1~>Ty2) @ (H,Ty1), Ty2),
	apply_ttFun_to_ttArgs(TT, TTRest, TTApp).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% apply a list of modifier terms to an argument
% first applied modifier is the last in the list
% in this way, the list has a right branching order
apply_ttMods_to_ttArg([], Arg, Arg).

apply_ttMods_to_ttArg([H|Tail], (Arg,TyA), Result) :-
	append(Front, [(M,TyA~>TyM)], [H|Tail]),
	TT = ((M,TyA~>TyM) @ (Arg,TyA), TyM),
	apply_ttMods_to_ttArg(Front, TT, Result).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% true when TT1 is properly subsumed by TT2
proper_tt_isa((tlp(_,Lem1,_,_,_), _),  (tlp(_,Lem2,_,_,_), _), KB_xp) :-
	Lem1 \= Lem2,
	isa(Lem1, Lem2, KB_xp).

proper_tt_isa((TT1_fun @ _, _),  (TT2_fun @ _, _), KB_xp) :- % FIXME args should be shared
	proper_tt_isa(TT1_fun, TT2_fun, KB_xp). % not sufficeint condition but necessary


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% true if TTterm is a conjunction of several constant NNPs
conj_of_const_NNPs( (((Conj, np:_~>np:_~>np:_) @ TT1, _) @ TT2, _) ) :-
	nonvar(Conj), !, % prevent variable matching
	Conj = tlp(_, Lemma, _CC, _, _),
	member(Lemma, ['or', 'and']),
	conj_of_const_NNPs(TT1),
	conj_of_const_NNPs(TT2).

conj_of_const_NNPs( (tlp(Tok,_,'NNP',_,_), np:_) ) :-
	nonvar(Tok). % prevent variable matching

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% true if TTterm is a Mod:NP~>NP @ Head:NP, where Mod is not conj@NP
np_mod_app_np( ((Mod,np:_~>np:_) @ _TT2, np:_) ) :-
	\+(	(Mod = (tlp(_,Lemma,_CC,_,_),np:_~>np:_~>np:_) @ _,
		member(Lemma, ['or', 'and']))
	  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% true if TTterm is CC@A where CC is a term with POS CC
cc_as_fun( ((TLP_CC,_) @ _B, _Ty) ) :-
	( tlp_pos_in_list(TLP_CC, ['CC'])
	; tlp_lemma_in_list(TLP_CC, ['and', 'or', 'who']) ), !.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Convert constant (either NP or e-type) to e-type
tt_constant_to_tt_entity((C, Type), (C, e)) :-
	member(Type, [np:_, e]),
	!.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Checks if ttTerm is A:n~>np @ N:n and if it can treated as constant
npTTterm_as_constant((TTdet @ _, np:_)) :-
	TTdet = (tlp(_,Lm,'DT',_,_), n:_~>np:_),
	nonvar(Lm),
	member(Lm, ['the', 'this', 'that']). %!!! every?

% the A conj the B
npTTterm_as_constant( ((Conj @ TT1, np:_~>np:_) @ TT2, np:_) ) :-
	Conj = (tlp(_,Lm,'CC',_,_), Ty~>Ty~>Ty),
	nonvar(Lm),
	npTTterm_as_constant(TT1),
	npTTterm_as_constant(TT2).

% special case is determiners monotone for 2nd argument
% treating them as constants can lead scope changing of negation
% a man sleeps =T, a man doesn't sleep=T can be forced to be inconsistent
% this cases fail npTTterm_as_constant but pass npTTterm_unlike_constant

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Checks if ttTerm is A:n~>np @ N:n where it cannot be treated as constant at all.
% e.g. is antitone for 2nd argument
% this kind of ttTerms are not good for treating as constants in aligned settings
% e.g. no_man sleeps -> no_man sleeps in a bed
npTTterm_unlike_constant((TTdet @ _, np:_)) :-
	TTdet = (tlp(_,Lm,'DT',_,_), n:_~>np:_),
	nonvar(Lm),
	( member(Lm, ['no']) %!!! add more details: no, every, two, s
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





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% normalize lexicon - a set(!) of (Lemma,POS) pairs
% normalizing includes Few & few to map to one item
% fracas-19 Europeans-European, fracas-44 few-Few
% !!! sick-train 2205? tokkens differ in register

normalize_lexicon([], []).

normalize_lexicon([(L1,Pos1) | Lex], Lexicon) :-
	member((L2,Pos2), Lex),
	normalize_Lemma_POS((L1,Pos1), (L2,Pos2), (L,Pos)) ->
		Lexicon = [(L,Pos) | Lexic],
		normalize_lexicon(Lex, Lexic)
	; Lexicon = [(L1,Pos1) | Lexic],
	  normalize_lexicon(Lex, Lexic).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% two atoms differ in the case of the first letter or dont differ
% returns the canonical word - with lower letter
% e.g. (A,A) -> A and ()
normalize_Lemma_POS((L1, P1), (L2, P2), (L, P)) :-
	atom_chars(L1, [I1 | REST1]),
	atom_chars(L2, [I2 | REST2]),
	downcase_atom(I1, Si),
	downcase_atom(I2, Si), % same letters in the begining
	(I1 = Si -> I = I1; I = I2),
	maplist(downcase_atom, REST1, Rest1),
	maplist(downcase_atom, REST2, Rest2),
	( Rest1 = Rest2 ->
	  	( I = I1 -> (L, P) = (L1, P1);  (L, P) = (L2, P2) )
    ; append(Rest1, ['s'], Rest2) ->
		atom_chars(L, [I | Rest1]),
	  	P = P1
    ; append(Rest2, ['s'], Rest1),
	  atom_chars(L, [I | Rest2]),
	  P = P2
	). % here maybe NNP be chosen over NN if NNS vs NNP, or VBS over NN, needs syntactic category distinguishing


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Normalized Tokens of TTterms based on normalized lexicon
%!!! not completely finished, just substitutses tokens with lemma, for tokesn special procedure needed

token_norm_ttTerm(_, (Var, Type), (Var, Type)) :-
	var(Var), !.

token_norm_ttTerm(Lex, (TT1 @ TT2, Type), (SimTT1 @ SimTT2, Type)) :-
	!, token_norm_ttTerm(Lex, TT1, SimTT1),
	token_norm_ttTerm(Lex, TT2, SimTT2).

token_norm_ttTerm( Lex,  (abst(TTx, TT), Type), (abst(TTx, SimTT), Type) ) :-
	!, token_norm_ttTerm(Lex, TT, SimTT).

token_norm_ttTerm( Lex, (tlp(_Tk,Lem,Pos,F1,F2), Type),  SimTT ) :-
	member((L,P), Lex),
	normalize_Lemma_POS((L,P), (Lem, Pos), (L, P)),
	%report(['Failure in normalization of lexicon: (', L, ',', P, ') vs (', Lem, ',', Pos, ')']), fail ),
	!, SimTT = (tlp(L,L,P,F1,F2), Type).

token_norm_ttTerm(Lex, (TT, Type), (SimTT, Type) ) :-
	!, token_norm_ttTerm(Lex, TT, SimTT).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% pretty variables instead of _G23
pretty_vars_in_ttterm(A, Z, TT, Pretty) :-
	copy_term(TT, Pretty),
	pretty_vars_in_ttterm_(A, Z, Pretty).

pretty_vars_in_ttterm_(X-P, Z, (Exp, _)) :-
	var(Exp) 	-> report(['Error: unexpected free variable found in pretty_vars_in_ttterms'])
	; atom(Exp) ->
		Z = X-P
	; Exp =.. [tlp | _] ->
		Z = X-P
	; Exp = TT1 @ TT2 ->
		pretty_vars_in_ttterm_(X-P, X1-P1, TT1),
		pretty_vars_in_ttterm_(X1-P1, Z, TT2)
	; Exp = abst((Var,Type), TT1) ->
		((memberchk(Type, [e,np:_]) ->
			atomic_list_concat(['x', X], Var),
		 	X1 is X + 1, P1 = P
		 ; atomic_list_concat(['p', P], Var),
			P1 is P + 1, X1 = X
		 ),
		pretty_vars_in_ttterm_(X1-P1, Z, TT1)
		)
	; Exp = (E,_) ->
		pretty_vars_in_ttterm_(X-P, Z, (E,_))
	; report(['Error: unexpected clause in pretty_vars_in_ttterms']).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
add_heads( (Tr,Ty), (Tr,Ty,_H) ) :-
	var(Tr), !.

add_heads( (Tr,Ty), (Term_H,Ty,_H) ) :- %heads can change in lx rules
	Tr = (Tr1,Ty1),
	Term_H = (_,Ty1,_), !,
	add_heads((Tr1,Ty1), Term_H).

add_heads( (Abst,Type), (Abst_H,Type,H) ) :-
	Abst = abst(TTX, (Tr,Ty)),
	Abst_H = abst( TTX, (Tr_H,Ty,H_1) ), !, %? before (TTX,_)
	ignore(H_1 = H),
	add_heads((Tr,Ty), (Tr_H,Ty,H_1)). %some details needed, % due to attach_pr_to_verb


add_heads( (App,Type), (App_H,Type,H) ) :-
	App = (Tr1, Ty1) @ (Tr2, Ty2),
	App_H = (Tr1_H1,Ty1,H1)@(Tr2_H2,Ty2,H2), !,
	add_heads((Tr1, Ty1), (Tr1_H1, Ty1, H1)),
	add_heads((Tr2, Ty2), (Tr2_H2, Ty2, H2)), %some details needed
	detect_head((Ty1,H1), (Ty2,H2), H).

add_heads((TLP,Ty), (TLP,Ty,H)) :-
	TLP = tlp(_,Lm,Pos,F1,F2),
	ignore(H = tlp(Ty,Lm,Pos,F1,F2)). % due to attach_pr_to_verb

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%detect_head( (Ty~>Ty, _), (Ty, H2), H2 ) :- !.

detect_head( (Ty2~>Ty1, _), (Ty2, H2), H2 ) :-
	cat_eq(Ty1, Ty2), !.  % binds category features

detect_head( (_, H1), (_, _), H1 ) :-
	!.

detect_head( (_, _), (_, _), _). % for removing heads since word substitutions cannot project upwards

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% auxiliary preds
wh_mod_np_to_nodes((WH @ NP, np:_), NP, [nd([], VP, [NP], true)|Rest]) :-
	WH = ((Who, (np:_~>s:_)~>_Mod) @ VP, np:_~>np:_),
	tlp_lemma_in_list(Who, ['who']),
	( NP = (Term,np:_) ->
		Rest = [nd([], VP, [(Term,e)], true)]
	; Rest = [] ).

% TTterm is a relative clause
rel_clause_ttterm(( (WH,_) @ (_VP,np:_~>s:_), n:_~>n:_ )) :-
	tlp_lemma_in_list(WH, ['who']).

% TTterm is a reduced relative clause with type-changing
red_rel_clause_ttterm(( (VP, np:_~>s:_), n:_~>n:_ )) :-
	nonvar(VP).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% auxiliary preds
tlp_pos_in_list(TLP, List) :-
	nonvar(TLP),
	TLP =.. [tlp,_,_,POS|_],
	memberchk(POS, List).

tlp_lemma_in_list(TLP, List) :-
	nonvar(TLP),
	TLP =.. [tlp,_,Lemma|_],
	memberchk(Lemma, List).

tlp_pos_with_prefixes(TLP, Prefixes) :-
	nonvar(TLP),
	TLP =.. [tlp,_,_,POS|_],
	findall(PF, (
		member(PF, Prefixes),
		atom_concat(PF, _, POS)
	), [_|_]).

is_tlp(TLP) :-
	nonvar(TLP),
	TLP =.. [tlp|_].
