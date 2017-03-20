%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: Tableau Prover for Natural Logic
%     Version: 12.06.12
%      Author: lasha.abzianidze{at}gmail.com 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%    Generic User Defined Predicates 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% true_member(Element, List)
% checks if Element is bound with the member of List
% also avoids binding variables of List
true_member(E, List) :-
	nonvar(List), 
	List = [Head | Rest],
	(E == Head;  % fixed
	 true_member(E, Rest) ).	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% subsumed_member(Element, List) 
% succeeds when Element is subsumed by a member of a list
% use for history update for tableau rule applications
subsumes_member(E, List) :-
	nonvar(List), 
	List = [Head | Rest],
	( subsumes_term(Head, E);  % member subsumes an element
	  subsumes_member(E, Rest) ),
	!.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% uncpecified list member
ul_member(E, List) :-
	nonvar(List), 
	List = [Head | Rest],
	( Head = E
	; ul_member(E, Rest) 
	).	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% append list to unspecified list
ul_append(MainList, List) :-
	nonvar(MainList), 
	!,
	MainList = [_ | Rest],
	ul_append(Rest, List).

ul_append(MainList, List) :-
	var(MainList),
	!,
	append(List, _, MainList).	

% adds a new element to UL if the element is not there
% if element is there fail
add_new_to_ul(New, UL) :-
	\+ul_member(New, UL),
	ul_append(UL, [New]).
	



append_uList(MainUList, UList) :-
	remove_varTail_from_uList(MainUList, MainList), 
	remove_varTail_from_uList(UList, List),
	append(MainList, List, SumList),
	list_to_set(SumList, Set),
	append(Set, _, MainUList).

remove_varTail_from_uList(UList, List) :-
	append(List, Var, UList),
	var(Var), !.




remove_adjacent_duplicates([H,H|Rest], Rest1) :-
	!, remove_adjacent_duplicates([H|Rest], Rest1). 

remove_adjacent_duplicates([H1,H2|Rest], [H1|Rest1]) :-
	!, remove_adjacent_duplicates([H2|Rest], Rest1). 

remove_adjacent_duplicates(X, X).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%5
% takes list and returns set, where matching is considered as euqlity
list_to_set_using_match(List, Set) :-
	list_to_set_using_match_r(List, Reverse),
	reverse(Reverse, Set).

list_to_set_using_match_r([], []) :- !.
	
list_to_set_using_match_r(List, Set) :-
	append(Front, [H], List), !,
	( \+memberchk(H, Front) ->
		Set = [H | Rest],
		list_to_set_using_match_r(Front, Rest)
	; list_to_set_using_match_r(Front, Set)
	). 	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% mon(Term, MonotonicityValue)
% takes Term and generates its MonotonicityValue
% MonotonicityValue is one of the atoms: up, dw, non
tt_mon(Term, Mon) :-
	tt_mon_(Term, [], [Mon | _]).	
	
tt_mon_((Var,_), _, _) :- %!!! abst(X, X@a) is up monotonoc actually! 
	var(Var),				% but it is not considered here yet
	!,
	fail.

tt_mon_( (tlp(_,Const,Pos,_,_), Type), _, MonList ) :-
	%atom(Const), 
	!,
	( Const :: Type :: MonList
	; Pos = 'CD', MonList = [up,up]  %!!! except null
	; atom_chars(Pos, ['V','B' | _]),
	  MonList = [up | _]  %!!! in general, verbs are upward monotone
	), !. %!!! kills variant of several output, eg. than
	
tt_mon_(TT, Vars, [Mon | RestMon]) :-
	%nonvar(TT), 
	TT = ( abst((X,_), TT1), _ ), !,
	tt_mon_(TT1, [X::Mon | Vars], RestMon).	
	
tt_mon_(AppTT, Vars, MonList) :-
	%nonvar(AppTT),
	AppTT = (FunTT @ (Arg,_), _), !,
	tt_mon_(FunTT, Vars, [ArgMon | MonList]),
	( var(Arg) -> 
		member(X::ArgMon, Vars), X == Arg; 
	  	true ).	
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% tt_mon_up differs from tt_mon(_,up) that it
% counts a and the as mon_ups
tt_mon_up((Term,Type)) :-
	Type = n:_~>(np:_~>s:_)~>s:_,
	Term = tlp(_,Lm,_,_,_),
	memberchk(Lm, ['s', 'the', 'a']),
	!.

tt_mon_up(TT) :- % too relaxed e.g. 'many':non,up passes this
	\+tt_mon(TT, dw),
	\+tt_mon(TT, non), % 'many' fails this. fracas-56,58
	!.
	
tt_mon_up(TT) :-
	tt_mon(TT, up).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% more relaxed version of tt_mon(TT, up) 
%maybe_tt_mon_up((Term, Type)) :-
 
maybe_tt_mon_up((Term, Type)) :-
	\+tt_mon((Term, Type), dw),
	\+memberchk(Type, [np:_~>_, e~>_]),
	\+atom(Term). % may cause information loss


	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% neg(Value1, Value2)
% true if negation of Value1 is Value2
neg(true, false).
neg(false, true).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% For testing
report(MessageList) :-
	%maplist(term_to_atom, MessageList, AtomList),
	%atomic_list_concat(AtomList, Message),
	with_output_to(atom(Message), maplist(write, MessageList)),
	writeln(Message).

report(Message, Term) :-
	\+is_list(Message),
	term_to_atom(Term, Atom),
	write(Message),
	writeln(Atom).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% For reports
:- dynamic debMode/1.

debMode( 'nil' ).
debMode( ral(400) ).
debMode( effCr(['nonProd', 'nonBr', 'equi', 'nonCons']) ).

set_debMode([H | Rest]) :-
	( H = ral(_) ->
		retractall( debMode(ral(_)) ),
		assertz( debMode(H) )
	; H = effCr(_) ->
		retractall( debMode(effCr(_)) ),
		assertz( debMode(H) )
	; H = ss(SS) ->
		retractall( debMode(ss(_)) ),
		(is_list(SS) -> List = SS; numlist(1,SS,List)),
		assertz( debMode(ss(List)) )
	; assertz( debMode(H) )
	),
	set_debMode(Rest).

set_debMode([]).

reset_debMode :-
	retractall( debMode(_) ),
	assertz( debMode('nil') ),
	assertz( debMode(effCr(['nonProd', 'nonBr', 'equi', 'nonCons'])) ),
	assertz( debMode(ral(400)) ).
	
%  debMode
% 'fix': 				prints fixes done on CCG trees
% 'proof_tree': 		develope a proof tree
% 'aall':				allows alignment of any NPs
% 'prprb':				prints the problem
%  waif(filename): 		writes answers in file in SICK style
% 'ne':					reports MW Named Entity found 												
% 'mwe':				multiword expression found
% 'prlim':				prints when rule limit is reached
% 'ProperNames':		consideres all bare nouns (even plurals) as proper names
% 'the':				inserts "the" for bare nouns (even plurals) instead of "a"
%  a2the				replace all a,an with the
%  s2the				replaces all plurals with definites
%  thE					allow Existential import for the in false context
% 'wn_ant':				uses antonym relation of Wordnet
%  lex:					print extracted Lexicon
% '2class':				binary classification
%  ral(N):				rule application limit is N
%  no_gq_llfs			dont obtain LLFs with generalized quantifiers, i.e. use fixed CCG terms
% 'gq_report'			report how quantifier raising is going on		
%  pr_lex_rules			print lexical rules that are not explained
%  pr_sen				print a sentence when running gen_llfs_latex
%  disj					use hand-coded disjoint relation
%  usedRules([rules])	print the rules if they are used
%  parallel				concurrent_maplist for entail
%  pr_kb				print knowledge base
%  singPrem				takes only single premised problems, for fracas
%  fracFilter			filter Fracas problems that are ill formed
%  noPl					Treat plural morpheme as a
%  constchk				allow consistency check
%  noHOQ				Treating most,many,several,a_few,both as a
%  noThe				Treat The as a
%  shallow				using shallow classifier
%  neg_cont				classifier based on negative vords to identify contradictions
%  sub_ent				classifier based on subset of set of words to identify entailment	
%  noAdmissRules		exclude admissible rules 
%  EffCr([nonBr, equi, nonProd, nonCons])	defining an effciency criterion 
%  eccg				    latex trees are probted in different tex file
%  ss([...])			list of frequent sysnsets to choose 
% allInt				All noun modifeirs are intersective


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% For concatenating list of terms
term_list_concat(TermList, Atom) :-
	maplist(term_to_atom, TermList, AtomList),
	atomic_list_concat(AtomList, Atom1),
	atomic_list_concat(List, '\'', Atom1),
	atomic_list_concat(List, Atom).






%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% remove(E, OldList, NewList); 
% NewList is a result of removing 
% all occurences of E from OldList;
% deterministic;
% based on matching;
% can be used delete/3 also but it is deprocated I guess

remove(E, [H | T], NewList) :- 
	%\+ E \= H, % just checks for matching but does not match it
	E = H,
	!,	
	remove(E, T, NewList).
	
remove(E, [H | T], [H | NewList]) :-
	!,	
	remove(E, T, NewList).

remove(_, [], []).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
discard(E, [H | T], NewList) :- 
	\+ E \= H, % just checks for matching but does not match it
	!,	
	discard(E, T, NewList).
	
discard(E, [H | T], [H | NewList]) :-
	!,	
	discard(E, T, NewList).

discard(_, [], []).



true_remove(E, [H|T], List) :- 
	E == H, 
	!,
	true_remove(E, T, List).

true_remove(E, [H | T], [H | List]) :-
	!, 
	true_remove(E, T, List).

true_remove(_, [], []).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% removes first element matching E from List 
remove_first(E, [E | Rest], Rest) :- 
	!.

remove_first(E, [H | Rest], [H | New]) :-
	!, 
	remove_first(E, Rest, New).

remove_first(_, [], []).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% adds only new elements of List1 to List2 without matching 
add_new_elements([H | Rest], List, NewList) :-
	subsumes_member(H, List) -> %!!! before was. this made H specific and can fail adding info if R1<R2 and R2 was done before R1 
	%member(X, List), subsumes_term(X, H) ->    % can cause loops  
		add_new_elements(Rest, List, NewList);
		add_new_elements(Rest, [H | List], NewList).

add_new_elements([], List, List).


add_new_elements_in_the_end([H | Rest], List, NewList) :-
	member(H, List) ->
		add_new_elements_in_the_end(Rest, List, NewList);
		append(List, [H], TempList),
		add_new_elements_in_the_end(Rest, TempList, NewList).

add_new_elements_in_the_end([], List, List).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% list_of_atoms(List)
% True if List is a list of atoms
list_of_atoms([H | Rest]) :-
	!,	atom(H),
	list_of_atoms(Rest).

list_of_atoms([]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% Maps Arg to Val if it is found in list
map(Arg, Val, [H | Rest]) :-
	nonvar(H),
	nonvar(Arg),
	( H =.. [_, Arg1, Val], Arg == Arg1 -> 
		true
	; map(Arg, Val, Rest)
	).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% list_of_atoms(List)
% True if List is a list of atoms
tt_atomList_to_atomList([(T,_) | TT_Rest], [NewT | Rest]) :-
	!,	( atom(T), NewT = T;
		  T = tlp(_,NewT,_,_,_) ), !,
	tt_atomList_to_atomList(TT_Rest, Rest).

tt_atomList_to_atomList([], []).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Convert nonvar TTexpression to TTterm
ttExp_to_ttTerm_info(TT1, TT2, Info) :-
	ttExp_to_ttTerm(TT1, TT2) -> 
		true;
	write('Typing error in: '),
	writeln(Info),
	fail.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Convert nonvar TTexpression to TTterm
ttExp_to_ttTerm(TTExp, TT) :-
	ttExp_to_ttTerm_pred(TTExp, TT, [], _) -> 
		true;
		writeln('Error in ttExp_to_ttTerm'), 
		fail.
	



ttExp_to_ttTerm_pred(Var, TTVar, Map, Map) :-
	var(Var), !,
	map(Var, TTVar, Map).
	

ttExp_to_ttTerm_pred((TTexp, TypeExp), (NewTTexp, Type), Map, Map) :-
	!,
	typeExp_to_type(TypeExp, Type),
	( atom(TTexp), pure_constant(TTexp) ->
		NewTTexp = tlp(TTexp,TTexp,na,na,na)  % new tlp format in prover
		%typeExp_to_type(TypeExp, Type)
	; TTexp = (Atom, POS), atom(Atom) ->
		NewTTexp = tlp(Atom,Atom,POS,na,na)
    ; NewTTexp = TTexp
		%Type = TypeExp  
	).	
		

ttExp_to_ttTerm_pred(Const, (TLP, Type), Map, Map) :-
	atom(Const), !,
	(  Const :: Type :: _
	%;  report('Unknown term: ', (Const, Type)), fail
	),
	TLP = tlp(Const,Const,na,na,na). % new tlp format in prover

ttExp_to_ttTerm_pred(TTexp1 @ TTexp2, TTterm, Map, Map) :-
	!, ttExp_to_ttTerm_pred(TTexp1, (Temp_TTexp, Type1), Map, Map),
	ttExp_to_ttTerm_pred(TTexp2, TTterm2, Map, Map),
	TTterm2 = (_, Type2),
	match_arg_type(Type1, Type2, ValType),
	TTterm = ((Temp_TTexp, Type1) @ TTterm2, ValType).

ttExp_to_ttTerm_pred(abst(Var, TTexp1), TTterm, Map, Map) :-
	!, ( var(Var) -> 
			TTVar = (Var, Type2),
				Map1 = [Var::TTVar | Map];
			Map1 = Map,
				TTVar = Var,
				Var = (_, Type2) ),	
	ttExp_to_ttTerm_pred(TTexp1, TTterm1, Map1, _),
	TTterm1 = (_, Type1),
	TTterm = (abst(TTVar, TTterm1), Type2 ~> Type1).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% matches two terms if they are different only in cases of chars
match_lowerCase(A, A) :-
	!.

match_lowerCase(A, B) :-
	term_to_atom(A, A1),
	atomic_list_concat(ListA1, '\'', A1),
	atomic_list_concat(ListA1, A2),
	term_to_atom(B, B1),
	atomic_list_concat(ListB1, '\'', B1),
	atomic_list_concat(ListB1, B2),
	downcase_atom(A2, A3),
	downcase_atom(B2, A3).
	


	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% choose element

choose([H|Rest], H, Rest).

choose([H|Rest], C, [H|Rest1]) :-
	choose(Rest, C, Rest1).


/*
choose(List, El, Rest) :-
	append(R1, [El | R2], List),
	append(R1, R2, Rest).
*/

true_choose([H|Rest], C, Rest) :-
	H == C.

true_choose([H|Rest], C, [H|Rest1]) :-
	true_choose(Rest, C, Rest1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% shuffle a list
shuffle_list([], []).

shuffle_list(List, [C|Shuff]) :-
	choose(List, C, Rest),	
	shuffle_list(Rest, Shuff).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% C1 is replaced by C2 in Nodes and results in NewNodes
list_substitution([H|T], C1, C2, [New_H|New_T]) :-
	substitution(H, C1, C2, New_H),
	%H = ndid(nd(TTterm, Args, X),Id),
	%substitute_tt(C1, C2, H, New_H),
	list_substitution(T, C1, C2, New_T).

list_substitution([], _, _, []). 

substitution(Term, C1, C2, New_Term) :-
	term_to_atom(Term, Atom_Term),
	term_to_atom(C1, Atom_C1),
	term_to_atom(C2, Atom_C2),
	atomic_list_concat(List, Atom_C1, Atom_Term),
	atomic_list_concat(List, Atom_C2, Atom_New_Term),
	atom_to_term(Atom_New_Term, New_Term, _).

% substitutes Old by New in Atom and unifies result with Result
substitute_in_atom(Atom, Old, New, Result) :-
	atomic_list_concat(List, Old, Atom),
	atomic_list_concat(List, New, Result).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% pair elements of two lists
two_lists_to_pair_list([H1|Rest1], [H2|Rest2], [H1,H2|Rest]) :-
	!,
	two_lists_to_pair_list(Rest1, Rest2, Rest).

two_lists_to_pair_list([], [], []).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% A1,...,An + B1,...,Bn = A1-B1,...,An-Bn
two_lists_to_list_of_pairs([H1|Rest1], [H2|Rest2], [H1-H2|Rest]) :-
	!,
	two_lists_to_list_of_pairs(Rest1, Rest2, Rest).

two_lists_to_list_of_pairs([], [], []).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% pair elements of two lists
append_element_to_list(List1, X, List2) :-
	append(List1, [X], List2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% pair elements of two lists:
% [t(a1,a2,a3), t(b1,b2,b3), t(c1,c2,c3)] -> [[a1,b1,c1], [a2,b2,c2], [a3,b3,c3]]
list_of_tuples_to_list_of_positions([], []).

list_of_tuples_to_list_of_positions([H_Tuple | Rest_Tuple], List_Poses) :-
	H_Tuple =.. [_| Elements],
	length(Elements, Len),
	length(Init_Poses, Len),
	maplist(=([]), Init_Poses),
	list_of_tuples_to_list_of_positions_step([H_Tuple | Rest_Tuple], Init_Poses, List_Poses), 
	!.

list_of_tuples_to_list_of_positions_step([], X, X).

list_of_tuples_to_list_of_positions_step( [H_Tuple | Rest_Tuple], List_Pos_0, List_Pos) :-
	H_Tuple =.. [_| Elements],
	maplist(append_element_to_list, List_Pos_0, Elements, List_Pos_1),
	list_of_tuples_to_list_of_positions_step( Rest_Tuple, List_Pos_1, List_Pos). 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% extract a sublist from a list
sublist_from_list(Start, Length, List, _) :-
	End is Start + Length,
	length(List, Len),
	End > Len,
	!, fail.

sublist_from_list(Start, Length, List, SubList) :-
	append(List1, List2, List),
	length(List1, Start),
	append(SubList, _, List2),
	length(SubList, Length),
	!.
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 'A@B' for alignment
pure_constant(Atom) :-	
	atomic_list_concat(X, '@', Atom),
	X = [_].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checks if ttTerm is a constant term
const_ttTerm((TTexp, _Type)) :-
	( atom(TTexp)
	; TTexp =.. [tlp | _]
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% unrelated lexical ttTerms
no_isa_rel_const_ttTerms(TT1, TT2, KB) :-
	TT1 = (tlp(_,Lm1,_,_,_),Ty1),
	TT2 = (tlp(_,Lm2,_,_,_),Ty2),
	sub_type(Ty1, Type),
	sub_type(Ty2, Type),
	nonvar(Lm1),
	nonvar(Lm2),
	\+isa(Lm1, Lm2, KB),
	\+isa(Lm2, Lm1, KB).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% random at most N-picks from the list
at_most_n_random_members_from_list(List, N, List) :-
	length(List, Length),
	N >= Length,
	!.
	
at_most_n_random_members_from_list(List, N, RandList) :-
	length(List, Length),
	randseq(N, Length, NumList),
	findall(RandEl, 
			( member(Index, NumList),
		  	  nth1(Index, List, RandEl) ),
			RandList).
		
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% compare cardinals and quantors
% e.g. is_greater(a_few, one); is_greater(7,5)
is_greater(A, B) :-
	text_to_number(A, A1),
	text_to_number(B, B1),
	!,
	A1 > B1.
	
is_greater('a_few', B) :-
	text_to_number(B, B1),
	!,
	%once( (B1 = 1; B1 = 0) ). % due to Fracas-107 and 109, explosion happens
	B1 = 0.
		
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% build a list of N length with all elements matching a term
repetition_list(X, N, List) :-
 	length(List, N), 
	maplist(=(X), List).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Problem IDs to sentence IDs
probID_to_senID(ProbID, SenIDs) :-
	findall(ID, sen_id(ID,ProbID,_,_,_), SenIDs).

probIDs_to_senIDs(ProbIDs, SenIDs) :-
	findall(ID, 
		(member(PrID, ProbIDs), sen_id(ID,PrID,_,_,_)), 
		SenIDs).

senID_to_probID(SenID, ProbID) :-
	sen_id(SenID,ProbID,_,_,_), 
	!.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% print a list with each element on a new line
writeln_list([]).

writeln_list([H | Rest]) :- 
	writeln(H),
	writeln_list(Rest).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% print a problem
print_prob(ID) :-
	findall(S, sen_id(_,ID,_,_,S), List),
	once(sen_id(_,ID,_,Ans,_)),
	report([ID, ': ', Ans]),
	maplist(writeln, List). 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% generate a set of all pairs from a set
all_pairs_from_set(Set, Pairs) :-
	%length(Lexicon, Len),
	findall((A, B), 
	  ( nth1(N1, Set, X),
		nth1(N2, Set, Y), 
		N1 < N2,
		X \= Y,
		sort([X,Y], [A,B]) %alphabetical order
	  ),
	  Pairs). 
		

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% a sequence of fixed number of indexed atoms
% a, 10 -> a1, a2, a3, ..., a10
indexed_atom_list(At, N, List) :-
	indexed_atom_list_(At, N, RevList),
	reverse(RevList, List).

indexed_atom_list_(_, 0, []) :- !.

indexed_atom_list_(At, N, [At_N | Rest]) :-
	!,
	atomic_list_concat([At, N], At_N),
	M is N - 1,
	indexed_atom_list_(At, M, Rest).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% rename free variables with indexed atoms
free_vars_to_indexed_atoms(At, A, B) :-
	copy_term(A, B),
	term_variables(B, Vars),
	length(Vars, N),
	indexed_atom_list(At, N, Vars).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Projection of argument
nth1_projection(N, Term, Proj) :-
	Term =.. [_|List],
	nth1(N, List, Proj).
	









