%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: Tableau Prover for Natural Logic
%     Version: 12.06.12
%      Author: lasha.abzianidze{at}gmail.com
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module('user_preds',
	[
		add_new_elements/3,
		average_list/2,
		all_pairs_from_set/2,
		at_most_n_random_members_from_list/3,
		add/3, minus/3, diff/3,
		choose/3,
		concurrent_maplist_n_jobs/3,
		const_ttTerm/1,
		element_list_member/3,
		is_greater/2,
		get_value_def/3,
		keep_smallest_lists/2,
		listInt_to_id_ccgs/2,
		list_of_tuples_to_list_of_positions/2,
		list_substitution/4,
		list_to_freqList/2,
		freqList_subtract/3,
		format_list/3,
		format_list_list/4,
		list_to_set_using_match/2,
		match_lowerCase/2,
		neg/2,
		nth1_projection/3,
		no_isa_rel_const_ttTerms/3,
		probIDs_to_senIDs/2,
		print_prob/1,
		match_remove/3,
		pairwise_append/2,
		partition_list_into_N_even_lists/3,
		patt_remove/3,
		prob_input_to_list/2,
		prIDs_to_prIDs_Ans/2,
		all_prIDs_Ans/1,
		true_remove/3,
		remove_adjacent_duplicates/2,
		uList2List/2,
		substitute_in_atom/4,
		shared_members/2,
		sort_list_length/2,
		sublist_of_list/2,
		sym_rels_to_canonical/2,
		term_list_concat/2,
		ttExp_to_ttTerm/2,
		ttExp_to_ttTerm_info/3,
		tt_mon_up/1,
		tt_mon/2,
		tt_atomList_to_atomList/2,
		true_member/2,
		two_lists_to_pair_list/3,
		two_lists_to_pairList/3,
		ul_append/2,
		ul_append_ul/2,
		ul_member/2,
		is_uList/1,
		writeln_list/1
	]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%    Generic User Defined Predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module('../knowledge/lexicon', [op(640, xfy, ::), '::'/2]).
:- use_module('../knowledge/ling', [text_to_number/2]).
:- use_module('../lambda/lambda_tt', [op(605, xfy, ~>),	op(605, yfx, @)]).
:- use_module('../lambda/type_hierarchy', [
	sub_type/2, typeExp_to_type/2, match_arg_type/3
	]).
:- use_module('../knowledge/knowledge', [isa/3]).
:- use_module('../printer/reporting', [report/1]).

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
	( subsumes_term(Head, E)  % member subsumes an element
	; subsumes_member(E, Rest)
	), !.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Predicates for unspecified lists = list with an unbound final tail
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% unspecified list member
ul_member(E, [Head | Rest]) :-
	nonvar(Head),
	( Head = E
	; ul_member(E, Rest)
	).

% append list to unspecified list
ul_append(UList, List) :-
	nonvar(UList),
	!,
	UList = [_ | Rest],
	ul_append(Rest, List).

ul_append(UList, List) :-
	var(UList),
	!,
	once(append(List, _, UList)).

% adds a new element to UL if the element is not there
% if element is there fail
add_new_to_ul(New, UL) :-
	\+ul_member(New, UL),
	ul_append(UL, [New]).

ul_append_ul(MainUList, UList) :-
	uList2List(UList, List),
	ul_append(MainUList, List).

uList2List(UList, List) :-
	append(List, Var, UList),
	var(Var), !.

is_uList(UList) :-
	append(_, Var, UList),
	var(Var),
	!.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
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
% can be used delete/3 also but it is depricated I guess

match_remove(E, [H | T], NewList) :-
	E = H,
	!,
	match_remove(E, T, NewList).

match_remove(E, [H | T], [H | NewList]) :-
	!,
	match_remove(E, T, NewList).

match_remove(_, [], []).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
patt_remove(E, [H | T], NewList) :-
	\+ E \= H, % just checks for matching but does not match it
	!,
	patt_remove(E, T, NewList).

patt_remove(E, [H | T], [H | NewList]) :-
	!,
	patt_remove(E, T, NewList).

patt_remove(_, [], []).



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
		add_new_elements(Rest, List, NewList)
	; 	add_new_elements(Rest, [H | List], NewList).

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
% get all elements shared by a set of lists
shared_members(Members, Lists) :-
    Lists = [] ->
      Members = []
    ; findall(M, (maplist(member(M), Lists)), Members).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% get all elements shared by a set of lists
element_list_member(List_of_Lists, List, List_Element) :-
	member(List_Element, List_of_Lists),
	sublist_of_list(List_Element, List).

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
two_lists_to_pairList([H1|Rest1], [H2|Rest2], [(H1,H2)|Rest]) :-
	!,
	two_lists_to_pairList(Rest1, Rest2, Rest).

two_lists_to_pairList([], [], []).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% A1,...,An + B1,...,Bn = A1-B1,...,An-Bn
two_lists_to_pair_list([H1|Rest1], [H2|Rest2], [H1-H2|Rest]) :-
	!,
	two_lists_to_pair_list(Rest1, Rest2, Rest).

two_lists_to_pair_list([], [], []).



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
no_isa_rel_const_ttTerms(TT1, TT2, KB_xp) :-
	TT1 = (tlp(_,Lm1,_,_,_),Ty1),
	TT2 = (tlp(_,Lm2,_,_,_),Ty2),
	sub_type(Ty1, Type),
	sub_type(Ty2, Type),
	nonvar(Lm1),
	nonvar(Lm2),
	\+isa(Lm1, Lm2, KB_xp),
	\+isa(Lm2, Lm1, KB_xp).


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
% print a list with each element on a new line
writeln_list([]) :- !.

writeln_list([H | Rest]) :-
	writeln(H),
	writeln_list(Rest).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Each member of list is formatted accordingly and sent to Source
format_list(Source, Format, List) :-
	findall(A, (
		member(E, List),
		format(atom(A), Format, [E])
	), As),
	atomic_list_concat(As, Message),
	format(Source, '~w', [Message]).

% Each member list of list is formatted as Format1
% and its elements are formatted as Format2 and sent to Source
format_list_list(Source, Format1, Format2, List_of_Lists) :-
	findall(A1, (
		member(List, List_of_Lists),
		format_list(atom(A2), Format2, List),
		format(atom(A1), Format1, [A2])
	), As),
	atomic_list_concat(As, Message),
	format(Source, '~w', [Message]).

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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% returns sentence id list from problem id list or vice versa
probIDs_to_senIDs([Prob_ID | Prob_Rest], Sen_IDs) :-
	!, findall(ID, sen_id(ID, Prob_ID,_,_,_), IDs),
	probIDs_to_senIDs(Prob_Rest, Sen_Rest),
	append(IDs, Sen_Rest, Sen_IDs).

probIDs_to_senIDs([], []).

senID_to_probID(SenID, ProbID) :-
	sen_id(SenID,ProbID,_,_,_),
	!.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% List_Int of senIDs into a list of (ID, CCG tree)-s
listInt_to_id_ccgs(List_Int, CCGs) :-
	( is_list(List_Int) ->
		findall(ccg(Id, Tree), (member(Id, List_Int), ccg(Id, Tree)), CCGs)
	; List_Int = Inf-Sup ->
		( nonvar(Inf), nonvar(Sup) -> findall(ccg(Id, Tree), (between(Inf, Sup, Id), ccg(Id, Tree)) , CCGs);
	 	  nonvar(Inf) -> findall(ccg(Id, Tree), (ccg(Id, Tree), Inf =< Id), CCGs);
		  nonvar(Sup) -> findall(ccg(Id, Tree), (ccg(Id, Tree), Sup >= Id), CCGs);
	 	  findall(ccg(Id, Tree), ccg(Id, Tree), CCGs)
		)
	; report(["Error: Wrong format of the argument: ", List_Int]),
	  fail
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Various input for problem IDs to list of problem _IDs
prob_input_to_list(Input, List) :-
	( var(Input) ->
		findall(X, sen_id(_,X,'h',_,_), List)
	; is_list(Input) ->
		List = Input
	; integer(Input) ->
		List = [Input]
	; Input = Inf-Sup ->
		( integer(Inf), integer(Sup) ->
			findall(X, (sen_id(_,X,'h',_,_), between(Inf,Sup,X)), List)
		; var(Inf), integer(Sup) ->
			findall(X, (sen_id(_,X,'h',_,_), X =< Sup), List)
		; integer(Inf), var(Sup) ->
				findall(X, (sen_id(_,X,'h',_,_), Inf =< X), List)
		)
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% List to sorted frequency list. List expected not to have free variables
% Freq list has element-count as its members
list_to_freqList(List, Freq) :-
	list_to_freqList(List, [], Freq).

list_to_freqList([], FL, FL) :- !.

list_to_freqList([E | Rest], FL1, FL2) :-
	selectchk(E-N, FL1, RestFL1),
	!,
	N1 is N + 1,
	list_to_freqList(Rest, [E-N1 | RestFL1], FL2).

list_to_freqList([E | Rest], FL1, FL2) :-
	list_to_freqList(Rest, [E-1 | FL1], FL2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% It is assumed that there are no elements with th3 same key in FreqList
% SubFL = { key:cnt | key in FL & val = FL[key] - (DelFL[key], def=0) > 0
freqList_subtract([], _DelFL, []) :- !.

freqList_subtract([Key-X | FL], DelFL, SubFL) :-
	memberchk(Key-Y, DelFL),
	!,
	( X > Y ->
		Z is X - Y,
		freqList_subtract(FL, DelFL, SubFL1),
		SubFL = [ Key-Z | SubFL1]
	;	freqList_subtract(FL, DelFL, SubFL)
	).

freqList_subtract([Key-X | FL], DelFL, [Key-X | SubFL]) :-
	freqList_subtract(FL, DelFL, SubFL).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% removes duplicates of symmetric predicates from the ord_list
% result is again an ord_list
rm_sym_preds_from_ord([], []).

rm_sym_preds_from_ord([H1|Rest], [H1|List]) :-
	H1 =.. [Pred, Arg1, Arg2],
	( memberchk(Pred, [disj]) -> % list of symmetric predicates
	    H2 =.. [Pred, Arg2, Arg1],
		select(H2, Rest, RestRest),
		!,
		rm_sym_preds_from_ord(RestRest, List)
	  ; List = Rest
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% for a list of relations, set a canonical order for symetric relations
sym_rels_to_canonical([], []) :- !.

sym_rels_to_canonical([R | Rels], [C | Cano_Rels]) :-
	R =.. [Pred, Arg1, Arg2],
	( memberchk(Pred, [disj, ant_wn]), Arg2 @=< Arg1 -> % list of symmetric predicates
		C =.. [Pred, Arg2, Arg1]
	; C = R ),
	sym_rels_to_canonical(Rels, Cano_Rels).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Given a list of lists, keep only those lists that are smallest,
% not set-containing other lists
keep_smallest_lists(List_of_Lists, Smallest_Lists) :-
	findall(List, (
		member(List, List_of_Lists),
		\+(( member(L, List_of_Lists),
			L \= List,
			sublist_of_list(L, List)
		  ))
	),	Smallest_Lists).


% All elements of the first list are elemenst of the second list
sublist_of_list([], _) :- !.

sublist_of_list([X|Rest], L) :- !,
	memberchk(X, L),
	sublist_of_list(Rest, L).

% sort list of lists according to length
sort_list_length(List_of_lists, Sorted) :-
	findall(Len-List, (
		member(List,List_of_lists), length(List, Len)
		), Length_List),
	keysort(Length_List, Sorted_Length_List),
	two_lists_to_pair_list(_Len, Sorted, Sorted_Length_List).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% chop list into N comparable parts
% used for creating jobs for concurrent computing, where N is the number of cores
% chopping keeps the order of elements: [1,2,3,4,5,6,7] -> [1,4.7], [2,5], [3,6]
% Predicate works in the reversed order too: get list from partitions
partition_list_into_N_even_lists(List, N, Partition) :-
	length(Partition, N),
	distribute_list_in_bins(List, Partition).

distribute_list_in_bins(EmptyList, EmptyBins) :-
	( var(EmptyList)
	; EmptyList == []
	),
	maplist(=([]), EmptyBins),
	!,
	EmptyList = [].

distribute_list_in_bins([E | List], [[E|B] | Bins]) :-
	append(Bins, [B], Bins_B),
	distribute_list_in_bins(List, Bins_B).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Append list of lists pairwise
% [[aa,...,az], [za,...,zz]] -> [aa+...+za,...az+...+zz]
pairwise_append([], []) :- !.

pairwise_append([LL|LLL], List_of_Nth_List) :-
	findall(Nth_List, (
		nth1(N, LL, _),
		maplist(nth1(N), [LL|LLL], Nth_LLs),
		append(Nth_LLs, Nth_List)
	), List_of_Nth_List).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Break arguments into parts for concyrrent maplist
concurrent_maplist_n_jobs(Functor, Inputs, Outputs) :-
	debMode(parallel(N)), !,
	partition_list_into_N_even_lists(Inputs, N, Job_List_Input),
	concurrent_maplist(maplist(Functor), Job_List_Input, Job_List_Output),
	partition_list_into_N_even_lists(Outputs, N, Job_List_Output).

concurrent_maplist_n_jobs(Functor, Inputs, Outputs) :-
	maplist(Functor, Inputs, Outputs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Given a list of Problem IDs, return a list of Problem ID and answer pairs
prIDs_to_prIDs_Ans(PrIDs, PrIDs_Ans) :-
	findall(PrID-Ans, (
		member(PrID, PrIDs),
		sen_id(_, PrID, 'h', Ans, _)
		), PrIDs_Ans).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
all_prIDs_Ans(PrIDs_Ans) :-
	findall((PrID,Ans), (
		sen_id(_,PrID,'h',Answer,_),
		( pid_labs(PrID, KeyLabs), debMode(lab_map(Key)) ->
			memberchk(Key-Ans, KeyLabs)
		; Ans = Answer )
	), PrIDs_Ans).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Macros for arithmetic operations
add(X, Y, Z) :-
	Z is X + Y.

minus(X, Y, Z) :-
	Z is X - Y.

diff(X, Y, Z) :-
	T is X - Y,
	abs(T, Z).

average_list(List, Average) :-
	length(List, N),
	sum_list(List, Sum),
	Average is Sum/N.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Get parameter value from key-value list
% Either key-value is there or only key
get_value_def(KeyVals, Key, Value) :-
	memberchk(Key-Value, KeyVals),
	!.

% If only key is there, this means that the key is Boolean
% Its existence results in true value and vice versa
get_value_def(KeyVals, Key, Value) :-
	( memberchk(Key, KeyVals) ->
		Value = true
	;	Value = false
	), !.
 % it is possible to add default values for some keys
