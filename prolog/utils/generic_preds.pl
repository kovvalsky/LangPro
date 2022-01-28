%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Generic Predicates
% These user defined predicates require no additional modules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module('generic_preds',
	[
		all_member_zip/2,
		dictList_to_dictPosition/2,
		filepath_write_source/2,
		format_list/3,
		format_list_list/3,
		format_list_list/4,
		get_cmd/1,
		keep_smallest_lists/2,
		list_product/3,
		list_to_set_variant/2,
		list_to_ord_set_variant/2,
		list_atom/2,
		member_zip/2,
		read_dict_from_json_file/2,
		rotate_list/2,
		scalar_x_list/3,
		symmdiff_variant/3,
		sort_list_length/2,
		sublist_of_list/2,
		substitute_in_atom/4,
		true_member/2
	]).

:- use_module(library(http/json)).
:- use_module(library(yall)). % added as conccurent runs sometimes throw errors

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% true_member(Element, List)
% checks if Element is bound with the member of List
% also avoids binding variables of List
true_member(E, List) :-
	nonvar(List),
	List = [Head | Rest],
	( E == Head % fixed
	; true_member(E, Rest) ).

variant_member(E, List) :-
	nonvar(List),
	List = [Head | Rest],
	( E =@= Head % fixed
	; variant_member(E, Rest) ).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Each member of list is formatted accordingly and sent to Source
format_list(Source, Format, List) :-
	findall(A, (
		member(E, List),
		format(atom(A), Format, [E])
	), As),
	atomic_list_concat(As, Message),
	format(Source, '~w', [Message]).

% Each list member is formatted accordingly and sent to Source
format_list_list(Source, Format, List_of_Lists) :-
	findall(A, (
		member(List, List_of_Lists),
		format(atom(A), Format, List)
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
	maplist([A,B,A-B]>>true, _Len, Sorted, Sorted_Length_List).


% read dictionary from json file
read_dict_from_json_file(JSON, Dict) :-
    open(JSON, read, S, [encoding(utf8), close_on_abort(true)]),
    json_read_dict(S, Dict, [value_string_as(atom), default_tag(j)]).


% substitutes Old by New in Atom and unifies result with Result
substitute_in_atom(Atom, Old, New, Result) :-
	atomic_list_concat(List, Old, Atom),
	atomic_list_concat(List, New, Result).


% rotate the list
rotate_list(L, R) :-
	rotate_list(L, R, 0).

rotate_list(L, L, N) :-
	length(L, Len),
	N =< Len.

rotate_list([H|Rest], Rotate2, N) :-
	length([H|Rest], Len),
	N < Len - 1,
	append(Rest, [H], Rotate1),
	N1 is N + 1,
	rotate_list(Rotate1, Rotate2, N1).


list_atom(List_or_Atom, Atom) :-
	is_list(List_or_Atom) ->
		atomic_list_concat(List_or_Atom, Atom)
	; Atom = List_or_Atom.

% create a source for a given filepath
filepath_write_source(FilePath, S) :-
    file_directory_name(FilePath, Dir),
    ( exists_directory(Dir) -> true; make_directory_path(Dir) ),
    open(FilePath, write, S, [encoding(utf8), close_on_abort(true)]).


% convert key->list structure into key->list_el->position
dictList_to_dictPosition(DictList, DictPos) :-
	dict_pairs(DictList, _, Pairs),
	maplist([K-L, K-D]>>list_to_dict(L,D), Pairs, Pairs1),
	dict_pairs(DictPos, d, Pairs1).

% convert list to a dictionary of elements to their positions
list_to_dict(List, El_Index) :-
	findall(E-I, nth1(I, List, E), E_I_List),
	dict_create(El_Index, d, E_I_List).


% member with N dimension
member_zip(E_List, ListOfList) :-
	maplist([L,E]>>member(E,L), ListOfList, E_List).


% all members obtained with member_zip
all_member_zip(ListOfList, AllMemberList) :-
	findall(MemberList, member_zip(MemberList, ListOfList), AllMemberList).


% from list to set but with checking on unification
% this is different from list_to_set that uses ==
list_to_set_variant([], []) :- !.

list_to_set_variant([H|T], S) :-
	( variant_member(H, T) ->
	  list_to_set_variant(T, S)
	; list_to_set_variant(T, S1),
	  S = [H|S1] ).


list_to_ord_set_variant(L, S) :-
	list_to_set_variant(L, V),
	sort(V, S).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% variant based subtraction and symmetric difference

% delete from L elements that are variant to some element in D, result is R
subtract_variant(L, D, R) :-
	include({D}/[E]>>(\+variant_member(E,D)), L, R).

symmdiff_variant(A, B, D) :-
	subtract_variant(A, B, A_B),
	subtract_variant(B, A, B_A),
	append(A_B, B_A, D).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% get a self-command
get_cmd(CMD) :-
	current_prolog_flag(os_argv, Options),
	atomic_list_concat(Options, ' ', CMD).


% cartesian product of two lists
list_product(L1, L2, Prod) :-
	findall(E1-E2, (
		member(E1, L1),
		member(E2, L2)
	), Prod).

% multiply list elements on a scalar
scalar_x_list(Scalar, List, Result) :-
	maplist({Scalar}/[L,R]>>(R is Scalar*L), List, Result).
