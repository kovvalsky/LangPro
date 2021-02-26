%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Generic Predicates
% These user defined predicates require no additional modules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module('generic_preds',
	[
		format_list/3,
		format_list_list/3,
		format_list_list/4,
		keep_smallest_lists/2,
		read_dict_from_json_file/2,
		sort_list_length/2,
		sublist_of_list/2,
		true_member/2
	]).

:- use_module(library(http/json)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% true_member(Element, List)
% checks if Element is bound with the member of List
% also avoids binding variables of List
true_member(E, List) :-
	nonvar(List),
	List = [Head | Rest],
	( E == Head % fixed
	; true_member(E, Rest) ).


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
