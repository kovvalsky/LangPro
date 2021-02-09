%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Generic Predicates
% These user defined predicates require no additional modules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module('user_preds',
	[
		format_list/3,
		format_list_list/3,
		format_list_list/4,
		true_member/2
	]).

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
