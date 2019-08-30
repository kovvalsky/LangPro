%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module('type_hierarchy',
	[
		cat_eq/2,
		final_value_of_type/2,
		set_final_value_of_type/3,
		luc/3,
		sub_type/2,
		typeExp_to_type/2,
		match_arg_type/3,
		general_cat/2
	]).
	
:- use_module('../printer/reporting', [report/1]).
:- use_module('lambda_tt', [op(605, xfy, ~>)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% least upper category
luc(X, Y, _) :-
	( var(X); var(Y)), !, fail.

luc(A1~>B1, A2~>B2, A~>B) :-
	!,
	glc(A1, A2, A),
	luc(B1, B2, B).

luc(A1~>A2, B, C1~>C2) :-
	!,
	sub_type(B, B1~>B2),
	luc(A1~>A2, B1~>B2, C1~>C2).

luc(A, B1~>B2, C1~>C2) :-
	!,
	sub_type(A, A1~>A2),
	luc(A1~>A2, B1~>B2, C1~>C2).

/*luc(X, Y, Z) :-        
	X \=.. ['~>'|_],
	( X = Y -> 
		Z = X
	; X = A:_, 
	  Y = A:_, 
	  Z = A:_
	),
	!.*/

luc(X, Y, Y) :- 
	sub_type(X, Y), !.

luc(X, Y, X) :- 
	sub_type(Y, X), !.

% greates lower category
glc(X, Y, _) :-
	( var(X); var(Y)), !, fail.

glc(A1~>B1, A2~>B2, A~>B) :-
	!,
	luc(A1, A2, A),
	glc(B1, B2, B).

glc(A1~>A2, B, C1~>C2) :-
	!,
	sub_type(B1~>B2, B),
	glc(A1~>A2, B1~>B2, C1~>C2).

glc(A, B1~>B2, C1~>C2) :-
	!,
	sub_type(A1~>A2, A),
	glc(A1~>A2, B1~>B2, C1~>C2).

/*glc(X, Y, Z) :-
	\+ X =.. ['~>'|_],
	( X = Y -> 
		Z = X
	; X = A:_, 
	  Y = A:_, 
	  Z = A:_
	),
	!.*/

glc(X, Y, X) :- 
	sub_type(X, Y), !.

glc(X, Y, Y) :- 
	sub_type(Y, X), !.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% sub_type(A, B)
sub_type(A, B) :-
	sub_type_(A, B).

sub_type_(A, B) :-
	var(A), var(B), 
	!,
	report(['Error: unexpected variable types passed to sub_type_/2']),
	fail.

sub_type_(A~>B, X~>Y) :-
	%sub_type(A, X),
	sub_type(X, A),
	sub_type(B, Y).

%sub_type_(X, X).
sub_type_(X, X) :-
	\+ X =.. ['~>'|_].  

% ignoring features, e.g. S:dcl is subtype of S:adj 
sub_type_(X:_, X:_).

sub_type_(s:_, t).

%sub_type_(np:_, e).
sub_type_(e, np:_).

sub_type_(n:_, e~>t).

sub_type_(pp, e~>t).





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Equivalenve predicate over CCG categories ignoring features
cat_eq(A, B) :- % binds categories
	ccgCat_ccgCat(A, B), !.

ccgCat_ccgCat(X, Y) :-
	( var(X); 
	  var(Y) ), !,
	X == Y.

ccgCat_ccgCat(A~>B, X~>Y) :-
	ccgCat_ccgCat(A, X),
	ccgCat_ccgCat(B, Y).

ccgCat_ccgCat(A:_,A:_).

ccgCat_ccgCat(X, X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Returnes general category according to features
general_cat(Cat, X) :-
	general_cat_(Cat, X), !.

general_cat_(Cat, Cat) :-
	var(Cat), !.

general_cat_(A~>B, X~>Y) :-
	general_cat_(A, X),
	general_cat_(B, Y).

general_cat_(A:_, A:_).

general_cat_(X, X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%!!! Takes function type Type and argument type ArgTy
% makes sure that Type is applicapable to ArgTy and Rest is most specific value type
match_arg_type(Type, ArgTy, Rest) :-
	nonvar(Type),
	%general_cat(ArgTy, G_ArgTy),
	%Type = G_ArgTy ~> Rest.
	sub_type(Type, A~>Rest),
	sub_type(ArgTy, A),
	!.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% concise version of type to canonical version
typeExp_to_type(A~>B, Type_A~>Type_B) :-
	!,
	typeExp_to_type(A, Type_A),
	typeExp_to_type(B, Type_B).
	
typeExp_to_type(Atom, Type) :-
	atom(Atom), 
	!,
	( member(Atom, [n, s, np]) ->
		Type = Atom:_
	  ;	Type = Atom
	).

typeExp_to_type(A:F, A:F).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% final_value_of_type(Type, Value)
% Value is the final type of Type if the latter is fed completely	
final_value_of_type(Type, Value) :-
	Type = _ ~> B ->
		final_value_of_type(B, Value)
	;	Value = Type.

% sets final type of a type
set_final_value_of_type(Type, NewType, FinVal) :-
	Type = A ~> B ->
		set_final_value_of_type(B, NewB, FinVal),
		NewType = A ~> NewB  
	;	NewType = FinVal.



	












