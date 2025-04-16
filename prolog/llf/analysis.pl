%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  predicates for analyzing trees
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%==================================
:- use_module('ccg_term', [
	ccgTree_to_ccgTerm/2, get_lex_categories/2,
    op(601, xfx, (/)), op(601, xfx, (\))
	]).
:- use_module('../lambda/lambda_tt', [
	op(605, xfy, ~>), op(605, yfx, @)
	]).
%==================================


get_all_lex_types(FreqPairs) :-
    findall(Types, (
        ccg(_ID, CGGTree),
        ccgTree_to_ccgTerm(CGGTree, Term),
        get_lex_types(Term, Types1),
        maplist(ignore_type_features, Types1, Types)
    ), List_of_types),
    append(List_of_types, AllTypes),
    msort(AllTypes, Sorted),
    clumped(Sorted, FreqPairs).


get_all_lex_categories(FreqPairs) :-
    findall(Cats, (
        ccg(_ID, CGGTree),
        get_lex_categories(CGGTree, Cats1),
        maplist(ignore_category_features, Cats1, Cats2),
        maplist(replace_modifier_categories, Cats2, Cats)
    ), List_of_cats),
    append(List_of_cats, AllCats),
    msort(AllCats, Sorted),
    clumped(Sorted, FreqPairs).



%--------------------------------------
% get lexical types from a term
%--------------------------------------
get_lex_types(TTterm, _) :-
    var(TTterm), !, fail.

get_lex_types((TT1@TT2,_), Types) :- !,
    get_lex_types(TT1, Types1),
    get_lex_types(TT2, Types2),
    append([Types1, Types2], Types).

get_lex_types((abst(TTX,SubTTterm),_), Types) :- !,
    get_lex_types(TTX, Types1),
    get_lex_types(SubTTterm, Types2),
    append([Types1, Types2], Types).

get_lex_types((TLP,Type), [Type]) :-
    TLP =.. [tlp|_], !.

get_lex_types((X,Type), [Type]) :-
    var(X), !.

get_lex_types((TTterm,_), Types) :-
    get_lex_types(TTterm, Types). 
%--------------------------------------

%-------------------------------------
% Ignore features in a type
%-------------------------------------
ignore_type_features(Type, _) :-
    var(Type), !, fail.

ignore_type_features(A~>B, A1~>B1) :- !,
    ignore_type_features(A, A1),
    ignore_type_features(B, B1).

ignore_type_features(A, A) :-
    atom(A), !.

ignore_type_features(A:_F, A) :- !.
%-------------------------------------

%-------------------------------------
% Ignore features in CCG categories
%-------------------------------------
ignore_category_features(Cat, _) :-
    var(Cat), !, fail.

ignore_category_features(A_B, A1_B1) :- 
    A_B =.. [Slash, A, B], 
    memberchk(Slash, ['/', '\\']), !,
    ignore_category_features(A, A1),
    ignore_category_features(B, B1),
    A1_B1 =.. [Slash, A1, B1]. 

ignore_category_features(A, A) :-
    atom(A), !.

ignore_category_features(A:_F, A) :- !.
%-------------------------------------

%-------------------------------------
% Replace modifier subcategories
%-------------------------------------
replace_modifier_categories(Cat, _) :-
    var(Cat), !, fail.

replace_modifier_categories(A_A, Mod) :- 
    A_A =.. [Slash, A, A], 
    memberchk(Slash, ['/', '\\']), !, 
    Mod =.. [Slash, 'X', 'X']. 

replace_modifier_categories(A_B, A1_B1) :- 
    A_B =.. [Slash, A, B], 
    memberchk(Slash, ['/', '\\']), !,
    replace_modifier_categories(A, A1),
    replace_modifier_categories(B, B1),
    A1_B1 =.. [Slash, A1, B1]. 

replace_modifier_categories(A, A) :- !.
%-------------------------------------