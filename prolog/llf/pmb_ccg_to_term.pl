%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module(ccg_term, [
	ccgIDTree_to_ccgIDTerm/2,
	ccgTree_to_ccgTerm/2,
	cat2type/2,
	main/1,
	main/2,
	op(601, xfx, (/)),
	op(601, xfx, (\))
]).
%==================================
:- use_module('../lambda/lambda_tt', [
	norm_tt/2, op(605, xfy, ~>), op(605, yfx, @)
	]).
:- use_module(library(term_to_json), [
	term_to_json/2
	]).

:- dynamic ccg_id/1.
:- dynamic ccg_tree/1.
:- dynamic out_format/1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

main(Fmt, DocIDList) :-
	error_if_no_ccgs,
	forall(
		( ccg(ID, CCG), ID = DocID-_, memberchk(DocID, DocIDList) ),
		( ccgIDTree_to_ccgIDTerm(ccg(ID, CCG), ccg(ID, TTterm)) ->
		  pretty_vars_in_ttterm(1-1, _, TTterm, PrettyTT),
		  print_ccg_term(Fmt, ID, PrettyTT)
		; format(user_error, 'Conversion failed: ~w~n', [ID]) )
	),
	halt.

main(Fmt) :-
	main(Fmt, _DocIDList).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
error_if_no_ccgs :-
	ccg(_,_) -> true;
	format(user_error, 'Error: No CCG derivation was found', []),
	halt(1).

print_ccg_term(Fmt, ID, PrettyTT) :-
	( 'xml' = Fmt ->
	  print_ccg_term_as_xml(ID, PrettyTT)
	; 'json' = Fmt ->
	  print_ccg_term_as_json(ID, PrettyTT)
	; 'prolog' = Fmt ->
	  print_ccg_term_as_term(ID, PrettyTT)
	; format(user_error, 'Error: Unknown output format: ~w', [Fmt]), halt(1) ).


print_ccg_term_as_xml(ID, TTterm) :-
	current_output(STDOUT),
	format('<id_ttterm>~n<id>~w</id>~n', [ID]),
	ttTerm_to_xml(STDOUT, TTterm),
	format('</id_ttterm>~n', []).

print_ccg_term_as_json(ID, TTterm) :-
	term_to_json(id_type_term(ID, TTterm), Json_term),
	print_term(Json_term, []),
	nl.

print_ccg_term_as_term(ID, TTterm) :-
	format('ccg(~w,~n', [ID]),
	print_ttTerm_as_term(2, TTterm),
	write(').\n').


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ccgIDTree_to_ccgIDTerm(CCG_ID, Term_ID)
% Converts (ID, CCGTree) pair into (ID, CCGterm) pair
ccgIDTree_to_ccgIDTerm(ccg(ID, Tree), ccg(ID, NormTT)) :-
	retractall(ccg_id(_)),
	asserta(ccg_id(ID)),
	retractall(ccg_tree(_)),
	asserta(ccg_tree(Tree)),
	ccgTree_to_ccgTerm(Tree, TT),
	norm_tt(TT, NormTT).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ccgTree_to_ccgTerm(Tree, tcTree))
% Converts CCG Tree into CCG term: a pair of term and type
ccgTree_to_ccgTerm( t(Cat, Tok, Tags), (t(Tok, Tags), Type) ) :- !,
	cat2type(Cat, Type).

ccgTree_to_ccgTerm( lx(Cat, _, Tree), (TermType, Type) ) :- !,
	cat2type(Cat, Type),
	ccgTree_to_ccgTerm(Tree, TermType).

ccgTree_to_ccgTerm( Tree, (Term, Type) ) :-
	( Tree = tr(Cat, SubTree)		% CandC output
	; Tree = tr(Cat, _, SubTree)	% easyCCG output
	), !,
	cat2type(Cat, Type),
	Type = (CatArg ~> CatVal) ~> CatVal, % sanity check
	ccgTree_to_ccgTerm(SubTree, TermType),
	TT_X = (_Var, CatArg ~> CatVal),
	Term = abst(TT_X, (TT_X @ TermType, CatVal)).

ccgTree_to_ccgTerm( Tree, ((TT_A,Ty_B~>Type) @ (TT_B,Ty_B), Type) ) :-
	( Tree = fa(Cat, A, B)
	; Tree = ba(Cat, B, A)
	), !,
	cat2type(Cat, Type),
	ccgTree_to_ccgTerm(A, (TT_A,Ty_B~>Type)),
	ccgTree_to_ccgTerm(B, (TT_B,Ty_B)).

ccgTree_to_ccgTerm( Tree, (Term, Type) ) :-
	( Tree =  fc(Cat, A, B)
	; Tree =  bc(Cat, B, A)
	; Tree = fxc(Cat, A, B)
	; Tree = bxc(Cat, B, A)
	), !,
	cat2type(Cat, Type),
	Type = Cat_X ~> Cat_Val,
	TT_A = (_, Cat1 ~> Cat_Val),
	TT_B = (_, Cat_X ~> Cat1),
	ccgTree_to_ccgTerm(A, TT_A),
	ccgTree_to_ccgTerm(B, TT_B),
	TT_X = (_, Cat_X),
	Term = abst(TT_X, (TT_A @ (TT_B @ TT_X, Cat1), Cat_Val)).

ccgTree_to_ccgTerm( conj(Cat, Arg, A, B), (TT_A @ TT_B, Type) ) :- !,
	cat2type(Cat, Type),
	cat2type(Arg, ArgType),
	Type = ArgType ~> ArgType, % sanity check
	TT_A = (TA, ArgType ~> Type),
	TT_B = (_, ArgType), % sanity check
	ccgTree_to_ccgTerm(A, (TA, _)),
	ccgTree_to_ccgTerm(B, TT_B).

ccgTree_to_ccgTerm( conj(Cat, Conj, A), (TT_Conj @ TT_A, Type) ) :- !, % pmb parse tags
	cat2type(Cat, Type),
	Type = TyA ~> TyA, % sanity check
	TT_A = (_, TyA),
	TT_Conj = (_, TyA~>TyA~>TyA),
	ccgTree_to_ccgTerm(A, TT_A),
	ccgTree_to_ccgTerm(Conj, TT_Conj).

ccgTree_to_ccgTerm( Tree, ( (PTerm, Type1 ~> Type) @ (Term1, Type1), Type ) ) :-
	( Tree = lp(Cat, PTree, SubTree)
	; Tree = rp(Cat, SubTree, PTree)
	; Tree = ltc(Cat, PTree, SubTree) % CandC
	; Tree = rtc(Cat, SubTree, PTree) % CandC
	), !,
	cat2type(Cat, Type),
	ccgTree_to_ccgTerm(SubTree, (Term1, Type1)),
	ccgTree_to_ccgTerm(PTree, (PTerm, Type1 ~> Type)).

ccgTree_to_ccgTerm( Tree, (Term, Type) ) :-
	( Tree = gbxc(Cat, 2, A, B)
	; Tree = gbc(Cat, 2, A, B)
	; Tree = gbxc(Cat, A, B)
	; Tree = gbc(Cat, A, B)
	; Tree = gfxc(Cat, 2, B, A)
	; Tree = gfc(Cat, 2, B, A)
	; Tree = gfxc(Cat, B, A)
	; Tree = gfc(Cat, B, A)
	), !,
	cat2type(Cat, Type),
	Type = TyX ~> TyY ~> FinTyB,
	TT_A = (_, TyX ~> TyY ~> FinTyA),
	ccgTree_to_ccgTerm(A, TT_A),
	ccgTree_to_ccgTerm(B, TT_B),
	TT_X = (_, TyX),
	TT_Y = (_, TyY),
	TT_A_X_Y = ((TT_A @ TT_X, TyY~>FinTyA) @ TT_Y, FinTyA),
	Term = abst(TT_X, (abst(TT_Y, (TT_B @ TT_A_X_Y, FinTyB)), TyY~>FinTyB)).

ccgTree_to_ccgTerm( Tree, _ ) :-
	Tree =.. [Comb | _],
	format(user_error, 'Error while processing the combinator: ~w~n', [Comb]).
	%write(Id).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% cat2type(DirCat, Type)
% Converts (directed) Syntactic category DirCat into undirected Type
cat2type(Conj, A ~> A ~> A) :-
	Conj == conj, !.

cat2type(Punct, Type) :-
	memberchk(Punct, ['.','rrb','lrb','lqu','rqu',':',';',',','"','#','$','`','(',')','\'','LQU','RQU']),
	!,
	( var(Type) -> Type = Punct
	; \+grounded_type(Type) -> Type = A ~> A % treat as a modifier
	; true ).


cat2type(Cat, TyB ~> TyA) :-
	nonvar(Cat),
	(Cat = A/B; Cat = A\B), !,
	cat2type(A, TyA),
	cat2type(B, TyB),
	( A = B -> TyA = TyB; true ). % for conj\conj case

% Type can be constraint and it takes priority
% as X of s:X is not global for a term
cat2type(Cat, Type) :-
	nonvar(Cat),
	( memberchk(Cat, [s, n, np]) ->
		Type = Cat : _Feat
	; nonvar(Type), Type = T:_F ->
		Cat = T:_
	; Type = Cat
	).


grounded_type(T) :-
	( var(T) -> fail
	; atom(T) -> true
	; T = C:_, atom(C) ), !.

grounded_type(T) :-
	nonvar(T),
	T = A ~> B,
	grounded_type(A),
	grounded_type(B).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ttTerm to XML
ttTerm_to_xml(S, (X,Ty)) :-
	var(X) ->
		report("Error: unexpected Var while converting ttTerm into XML", []), fail
	; atom(X), (atom_chars(X, ['x'|_]); atom_chars(X,['p'|_])) -> %variable
		term_to_atom(X, AtX),
		type_to_xml(Ty, AtTy),
		atomic_list_concat(['<ttterm>\n<var>', AtX, '</var>\n<type>', AtTy, '</type>\n</ttterm>\n'], Atom),
		write(S, Atom)
	; X = t(Tk,Tags) -> %constant
		type_to_xml(Ty, AtTy),
		maplist(tag_to_xml, Tags, AtomTags),
		atomic_list_concat(AtomTags, '\n', XMLtags),
		atomic_list_concat(['<ttterm>\n<const>\n<tok>',Tk,'</tok>\n',XMLtags,'</const>\n<type>', AtTy, '</type>\n</ttterm>\n'], Atom),
		write(S, Atom)
	; X = TT1 @ TT2 -> %application
		write(S, '<ttterm>\n<app>\n'),
		ttTerm_to_xml(S, TT1),
		ttTerm_to_xml(S, TT2),
		type_to_xml(Ty, AtTy),
		atomic_list_concat(['</app>\n<type>', AtTy, '</type>\n</ttterm>\n'], Atom),
		write(S, Atom)
	; X = abst(Y, TT) -> %abstraction
		write(S, '<ttterm>\n<abst>\n'),
		ttTerm_to_xml(S, Y),
		ttTerm_to_xml(S, TT),
		type_to_xml(Ty, AtTy),
		atomic_list_concat(['</abst>\n<type>', AtTy, '</type>\n</ttterm>\n'], Atom),
		write(S, Atom)
	; X = (E, Ty1) -> %type changing
		write(S, '<ttterm>\n'),
		ttTerm_to_xml(S, (E,Ty1)),
		type_to_xml(Ty, AtTy),
		atomic_list_concat(['<type>', AtTy, '</type>\n</ttterm>\n'], Atom),
		write(S, Atom)
	; report("Error: unexpected clause while converting ttTerm into XML", []), fail.

tag_to_xml(Tag:Value, El) :-
	format(atom(El), '<~w>~w</~w>', [Tag, Value, Tag]).

% convert type into atom for html printing
type_to_xml(Type, HTML) :-
	var(Type) ->
		report("Error: unexpected type while converting into XML", [])
	; atom(Type) ->
		HTML = Type
	; Type = A:B ->
		(var(B) ->
			HTML = A
		; atomic_list_concat([A,'<tyfeat>',B,'</tyfeat>'], HTML)
		)
	; Type = np:A~>s:B, var(A) ->
		( var(B) -> Feat = ''; atomic_list_concat(['<tyfeat>',B,'</tyfeat>'], Feat)  ),
		atomic_list_concat(['vp',Feat], HTML)
	; Type = A~>B ->
		type_to_xml(A, AtA),
		type_to_xml(B, AtB),
		( A = _~>_, \+((A = np:F~>s:_, var(F))) ->
			atomic_list_concat(['(',AtA,'),',AtB], HTML)
		; atomic_list_concat([AtA,',',AtB], HTML)
		)
	; report("Error: unexpected type while converting into XML", []).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% pretty variables instead of _G23
pretty_vars_in_ttterm(A, Z, TT, Pretty) :-
	copy_term(TT, Pretty),
	pretty_vars_in_ttterm_(A, Z, Pretty).

pretty_vars_in_ttterm_(X-P, Z, (Exp, _)) :-
	var(Exp) ->
		report('Error: unexpected free variable found in pretty_vars_in_ttterms', [])
	; atom(Exp) ->
		Z = X-P
	; Exp =.. [t | _] ->
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
	; report('Error: unexpected clause in pretty_vars_in_ttterms', []).


report(Format, List) :-
	format(user_error, Format, List).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
print_ttTerm_as_term(Ind, (t(Tok, Tags), Type)) :- !,
	tab(Ind), write('t('),
	print_type_as_term(Type), write(', '),
	print(Tok), write(', '),
	print(Tags), write(')').

print_ttTerm_as_term(Ind, ((Term, Ty), Type)) :- !,
	tab(Ind), write('*('),
	print_type_as_term(Type), write(',\n'),
	Ind2 is Ind + 2,
	print_ttTerm_as_term(Ind2, (Term, Ty)),
	write(')').

print_ttTerm_as_term(Ind, (App_Abst, Type)) :-
	( App_Abst = A @ B, Op = '@'
	; App_Abst = abst(A, B), Op = 'λ' ),
	!,
	tab(Ind), Ind2 is Ind + 2,
	write(Op), write('('),
	print_type_as_term(Type), write(',\n'),
	print_ttTerm_as_term(Ind2, A), 	write(',\n'),
	print_ttTerm_as_term(Ind2, B), write(')').

print_ttTerm_as_term(Ind, (Const, Type)) :-
	atom(Const), !,
	tab(Ind), write('('),
	print_type_as_term(Type), write(', '),
	print(Const), write(')').

%%%%%%%%%%%%%%%%%%%
print_type_as_term(A) :-
	var(A), !,
	print(A).

print_type_as_term(A~>B) :- !,
	( nonvar(A), A = _~>_ -> write('('); true ),
	print_type_as_term(A),
	( A = _~>_ -> write(')'); true ),
	write('~>'),
	print_type_as_term(B).

print_type_as_term(A:B) :-
	var(B), !,
	print(A).

print_type_as_term(Ty) :-
	print(Ty).
