%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: Simply Typed Lambda Calculus
%     Version: 12.06.12
%      Author: lasha.abzianidze{at}gmail.com 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%          Defined Functors
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%:-op(650, xfx, '|-').
%:-op(640, xfy, ::).
%:-op(605, xfy, ~>). 	% more than : 600
%:-op(605, yfx, @).    	% more than : 600


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% free(Var, AlphaNormTerm)
% checks if Var is free in Alpha normal term 

free(X, LTerm) :-
	\+ compound(LTerm),
	!,
	X == LTerm.
	
free(X, Fun @ Arg) :-
	!,
	(free(X, Fun); 
	 free(X, Arg)).

free(X, abst(Y, Term)) :-
	!,
	\+X == Y, % added and Fixed
	free(X, Term).

 	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%               Typing Lambda Terms
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% Env '|-' LambdaTerm :: Type
% types closed alpha converted LambdaTerm by Type
% wrt environment Env 

Env '|-' Const :: Alpha :-
	atom(Const), 
	!,
	%(lex(Const, Alpha) ->
	%	true;
	(member(C :: Alpha, Env), C == Const  ->
		true;
	 Const :: Alpha :: _). % from lexicon or from lex

Env '|-' X :: Alpha :-
	var(X), 
	!,
	member(Y :: Type, Env),	
	X == Y,
	unify_with_occurs_check(Type, Alpha). 
% linear lambda terms does not need occurs check

Env '|-' abst(X, Term) :: Alpha ~> Beta :-
	!, 
	(var(X) ->
		[ X :: Alpha | Env ] '|-' Term :: Beta;
		writeln('\nError: Non-variable in abstraction')).
	
Env '|-' A @ B :: Beta :- 
	!, 
	Env '|-' A :: Alpha ~> Beta, 
	Env '|-' B :: Alpha.
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%       Alpha, Beta, Eta equivalences
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% alphaConvert(Term1, Term2)
% converts Term1 to alpha normal (with different
% lambda variables) form Term2  

alphaConvert(F1,F2):-
	var(F2), 
	alphaConvert(F1,[],F2),
	!.

alphaConvert(X, Subs, Y):-
	var(X),
	member(sub(Z,Y), Subs), 
    X == Z,
	!.

alphaConvert(X, _, Y):-
	var(X),
	X = Y,
	!.  % accepts open terms too

alphaConvert(X, _, Y):-
	atom(X),
	!,
	Y = X.

alphaConvert(abst(X,F1), Subs, abst(Y,F2)):-
	var(X),
	var(Y),
	!,
	alphaConvert(F1, [sub(X,Y) | Subs], F2).

alphaConvert(Fun1 @ Arg1, Subs, Fun2 @ Arg2):-
	!,
	alphaConvert(Fun1, Subs, Fun2),
	alphaConvert(Arg1, Subs, Arg2).	

alphaConvert(abst(X,F1), Subs, abst(Y,F2)):- %shouldn't be used by normal calculus
	nonvar(X),
	%nonvar(Y), impossible
	X = X1 @ X2, var(X1), var(X2),
	Y = Y1 @ Y2, %var(Y1), var(Y2),
	!,
	alphaConvert(F1, [sub(X1,Y1), sub(X2,Y2)| Subs], F2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% alpha(Term1, Term2)
% checks if two lambda terms are alpha equivalent

alpha(LTerm1, LTerm2) :-
	alpha(LTerm1, [], LTerm2),
	!.

alpha(Lit1, Subs, Lit2) :-
	(var(Lit1); atom(Lit1); var(Lit2); atom(Lit2)),
	!,
	(member(sub(X, Y), Subs), 
	 (X == Lit1; Y == Lit2) -> 
	   	Y == Lit2,
		X == Lit1;
		Lit1 == Lit2).

alpha(Fun1 @ Arg1, Subs, Fun2 @ Arg2) :-
	!,
	alpha(Fun1, Subs, Fun2),
	alpha(Arg1, Subs, Arg2).

alpha(abst(X, Term1), Subs, abst(Y, Term2)) :-
	var(X), 
	var(Y),
	!,
	alpha(Term1, [sub(X,Y) | Subs], Term2).

alpha(abst(X, Term1), Subs, abst(Y, Term2)) :- %shouldn't be used by normal calculus
	nonvar(X), 
	nonvar(Y), 
	X = X1 @ X2, var(X1), var(X2),
	Y = Y1 @ Y2, var(Y1), var(Y2),
	!,
	alpha(Term1, [sub(X1,Y1), sub(X2,Y2)|Subs], Term2).


	
		
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% betaNorm(Term1, BetaTerm)	
% Typable Term1 reduces to beta normal form BetaTerm

betaNorm(LTerm, BNorm) :-
	alphaConvert(LTerm, NewLTerm),
	betaRed(NewLTerm, BNorm).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% betaRed(Term, BetaReducedTerm)	
% Beta-reduces alpha-normal Term to BetaReducedTerm 

betaRed(LTerm, BNorm) :-
	\+ compound(LTerm),
	!,
	BNorm = LTerm.
	
betaRed(Fun @ Arg, BNorm) :-
	nonvar(Fun),
	Fun = abst(X, Term),
	!,
	betaRed(Arg, NormArg), % added, reduces complexity
	X = NormArg,
    betaNorm(Term, BNorm).	% ensures alpha conversion of Term
	
betaRed(Fun @ Arg, BNorm) :-
	!,
	betaRed(Fun, NormFun),
	betaRed(Arg, NormArg),
	( alpha(Fun, NormFun), alpha(Arg, NormArg) -> BNorm = Fun @ Arg; 
	  betaNorm(NormFun @ NormArg, BNorm)  % betanorm, because of NormFun and NormArg
	).

betaRed(abst(X, Term), BNorm) :-
	!,
	betaRed(Term, NormTerm),
	BNorm = abst(X, NormTerm).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% etaNorm(Term1, EtaTerm)	
% Typable Alpha normal Term1 reduces to Eta-normal form EtaTerm

etaNorm(LTerm, ENorm) :- 
	\+ compound(LTerm),
	!,
	ENorm = LTerm.
	
etaNorm(LTerm, ENorm) :- 
	LTerm = Fun @ Arg,
	!,
	etaNorm(Fun, NewFun),
	etaNorm(Arg, NewArg),
	ENorm = NewFun @ NewArg.	

etaNorm(LTerm, ENorm) :- 
	LTerm = abst(X, Term @ Y),
	X == Y,
	var(X),
	\+ free(X, Term),
	!,
	etaNorm(Term, ENorm).
	
etaNorm(LTerm, ENorm) :- 
	LTerm = abst(Y, Term),
	!,
	etaNorm(Term, NewTerm),
	( NewTerm == Term -> 
		ENorm = LTerm; 
		etaNorm(abst(Y, NewTerm), ENorm) ).	 % fixxing eta reduction	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% betaEtaNorm(Term1, BetaEtaTerm)	
% Alpha normal (un)typable Term1 reduces to 
% Beta Eta normal form BetaEtaTerm

betaEtaNorm(LTerm, BENorm) :-
	betaNorm(LTerm, BNorm),
	etaNorm(BNorm, BENorm) ->
		true;
		writeln('Error: can not normalize a term.'),
			fail.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% equiTerms(Term1, Term2)	
% cheks if terms are BetaEtaEquivalent

equiTerms(LTerm1, LTerm2) :-
	betaEtaNorm(LTerm1, normLTerm1),
	betaEtaNorm(LTerm2, normLTerm2),
	alpha(normLTerm1, normLTerm2).

