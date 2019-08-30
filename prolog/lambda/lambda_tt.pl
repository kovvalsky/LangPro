%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module(lambda_tt, [
	norm_tt/2,
	op(605, xfy, ~>), 	% more than : 600
	op(605, yfx, @)   	% more than : 600
]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/*
:- 	prolog_load_context(directory, Dir), 
	format('lambda.tt: ~w~n', [Dir]),
	asserta(file_search_path(curr, Dir)),
	absolute_file_name(curr, Abs, []),
	format('curr_dir is ~w~n', [Abs]),
	asserta(file_search_path('..', curr('..'))),
	absolute_file_name('..', SRCAbs, []),
	format('src_lib is ~w~n', [SRCAbs]).
*/
:- use_module('../printer/reporting', [throw_error/2, report/1]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% beta-eta Normalize (term, type)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
norm_tt(TT, NormTT) :-
	beta_norm_tt(TT, BetaNormTT),
	eta_norm_tt(BetaNormTT, NormTT) ->
		true
	; throw_error('~w ~w', ['norm_tt/2 failed to normalize', TT]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% free(TTvar, TTterm,)
% checks if TTvar is free in TTterm 

free_tt( (X,Ty), (Tr,Ty) ) :-
	(\+compound(Tr); Tr =.. [tlp|_]), !,
	X == Tr.
	
free_tt( (X,Ty), (FunTT@ArgTT,_) ) :-
	!, (free_tt( (X,Ty), FunTT); 
	 	free_tt( (X,Ty), ArgTT)	), !.

free_tt( TTx, (abst(TTy,TT),_) ) :-
	\+TTx == TTy,
	free_tt(TTx, TT), !.

free_tt( TTx, (TT,_) ) :-
	free_tt(TTx, TT).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%    Alpha, Beta, Eta equivalences for TTs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% alpha_convert_tt(TT1, TT2)
% converts TT1 to alpha normal (with different
% lambda variables) form TT2  

alpha_convert_tt(TT1,TT2) :-
	var(TT1) ->
		writeln('Error: TT expected but a variable found'), 
		fail;
	var(TT2) ->
 		alpha_convert_tt(TT1,[],TT2), !;
	writeln('Error: an unbound variable expected but bound found'), 
	fail.

alpha_convert_tt(TT1,TT2) :-
 		alpha_convert_tt(TT1,[],TT2).

alpha_convert_tt( (Tr1, Ty1), Subs, (Tr2, Ty1)) :-
	var(Tr1), !,
	member(sub((A, Ty1) ,(Tr2, Ty1)), Subs),
    Tr1 == A, !.

alpha_convert_tt( (Fun1 @ Arg1, Ty1), Subs, (Fun2 @ Arg2, Ty1)) :-
	!,
	alpha_convert_tt(Fun1, Subs, Fun2),
	alpha_convert_tt(Arg1, Subs, Arg2).	

alpha_convert_tt(X, _, X) :-
	X = (tlp(_,_,_,_,_), _), !;
	X = (A,_),
	atom(A), !. 

alpha_convert_tt( (abst((X,Ty),F1), Ty1), Subs, (abst((Y,Ty),F2), Ty1)) :-
	alpha_convert_tt(F1, [sub((X,Ty),(Y,Ty)) | Subs], F2), !.

alpha_convert_tt( ((Tr,Ty1),Ty2), Subs, ((Term,Ty1),Ty2)) :-
	alpha_convert_tt((Tr,Ty1), Subs, (Term,Ty1)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% alpha_eq_tt(TT1, TT2)
% checks if TT1 and TT2 are alpha equivalents 

alpha_eq_tt(TT1,TT2):-
 		alpha_eq_tt(TT1,[],TT2).

alpha_eq_tt( (Tr1, Ty1), Subs, (Tr2, Ty1)):-
	var(Tr1), !,
	member(sub((A, Ty1) ,(B, Ty1)), Subs),
    Tr1 == A, 
	Tr2 == B, !.

alpha_eq_tt( (Fun1 @ Arg1, Ty1), Subs, (Fun2 @ Arg2, Ty1)):-
	!,
	alpha_eq_tt(Fun1, Subs, Fun2),
	alpha_eq_tt(Arg1, Subs, Arg2).	

alpha_eq_tt( (A, T), _, (A, T)):-
	(A = tlp(_,_,_,_,_); atom(A)), !. 

alpha_eq_tt( (abst((X,Ty),F1), Ty1), Subs, (abst((Y,Ty),F2), Ty1)):-
	alpha_eq_tt(F1, [sub((X,Ty),(Y,Ty)) | Subs], F2), !.

alpha_eq_tt( ((Tr1,Ty1),Ty2), Subs, ((Tr2,Ty1),Ty2)):-
	alpha_eq_tt((Tr1,Ty1), Subs, (Tr2,Ty1)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% beta_norm_tt(Term1, BetaTerm)	
% Typable Term1 reduces to beta normal form BetaTerm
% it is NOT pressuposed that Terms are alpha converted already

beta_norm_tt(TT_alpha, Beta_Norm_TT) :-
	beta_red_tt(TT_alpha, BN_TT),
	( 	TT_alpha == BN_TT -> 
	 		Beta_Norm_TT = BN_TT;
	  	beta_norm_tt(BN_TT, BNorm_TT),
		Beta_Norm_TT = BNorm_TT		). 
	 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% beta_red_tt(Term, BetaReducedTerm)	
% removes at least one RedEx sub expression 

beta_red_tt((Tr,Ty), (Tr,Ty)) :-
	(\+compound(Tr); Tr =.. [tlp|_]), !.

beta_red_tt((abst(TTx, TT),_) @ TTarg, BetaTT) :-
	!, %beta_norm_tt(TTarg, Norm_TTarg),
	substitute_tt(TTx, TTarg, TT, Subst_TT),
	%report(['!!! Case of beta reduction']),
	% doesn't loop as predicate discards a lambda abst
	beta_norm_tt(Subst_TT, BetaTT).
	
beta_red_tt( (TTfun @ TTarg,Ty), BetaTT) :-
	!, beta_norm_tt(TTfun, (FunTrN, FunTyN)),
	( 	nonvar(FunTrN), FunTrN = abst(TTx, TT) ->
			substitute_tt(TTx, TTarg, TT, Subst_TT),
			%report(['!!! Case of beta reduction']),
			% doesn't loop as predicate discards a lambda abst
			beta_norm_tt(Subst_TT, BetaTT);
		beta_norm_tt(TTarg, Norm_TTarg),
		BetaTT =  ((FunTrN, FunTyN) @ Norm_TTarg, Ty)	).
	
beta_red_tt( (abst(TTx, TT), Ty), BetaTT) :-
	!, beta_norm_tt(TT, Norm_TT),
	BetaTT = (abst(TTx, Norm_TT), Ty).

beta_red_tt( (TT, Ty), BetaTT) :-
	beta_norm_tt(TT, Norm_TT),
	BetaTT = (Norm_TT, Ty).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% substitute_tt(Var, TTerm, MainTTterm, TTterm_after_substitution)	

substitute_tt((Var,Ty1), TT, (Exp,Ty2), TT) :-
	Var == Exp,
	!,
	( Ty1 == Ty2 -> true
	; report(['Error is substitution of variable while Beta Reducing']), false %cahnegs due to %sick-272 a:DT,n~>n~>n
	).

substitute_tt(_VarTT, _TT, (Tr, Ty), (Tr, Ty)) :-
	(\+compound(Tr); Tr =.. [tlp|_]), !.

substitute_tt(VarTT, TT, (TT1@TT2,Ty), (R1@R2,Ty)) :-
	!, substitute_tt(VarTT, TT, TT1, R1), 
	substitute_tt(VarTT, TT, TT2, R2). 

substitute_tt(VarTT, TT, (abst(TTx,TT1),Ty), (abst(TTx,R2),Ty)) :-
	!, (	TTx == VarTT ->
				R2 = TT1; 
			substitute_tt(VarTT, TT, TT1, R2)	). 

substitute_tt(VarTT, TT, (MainTT,Ty), (R_TT,Ty)) :-
	substitute_tt(VarTT, TT, MainTT, R_TT). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% eta_norm_tt(TT, EtaNormTT)	
% Reduces TT to eta-normal form EtaNormTT 

eta_norm_tt((Tr,Ty), (Tr,Ty)) :- 
	(\+compound(Tr); Tr =.. [tlp|_]), !.
	
eta_norm_tt((FunTT@ArgTT,Ty), (N_FunTT@N_ArgTT,Ty)) :- 
	!, eta_norm_tt(FunTT, N_FunTT),
	eta_norm_tt(ArgTT, N_ArgTT).	

eta_norm_tt( (abst(TTx,TT),_), ResTT ) :- 
	TT = (FunTT @ ArgTT, _),
	TTx == ArgTT,
	\+ free_tt(TTx, FunTT), !,
	eta_norm_tt(FunTT, ResTT).
	
eta_norm_tt( (abst(TTx,TT),Ty), NormTT ) :- 
	!, eta_norm_tt(TT, Norm),
	( TT == Norm ->
		NormTT = (abst(TTx,TT),Ty);
		eta_norm_tt((abst(TTx,Norm),Ty), NormTT) ).

eta_norm_tt( ((TT1, Ty1), Ty), ((NormTT1, Ty1), Ty) ) :-
	eta_norm_tt((TT1, Ty1), (NormTT1, Ty1)). 


