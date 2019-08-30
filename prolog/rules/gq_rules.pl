%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 		Generalized Quantifier Rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module('../llf/ttterm_preds', [feed_ttTerm_with_ttArgs/3]).
:- use_module('../lambda/type_hierarchy', [final_value_of_type/2]).

:- multifile r/4.

gq_rules([
	'TR',
	'TR_by'
]).




% Type raise non-bare quantifiers
r('TR',  equi:non,  _, _Lexicon, 
		br([nd( M, (VPTT @ ((Det,n:_~>np:_)@NounTT,np:_), Ty_S), 
				Args, TF )], 
		  Sig) 
		===>
		br([nd( M, ((TR_Det @ NounTT, (np:_~>s:_)~>s:_) @ VPTT1, s:_), 
				[], TF)], 
		  Sig) )
:-
		Det =.. [tlp | _],
		TR_Det = (Det, n:_~>(np:_~>s:_)~>s:_),
		final_value_of_type(Ty_S, s:_),
		( Args = [] -> 
			VPTT1 = VPTT
		  ;	%Ty_S = np:_~>Val,
			VP_X = (VPTT @ (X,np:A), Ty_S),
			feed_ttTerm_with_ttArgs(VP_X, VP_X_fed, Args),
			VPTT1 = (abst((X,np:A), VP_X_fed), np:_~>s:_)  
		).

% 
r('TR_by',  equi:non,  _, _Lexicon, 
		br([nd( M, ((BY @ ((Det,n:_~>np:_)@NounTT,np:_), _) @ VP, np:_~>s:_),
				Args, TF )], 
		  Sig) 
		===>
		br([nd( M, ((TR_Det @ NounTT, (np:_~>s:_)~>s:_) @ Abst_BY, s:_), 
				[], TF)], 
		  Sig) )
:-
		BY = (tlp(_,'by','IN',_,_), np:_~>(np:_~>s:_)~>(np:_~>s:_)),
		Det =.. [tlp | _],
		TR_Det = (Det, n:_~>(np:_~>s:_)~>s:_),
		BYTT1 = ((BY @ (X,np:A), (np:_~>s:_)~>(np:_~>s:_)) @ VP, np:_~>s:_),
		feed_ttTerm_with_ttArgs(BYTT1, BYTT2, Args),
		Abst_BY = (abst((X,np:A), BYTT2), np:A~>s:_).
		

r('TR_prep',  equi:non,  _, _Lexicon, 
		br([nd( M, (Prep @ ((Det,n:_~>np:_)@NounTT,np:_), Ty_S), 
				Args, TF )], 
		  Sig) 
		===>
		br([nd( M, ((TR_Det @ NounTT, (np:_~>s:_)~>s:_) @ VPTT1, s:_), 
				[], TF)], 
		  Sig) )
:-
		Det =.. [tlp | _],
		TR_Det = (Det, n:_~>(np:_~>s:_)~>s:_),
		final_value_of_type(Ty_S, s:_),
		( Args = [] -> 
			VPTT1 = VPTT
		  ;	%Ty_S = np:_~>Val,
			VP_X = (VPTT @ (X,np:A), Ty_S),
			feed_ttTerm_with_ttArgs(VP_X, VP_X_fed, Args),
			VPTT1 = (abst((X,np:A), VP_X_fed), np:_~>s:_)  
		).











