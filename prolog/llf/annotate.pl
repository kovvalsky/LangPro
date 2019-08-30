%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Context free Annotation of words with extra information
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module('annotate',
	[
		cf_annotation/2
	]).

:- use_module('../knowledge/ling', [a_list_of_colors/1]).
:- use_module('../lambda/lambda_tt', [op(605, yfx, @)]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

cf_annotation((Var, Type), (Var, Type)) :-
	var(Var), !.

cf_annotation((TT1 @ TT2, Type), (SimTT1 @ SimTT2, Type)) :-
	!, 
	cf_annotation(TT1, SimTT1),
	cf_annotation(TT2, SimTT2).

cf_annotation( (tlp(Tk1,Lem1,Pos1,F11,F21), Type1), (tlp(Tk2,Lem2,Pos2,F12,F22), Type2) ) :-
	!, 
	TLP1 = (tlp(Tk1,Lem1,Pos1,F11,F21), Type1),
	TLP2 = (tlp(Tk2,Lem2,Pos2,F12,F22), Type2),
	( 
	is_color(TLP1, TLP2)
	), !.

cf_annotation( (abst(TTx, TT), Type), (abst(TTx, SimTT), Type) ) :-
	!, 
	cf_annotation(TT, SimTT).	

cf_annotation( (TT, Type), (SimTT, Type) ) :-
	!, 
	cf_annotation(TT, SimTT). 



is_color( (tlp(Tk,Lem,Pos,F1,F2), Type), (tlp(Tk,Lem,Pos,F1,X), Type)) :-
	a_list_of_colors(Colors),
	( member(Lem, Colors) ->
		X = 'COL'
	 ;  X = F2
	).
	 
	
	

