%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- use_module('../utils/user_preds', [ttExp_to_ttTerm/2]).	
:- use_module('../printer/reporting', [report/1]).
:- use_module('../llf/recognize_MWE', [remove_pp_arg/2]).
:- use_module('../llf/ccg_term', [ccgIDTree_to_ccgIDTerm/2]).
:- use_module('ttterm_to_term', [ttTerm_to_prettyTerm/2]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% takes a pattern in TTexp representation and
% searches matches in all CCG terms or LLFs
term_query(TTexp, StrucType, Matches) :-
	ttExp_to_ttTerm(TTexp, TT),
	ccgTrees_to_structures(StrucType, ID_CCGterms),
	


/*
match_TTterm_pattern(_Pat, TT) :-
	var(TT),
	!.

match_TTterm_pattern(Pat, TT) :-
	subsumes_term(Pat, TT),
	!,
	
	( debMode('mwe') -> ttTerm_to_prettyTerm(PreFixed, Pr), term_to_atom(Pr, At),  report(['!!! MWE: ', At]); true ),
  	loc_fix_ccgTerm(PreFixed, Fixed). 

loc_fix_ccgTerm(App_TC, Fixed) :-
	App_TC = (_@_, Cat),
	remove_pp_arg(App_TC, App_TC2),
	App_TC2 = (TC1@TC2, Cat), 
  	loc_fix_ccgTerm(TC1, Clean1),
  	loc_fix_ccgTerm(TC2, Clean2),
	Fixed = (Clean1 @ Clean2, Cat). 

loc_fix_ccgTerm((TC_term, Cat), Clean) :-
	TC_term = abst(X, SubTC), 
	Clean = (abst(X, SubClean), Cat), 
	loc_fix_ccgTerm(SubTC, SubClean).

loc_fix_ccgTerm((TC_term, Cat), Clean) :-
	TC_term = (_, _),
	loc_fix_ccgTerm(TC_term, Clean1),
	Clean = (Clean1, Cat). 

loc_fix_ccgTerm(TC, TC). 

*/






% obtain desirable structures from CCG trees 
ccgTrees_to_structures('CCG term', ID_CCGterms) :-
	findall(ccg(Id, Tree), ccg(Id, Tree), ID_CCGs),
	maplist(ccgIDTree_to_ccgIDTerm, ID_CCGs, ID_CCGterms).
	

ccgTrees_to_structures('CCG tree', List) :-
	findall(ccg(Id, Tree), ccg(Id, Tree), List). 





