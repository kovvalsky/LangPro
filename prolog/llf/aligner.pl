%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ============== Aligner ==================
% finds phrases that are shared by premises
% and hypotheses and treats them as a unit
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module('aligner',
	[
		align_ttTerms/4
	]).

:- use_module('../lambda/lambda_tt', [op(605, yfx, @)]).
:- use_module('../printer/reporting', [report/1]).
:- use_module('ttterm_to_term', [ttTerm_to_prettyTerm/2]).
:- use_module('ttterm_preds', [
	print_ttTerms_in_latex/1, npTTterm_as_constant/1, match_ttTerms/3,
	npTTterm_unlike_constant/1, modTTterm_with_conj_sent_head/1, add_heads/2
	]).
:- use_module('../utils/user_preds', [
	ul_append/2, uList2List/2
	]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% For testing purposes
test_align(Prob_Id) :-
	findall(Sen_Id, sen_id(Sen_Id, Prob_Id, _, _, _), Sen_Ids),
	findall(CCGTree,
			( member(Id, Sen_Ids), ccg(Id, CCGTree) ),
			CCGTrees),
	maplist(ccgTree_to_correct_ccgTerm, CCGTrees, CCGTerms),
	align_ttTerms(CCGTerms, NewTTterms, CommonTTterms, []-[]),
	( CommonTTterms = [] ->
	  	report([Prob_Id, ': '])
	  ; report([Prob_Id, ': ' | CommonTTterms])
	),
	maplist([A,B,(A,B)]>>true, CCGTerms, NewTTterms, PairList),
	%once_gen_quant_tt(CCGTerm4, TTterm),
	print_ttTerms_in_latex(PairList).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% takes a list of ttTerms and searches non-atomic ttTerms
% that are shared by all ttTerms
% KB_XP is not changed
align_ttTerms(TTterms, NewTTterms, CommonTTterms, KB_XP) :-
	TTterms = [TT | _], % hint: pick the smallest term
	!,
	once(find_alignment(TT, TTterms, NewTTterms, CommTTterms, KB_XP)),
	uList2List(CommTTterms, CommonTTterms).

align_ttTerms([], [], [], _).

%%%%%%%%%%%%%%%%%%%%%%%
% picks a ttTerm TT1 and a list of ttTerms and
% searches non-atomic subterms of TT1 that are shared by all list member ttTerms too
find_alignment((Exp,_Ty), List_TTterms, List_TTterms, _CommonTTterms, _) :-
	( \+compound(Exp)
	; Exp =.. [tlp|_] ),
	!.

find_alignment(TTterm, List_TTterms, New_List_TTterms, CommonTTterms, KB_XP) :-
	TTterm = (_TTExp, Type),
	% avoids alignment of 'a man', 'no car' etc they dont behave like constants
	( Type = np:_ ->
		( debMode('aall') -> \+npTTterm_unlike_constant(TTterm); npTTterm_as_constant(TTterm) ) %solves fracas-22
	; true ), % add that not mon downward
	\+modTTterm_with_conj_sent_head(TTterm), % avoids alignment of 'and X' where X: ...~>s
	maplist(replace_subttTerm_in_ttTerm(KB_XP, TTterm, (TLP, Type)), List_TTterms, New_List_TTterms),
	ttTerm_to_prettyTerm(TTterm, PrettyTerm),
	term_to_atom(PrettyTerm, AtomTerm),
	add_heads(TTterm, (_,_,tlp(_,_,Pos,F1,F2))), %!!! adds information from head, can give wrong information, e.g. a@man,DT,...
	TLP = tlp(AtomTerm,AtomTerm,Pos,F1,F2),		 % shared parts are treated as TLP
	( var(Pos) -> Pos = 'nil'; true),  ( var(F1) -> F1 = 'nil'; true), ( var(F2) -> F2 = 'nil'; true), %otherwiese atom_chars(POS, List) crashes
	!,
	ul_append(CommonTTterms, [TLP]).

find_alignment((TT1@TT2,_Ty), List_TTterms, New_List_TTterms, CommonTTterms, KB_XP) :-
	!,
	find_alignment(TT1, List_TTterms,   List_TTterms_1,   CommonTTterms, KB_XP),
	find_alignment(TT2, List_TTterms_1, New_List_TTterms, CommonTTterms, KB_XP).

find_alignment(((Exp,Ty),_Ty), List_TTterms, New_List_TTterms, CommonTTterms, KB_XP) :-
	!,
	find_alignment((Exp,Ty), List_TTterms, New_List_TTterms, CommonTTterms, KB_XP).

find_alignment((abst(_X,TT),_Ty), List_TTterms, New_List_TTterms, CommonTTterms, KB_XP) :-
	!,
	find_alignment(TT, List_TTterms, New_List_TTterms, CommonTTterms, KB_XP).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% replaces subTTterm1 with subTTterm2 in TTterm1,
% TTterm2 is a result of a substitution
% equivalent to searching if subTTterm1 = subTTterm2
replace_subttTerm_in_ttTerm(_KB_XP, _, _, (Var,_Ty), _) :-
	var(Var),
	!,
	fail.

replace_subttTerm_in_ttTerm(KB_XP, SubTTterm1, SubTTterm2, TTterm1, TTterm2) :-
	match_ttTerms(SubTTterm1, TTterm1, KB_XP), % alignment with empty knowledge base
	TTterm2 = SubTTterm2,
	!.

replace_subttTerm_in_ttTerm(KB_XP, SubTTterm1, SubTTterm2, ((TTExp1,Ty1), Type), ((TTExp2,Ty2), Type)) :-
	!,
	replace_subttTerm_in_ttTerm(KB_XP, SubTTterm1, SubTTterm2, (TTExp1,Ty1), (TTExp2,Ty2)).

replace_subttTerm_in_ttTerm(KB_XP, SubTTterm1, SubTTterm2, (TT1@TT2, Type), (NewTT1@NewTT2, Type)) :-
	!,
	( replace_subttTerm_in_ttTerm(KB_XP, SubTTterm1, SubTTterm2, TT1, NewTT1)
	->	( replace_subttTerm_in_ttTerm(KB_XP, SubTTterm1, SubTTterm2, TT2, NewTT2)
		->	true
		; 	NewTT2 = TT2
		)
	;	( replace_subttTerm_in_ttTerm(KB_XP, SubTTterm1, SubTTterm2, TT2, NewTT2)
		->	NewTT1 = TT1
		; 	fail
		)
	).

replace_subttTerm_in_ttTerm(KB_XP, SubTTterm1, SubTTterm2, (abst(X,TT1), Type), (abst(X,TT2), Type)) :-
	!,
	replace_subttTerm_in_ttTerm(KB_XP, SubTTterm1, SubTTterm2, TT1, TT2). % be carefull of matching like@X to like@y
