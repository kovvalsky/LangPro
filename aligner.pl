%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ============== Aligner ==================
% finds phrases that are shared by premises
% and hypotheses and treats them as a unit
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% For testing purposes
test_align(Prob_Id) :-
	findall(Sen_Id, sen_id(Sen_Id, Prob_Id, _, _, _), Sen_Ids),
	findall(CCGTree, 
			( member(Id, Sen_Ids), ccg(Id, CCGTree) ),
			CCGTrees),
	maplist(ccgTree_to_correct_ccgTerm, CCGTrees, CCGTerms),
	align_ttTerms(CCGTerms, NewTTterms, CommonTTterms),
	( CommonTTterms = [] -> 
	  	report([Prob_Id, ': '])
	  ; report([Prob_Id, ': ' | CommonTTterms]) 
	),
	two_lists_to_pair_list(CCGTerms, NewTTterms, PairList),
	%once_gen_quant_tt(CCGTerm4, TTterm),
	print_ttTerms_in_latex(PairList).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% takes a list of ttTerms and searches non-atomic ttTerms
% that are shared by all ttTerms
align_ttTerms(TTterms, NewTTterms, CommonTTterms) :-
	TTterms = [TT | _], % hint: pick the smallest term
	!,
	once(find_alignment(TT, TTterms, NewTTterms, CommTTterms)),
	remove_varTail_from_uList(CommTTterms, CommonTTterms).

align_ttTerms([], [], []).

%%%%%%%%%%%%%%%%%%%%%%%
% picks a ttTerm TT1 and a list of ttTerms and 
% searches non-atomic subterms of TT1 that are shared by list member ttTerms too
find_alignment((Exp,_Ty), List_TTterms, List_TTterms, _CommonTTterms) :-
	( \+compound(Exp)
	; Exp =.. [tlp|_] ),
	!.

find_alignment(TTterm, List_TTterms, New_List_TTterms, CommonTTterms) :-
	TTterm = (_TTExp, Type),
	% avoids alignment of 'a man', 'no car' etc they dont behave like constants
	( debMode('aall') -> true; \+npTTterm_unlike_constant(TTterm) ), 
	\+modTTterm_with_conj_sent_head(TTterm), % avoids alignment of 'and X' where X: ...~>s
	ttTerm_to_prettyTerm(TTterm, PrettyTerm),
	term_to_atom(PrettyTerm, AtomTerm),
	maplist(replace_subttTerm_in_ttTerm(TTterm, (AtomTerm, Type)), List_TTterms, New_List_TTterms),
	!,
	ul_append(CommonTTterms, [AtomTerm]).

find_alignment((TT1@TT2,_Ty), List_TTterms, New_List_TTterms, CommonTTterms) :-
	!,
	find_alignment(TT1, List_TTterms,   List_TTterms_1,   CommonTTterms),
	find_alignment(TT2, List_TTterms_1, New_List_TTterms, CommonTTterms).

find_alignment(((Exp,Ty),_Ty), List_TTterms, New_List_TTterms, CommonTTterms) :-
	!,
	find_alignment((Exp,Ty), List_TTterms, New_List_TTterms, CommonTTterms).

find_alignment((abst(_X,TT),_Ty), List_TTterms, New_List_TTterms, CommonTTterms) :-
	!,
	find_alignment(TT, List_TTterms, New_List_TTterms, CommonTTterms).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% replaces subTTterm1 with subTTterm2 in TTterm1, 
% TTterm2 is a result of a substitution
% equivalent to searching if subTTterm1 = subTTterm2
replace_subttTerm_in_ttTerm(_, _, (Var,_Ty), _) :-
	var(Var),
	!,
	fail.

replace_subttTerm_in_ttTerm(SubTTterm1, SubTTterm2, TTterm1, TTterm2) :-
	match_ttTerms(SubTTterm1, TTterm1), 
	TTterm2 = SubTTterm2,
	!.

replace_subttTerm_in_ttTerm(SubTTterm1, SubTTterm2, ((TTExp1,Ty1), Type), ((TTExp2,Ty2), Type)) :-
	!,
	replace_subttTerm_in_ttTerm(SubTTterm1, SubTTterm2, (TTExp1,Ty1), (TTExp2,Ty2)).

replace_subttTerm_in_ttTerm(SubTTterm1, SubTTterm2, (TT1@TT2, Type), (NewTT1@NewTT2, Type)) :-
	!,
	( replace_subttTerm_in_ttTerm(SubTTterm1, SubTTterm2, TT1, NewTT1) ->
		( replace_subttTerm_in_ttTerm(SubTTterm1, SubTTterm2, TT2, NewTT2) ->
			true
		  ; NewTT2 = TT2
		)
	  ;	( replace_subttTerm_in_ttTerm(SubTTterm1, SubTTterm2, TT2, NewTT2) ->
			NewTT1 = TT1
		  ; fail 
		) 
	).  

replace_subttTerm_in_ttTerm(SubTTterm1, SubTTterm2, (abst(X,TT1), Type), (abst(X,TT2), Type)) :-
	!,
	replace_subttTerm_in_ttTerm(SubTTterm1, SubTTterm2, TT1, TT2). % be carefull of matching like@X to like@y









