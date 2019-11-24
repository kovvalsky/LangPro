%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%% Bag of words %%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


shallow_reasoning(PrId, Answer, [], Closed, Status) :-
	debMode('lexical') ->
		lexical_reasoning(PrId, Answer, Closed, Status)
	; debMode('neg_cont') ->
		contradiction_negation_based(PrId, Answer, Closed, Status)
	; debMode('sub_ent') ->
		entailment_similarity_based(PrId, Answer, Closed, Status)
	; lexical_reasoning(PrId, Answer, Closed, Status).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% lexical classifier
% Acc .768 Prec .73, Rec .71
lexical_reasoning(PrId, Answer, Closed, 'Terminated') :-
	contradiction_negation_based(PrId, Ans1, Cl1, _Stat1),
	entailment_similarity_based(PrId, Ans2, Cl2, _Stat2),
	( Ans1 = 'no' ->
		Answer = Ans1,
		Closed = Cl1
	  ; Answer = Ans2,
		Closed = Cl2
	).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% gives 1% incerase in accuracy if combined
% Acc .67, Prec .94, Rec .26
contradiction_negation_based(PrId, Answer, Closed, _Term) :-
	( probID_to_lemma_list(PrId, PrL, CoL, _) -> true
	  ; probID_to_token_list(PrId, PrL, CoL)
	),
	subtract(PrL, CoL, List1),
	subtract(CoL, PrL, List2),
	append(PrL, CoL, AllL),
	length(AllL, AB),
	append(List1, List2, List),
	length(List, A1B1),
	Thr is A1B1/AB,
	( intersection(['no', 'not', 'nobody', 'nothing', 'none'], List, [_|_]),  Thr =< 0.3   ->
	  	Answer = 'no',
		Closed = 'closed'
	  ; Answer = 'unknown',
		Closed = 'open'
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Acc .66, Prec .52, Rec .45
entailment_similarity_based(PrId, Answer, Closed, _Term) :-
	( probID_to_lemma_list(PrId, PrL, CoL, _) -> true
	  ; probID_to_token_list(PrId, PrL, CoL)
	),
	subtract(CoL, PrL, DiffL_C_P),
	length(DiffL_C_P, C_P),
	( subtract(DiffL_C_P, ['a', 'the', 'an'], []) ->
 		Answer = 'yes',
		Closed = 'closed'
	; C_P =< 1 ->
	    Answer = 'yes',
		Closed = 'closed'
	; Answer = 'unknown',
	  Closed = 'open'
	).





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% problem id to tokens of premises and copnclusion
probID_to_token_list(PrID, PrTok, CoTok) :-
	sen_id(_, PrID, 'p', _, Premise),
	sen_id(_, PrID, 'h', _, Conclusion),
	!,
	atomic_list_concat(PrTokens, ' ', Premise),
	atomic_list_concat(CoTokens, ' ', Conclusion),
	maplist(downcase_atom, PrTokens, PrTok),
	maplist(downcase_atom, CoTokens, CoTok).
