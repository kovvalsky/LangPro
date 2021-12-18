%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%% Sentence Similarities %%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module('../utils/user_preds', [print_prob/1]).
:- use_module('../printer/reporting', [report/1]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Extracts lemmas from the ccg tree
% Analyze whole tree
ccgTree_to_lemmata(Tree, List) :-
	nonvar(Tree),
	Tree =.. [Funct | TreeL],
	Funct \= t,
	!,
	maplist(ccgTree_to_lemmata, TreeL, LList),
	append(LList, List).

% lemma from a terminal node
ccgTree_to_lemmata(Tree, List) :-
	Tree = t(_, _, Lemma, _, _, _),
	nonvar(Lemma),
	\+member(Lemma, ['.',',']) -> % here is some filter
		List = [Lemma]
	;   List = [].


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% problem id to lemmas of premise and conslusion with answer
probID_to_lemma_list(PrID, PrLemmas, CoLemmas, Ans) :-
	sen_id(Pid, PrID, 'p', Ans, _),
	sen_id(Cid, PrID, 'h', Ans, _), %memberchk(Ans, ['yes', 'unknown']),
	!,
	ccg(Pid, Tree1),
	ccg(Cid, Tree2),
	ccgTree_to_lemmata(Tree1, PrL),
	ccgTree_to_lemmata(Tree2, CoL),
	maplist(downcase_atom, PrL, PrLemmas),
	maplist(downcase_atom, CoL, CoLemmas).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% print the TEPs that has similar sentences modulo determiners
print_TEPs_a_the(N) :-
	findall(PrID,
		( sen_id(_, PrID, 'h', _, _),
		  similar_modulo_list(PrID, ['a', 'an', 'the'], N)
		),
		IDs),
	maplist(print_prob, IDs),
	length(IDs, Num),
	report(['Total: ', Num]).


% print those TEPS that satisfy shemmas PL and CL



similar_modulo_list(PrID, ModList, Thr) :-
	probID_to_lemma_list(PrID, PrL, CoL, 'yes'),
	PrL = ['a', N1 | _],
	CoL = ['the', N2 | _],
	N1 \= N2,
	\+once(word_hyp(N1, N2, _)),
	%once(word_hyp(N2, N1, _)),
	subtract(L1, L2, R1),
	subtract(L2, L1, R2),
	once( (	subtract(R1, ModList, Rest1), length(Rest1, N), N =< Thr
		  , subtract(R2, ModList, Rest2), length(Rest2, N), N =< Thr
		  )
	).



% print_schemma_TEP([[the], N, V], [[a], N, V]).
print_schemma_TEP(SCH1, SCH2) :-
	findall(PrID,
		( sen_id(_, PrID, 'h', _, _),
		  schemma_matches_TEP(PrID, SCH1, SCH2)
		),
		IDs),
	maplist(print_prob, IDs),
	length(IDs, Num),
	report(['Total: ', Num]).

% schemma for TEPS
schemma_matches_TEP(PrID, PS, CS) :-
	probID_to_lemma_list(PrID, PrL, CoL, _Ans),
	append(PS, PrL),
	append(CS, CoL),
	!.
