:- op(601, xfx, (/)).
:- op(601, xfx, (\)).

:- ensure_loaded([lambda_tt,
				  lambda,
				  lexicon,
				  online_demo,
				  %'ccg_sen/temp_ccg',
				  %'ccg_sen/ccg', 'ccg_sen/sen',
				  %'ccg_sen/fracas_ccg', 
				  %'ccg_sen/fracas_sen',
				  %'ccg_sen/fracas_odd_ccg', 'ccg_sen/fracas_odd_sen', %train
				  %'ccg_sen/fracas_even_ccg', 'ccg_sen/fracas_even_sen',
				  %'ccg_sen/fracas-1-premise_ccg', 'ccg_sen/fracas-1-premise_sen',
				  %'ccg_sen/rte1-dev_ccg', 'ccg_sen/rte1-dev_sen',	
				  %'ccg_sen/my_test_ccg', 'ccg_sen/my_test_sen',
				  %'ccg_sen/tr_rte', 'ccg_sen/rte_tr_spl',	
				  %'ccg_sen/SICK_trial_ccg', 'ccg_sen/SICK_trial_sen',
				  %'ccg_sen/SICK_train_ccg', 'ccg_sen/SICK_train_sen',
				  %'ccg_sen/SICK_test_annotated_ccg', 'ccg_sen/SICK_test_annotated_sen',	
				  %'ccg_sen/syllogisms_ccg', 'ccg_sen/syllogisms_sen',		
				  latex_ccgtree,
				  %term_query,
				  ttterm_to_term,
				  latex_ttterm,
				  ccg_term,
				  ccgTerm_to_ttTerm,
				  ccgTerm_to_llf,
				  gen_quant,
				  correct_term,
				  aligner,
				  ner,
				  extract,
				  sent_sim,	
				  bag_of_words,	
				  ling,
				  %nattableau,
				  tt_nattableau,
				  ttterm_preds,	
				  type_hierarchy,		
				  assign_term, % assigns a term to tlp
				  recognize_MWE,
				  annotate,	
				  wn_preds,	
				  tableau_tree,	
				  entail				  			
				 ]).

:- dynamic latex_file_stream/1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% generates LambdaLogicalForms (LLF) from CCGtrees
% and writes in latex file as application trees.
% gen_llfs_latex(nonvar_List_of_CCG_IDs) - for processing specific CCGtrees
% gen_llfs_latex(Min_ID, Max_ID) - for processing CCGtrees of ID between Min_ID and Max_ID
% if Min_ID and Max_ID are unspecified then all CCGtrees are processed

gen_llfs_latex(List) :- 
	findall(ccg(Id, Tree), (member(Id, List), ccg(Id, Tree)), CCGs),
	ccgs_to_llfs_latex(CCGs).

gen_llfs_latex(Inf, Sup) :-
	(nonvar(Inf), nonvar(Sup) -> 
		findall(ccg(Id, Tree), (between(Inf, Sup, Id), ccg(Id, Tree)) , CCGs);
	 nonvar(Inf) -> 
	  	findall(ccg(Id, Tree), (ccg(Id, Tree), Inf =< Id), CCGs);
	 nonvar(Sup) ->
		findall(ccg(Id, Tree), (ccg(Id, Tree), Sup >= Id), CCGs);
	 findall(ccg(Id, Tree), ccg(Id, Tree), CCGs) 
	),
	ccgs_to_llfs_latex(CCGs).
	%maplist(ccg_to_ccg_term, CCGs).


probs_to_llfs_latex(Prob_IDs) :-
	probIds_to_senIds(Prob_IDs, Sen_IDs),
	gen_llfs_latex(Sen_IDs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% returns sentence id list from problem id list
probIds_to_senIds([Prob_ID | Prob_Rest], Sen_IDs) :-
	!, findall(ID, sen_id(ID, Prob_ID,_,_,_), IDs),
	probIds_to_senIds(Prob_Rest, Sen_Rest),
	append(IDs, Sen_Rest, Sen_IDs).
	
probIds_to_senIds([], []).
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ccgs_to_llfs_latex(CCG_IDs)
% creates tex file and writes well-formed LLFs obtained from CCG_IDs
% writes percentage of well-formed LLFs on the screen 
ccgs_to_llfs_latex(CCG_IDs) :-
	(exists_directory('latex') -> true; make_directory('latex')),
	( debMode(eccg) -> 
		open('latex/gen_ellfs.tex', write, S, [encoding(utf8), close_on_abort(true)])
	  ;	open('latex/gen_llfs.tex',  write, S, [encoding(utf8), close_on_abort(true)])
	),
	asserta(latex_file_stream(S)),
	latex_ttTerm_preambule(S),
	write(S, '\\begin{document}\n'),
	%retractall(event_index), % temporarily here
	%maplist(ccg_to_lambda_term_latex(S), CCG_IDs, TTterm_IDs), % for ttterms solution 1
	maplist(ccg_to_abst_acg(S), CCG_IDs, TTterm_IDs), % for acg abstract level
	!,
	write(S, '\\end{document}'),
	close(S),
	findall(ccg(Id, TTterm), (member(ccg(Id, TTterm), TTterm_IDs), nonvar(TTterm)), WF_TTterms),	
	length(WF_TTterms, Num), 
	%findall(XX, member(ccg(XX, _), WF_TTterms), Output), write(Output),
	length(TTterm_IDs, Total),
	format(atom(Per), '~2f', [Num * 100 / Total]),
	atomic_list_concat([Per, '% (', Num, ' from ', Total, ') of LLFs were generated\n'], Message),
	write(Message).	



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ccg_to_abst_acg(S, CCG_ID, TTterm_ID)
ccg_to_abst_acg(S, CCG_ID, TTterm_ID) :-
	CCG_ID = ccg(Id, CCGTree),
	TTterm_ID = ccg(Id, GQTT), 
	( debMode('pr_sen') -> sen_id(Id,_,_,_,Sen), report([Id,': ',Sen]); true ),
	report([Id]),
	% print sentence and CCGtree
	sen_id_latex(S, Id),	
	ccgTree_to_tikzpicture(S, CCGTree), 				% print
	% CCGtree to ccgTerm
	ccgIDTree_to_ccgIDTerm(CCG_ID, ccg(Id, CCGTerm)),
	latex_ttTerm_print_tree(S, 2, CCGTerm), 			% print
	ne_ccg(CCGTerm, CCGTerm_1),
	%latex_ttTerm_print_tree(S, 6, CCGTerm_1), 			% print
	clean_ccgTerm_once(CCGTerm_1, CCGTerm_2),
	%latex_ttTerm_print_tree(S, 6, CCGTerm_2),			% print 
	CCGTerm_final = CCGTerm_2,
	correct_ccgTerm(CCGTerm_final, Corr_CCGTerm_final),
	print_used_lexical_rules(Id, Corr_CCGTerm_final),	% print
	latex_ttTerm_print_tree(S, 2, Corr_CCGTerm_final),	% print
	%% gen_quant_tt(Corr_CCGTerm_final, GQTTs),			% sick-train 7618 loops here
	%% maplist( latex_ttTerm_print_tree(S, 2), GQTTs ),	% print all GQ versions
	%% GQTTs = [GQTT|_],
	%% maplist( ttTerm_to_latexTerm, GQTTs, LatexTerms), maplist( writeln(S), LatexTerms). 
	once_gen_quant_tt(Corr_CCGTerm_final, GQTT),
	ttTerm_to_latexTerm(GQTT, LatexTerm), writeln(S, LatexTerm), writeln(S, '\n'), % pronts first LLF as a term
	latex_ttTerm_print_tree(S, 6, GQTT).				% print the first GQ version

	
	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ccg_to_abst_acg(S, CCG_ID, TTterm_ID)
ccg_to_ccg_term(CCG_ID) :-
	ccgIDTree_to_ccgIDTerm(CCG_ID, ccg(Id, CCGTerm)),
	ne_ccg(CCGTerm, CCGTerm_1),
	clean_ccgTerm_once(CCGTerm_1, CCGTerm_2),
	CCGTerm_final = CCGTerm_2,
	correct_ccgTerm(CCGTerm_final, Corr_CCGTerm_final),
	print_used_lexical_rules(Id, Corr_CCGTerm_final).






		
		


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ccg_to_lambda_term_latex(S, CCG_ID, TTterm_ID)
% converst CCG_ID pair into CCGTerm, CCGTerm into ttTerms (may fail),
% then prints target sentence, CCG_ID, CCGterm, ttTerms in latex way on S chanelle 
ccg_to_lambda_term_latex(S, CCG_ID, TTterm_ID) :-
	CCG_ID = ccg(Id, CCGTree),
	% print sentence and CCGtree
	sen_id_latex(S, Id),	
	ccgTree_to_tikzpicture(S, CCGTree),
	% CCGtree to ccgTerm
	ccgIDTree_to_ccgIDTerm(CCG_ID, ccg(Id, CCGTerm)),
	ne_ccg(CCGTerm, CCGTerm_1),
	clean_ccgTerm_once(CCGTerm_1, CCGTerm_2),
	CCGTerm_final = CCGTerm_2,
	% print ccgTerm
	latex_ttTerm_print_tree(S, 6, CCGTerm_final), 
	%ignore(ccgTerms_to_ttTerms([CCG_ID_term_final], [TTterm_ID])),
	(	%getting TTterm
		ccgTerms_to_ttTerms([ccg(Id, CCGTerm_final)], [TTterm_ID]),
		TTterm_ID = tt_id(Id, TTterm),
		nl, write(Id), %write(' TTterms,'),
		latex_ttTerm_print_tree(S, 6,  TTterm_ID),
		%greason([TTterm], []);
		% normalization of TTterm
		ttTerm_to_norm_term(TTterm, Normal_Term, _Sig, _Lexicon, _),
		writeln(' yes'),
		latex_norm_term_print(S, Normal_Term)%,
		% reasoning 
		%assert_list(Sig, clean),
		%gvalid(Normal_Term ===> '*'),
		%write(' reasoning, YES')
		;
		% OTHERWISE
		nl, write(Id), 
		writeln(' No')
	).



latex_norm_term_print(S, Normal_Term) :-
	lambdaTerm_to_latex(Normal_Term, Latex_Term),
	write(S, Latex_Term),
	write(S, '\\\\').



/*
assert_list(List, clean) :-
	List = [Head | _],
	!,
	Head =.. [H | _],
	retractall(H),
	assert_list(List, noclean).
	
assert_list([], clean).

assert_list([H | Rest], noclean) :-
	!,
	assert(H),
	assert_list(Rest, noclean). 	

assert_list([], noclean).
*/
	





