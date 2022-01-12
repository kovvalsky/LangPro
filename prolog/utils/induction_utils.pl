%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module('induction_utils',
	[
		add_lex_to_id_ans/2,
		filterAns_prIDs_Ans/3,
		format_pairs/2,
		get_IDAs/2,
		has_rel_against_kb/3,
		has_rel_incomparables/2,
		kb_length/2,
		log_parameters/1,
		partition_as_prIDs_Ans/6,
		print_learning_stages/2,
		print_learning_phase_stats/3,
		print_kb_learning_stages/3,
		print_phase_stats/4,
		waif_cv3/3,
		write_induced_kb_in_file/3
	]).

:- use_module(library(pairs)).
:- use_module(library(random)).
:- use_module('../utils/user_preds.pl', [
	atom_char_occur/3, partition_list_into_N_even_lists/3, prob_input_to_list/2,
	prIDs_to_prIDs_Ans/2, diff/3,
	freqList_subtract/3, list_to_freqList/2, last_member/2, pairwise_append/2
	]).
%:- use_module('../printer/reporting', [write_parList/1]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                Partitioning data
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Partition problems in N parts and print label distribution of the parts
% Seed 990 gives the smallest cumDiff from 0 to 1000
partition_as_prIDs_Ans(Problems, Answers, Seed, N, OrdParts, CumDiff) :-
	prob_input_to_list(Problems, PrIDs),
	prIDs_to_prIDs_Ans(PrIDs, PrIDs_Ans1),
	filterAns_prIDs_Ans(PrIDs_Ans1, Answers, PrIDs_Ans),
	print_prID_Ans_dist(PrIDs_Ans, AllDist),
	format('~`=t Distribution in Partitions ~`=t~60|~n', []),
	% random_partition_of_list(PrIDs_Ans, Seed, N, Parts),
	stratified_partition_of_list(PrIDs_Ans, Seed, N, Parts),
	maplist(print_prID_Ans_dist, Parts, Parts_Dist),
	mismatch_rate(AllDist, Parts_Dist, 0, CumDiff),
	format('Cummulative Difference: ~1f%~n', [CumDiff]),
	maplist(sort(1, @=<), Parts, OrdParts).

%---------------------------------
% Print label distribution (%) from the problem-ans list
print_prID_Ans_dist([], Distribution) :-
	!, Distribution = [0, 0, 0],
	format('Yes:~1f%  No:~1f%  Unk:~1f%~n', Distribution).

print_prID_Ans_dist(PrIDs_Ans, Distribution) :-
	length(PrIDs_Ans, N),
	prID_Ans_distribution(PrIDs_Ans, Lab_cnt),
	findall(Per, (
		member(A, ['yes', 'no', 'unknown']),
		once((memberchk(A-Cnt, Lab_cnt); Cnt=0)),
		Per is 100*Cnt/N
	), Distribution),
	format('Yes:~1f%  No:~1f%  Unk:~1f%~n', Distribution).

%--------------------------------------
% Calculate cumulative difference between a vector and a list of vectors
mismatch_rate(Dist, [D|Dists], Rate0, Rate) :-
	!, maplist(diff, Dist, D, Diff),
	sum_list([Rate0 | Diff], Difference),
	mismatch_rate(Dist, Dists, Difference, Rate).

mismatch_rate(_, [], Rate, Rate).

%---------------------------------
% Get label distribution from the prob-ans list
prID_Ans_distribution(PrIDs_Ans, Lab_cnt) :-
	pairs_keys_values(PrIDs_Ans, _, Answers),
	list_to_freqList(Answers, Lab_cnt1),
	keysort(Lab_cnt1, Lab_cnt).

%-------------------------------------------
% partition List in random N parts
random_partition_of_list(List, Seed, N, Parts) :-
	set_random(seed(Seed)),
	random_permutation(List, Shuffled),
	partition_list_into_N_even_lists(Shuffled, N, Parts).

% partition List in random N parts
stratified_partition_of_list(ID_Lab_List, Seed, N, Parts) :-
	set_random(seed(Seed)),
	random_permutation(ID_Lab_List, Sh_ID_Lab_List),
	transpose_pairs(Sh_ID_Lab_List, Lab_ID_List),
	group_pairs_by_key(Lab_ID_List, Lab_IDs_List),
	findall(Ps, (
		member(Lab-IDs, Lab_IDs_List),
		maplist({Lab}/[ID,ID-Lab]>>true, IDs, Lab_IDs),
		partition_list_into_N_even_lists(Lab_IDs, N, Ps)
	), List_of_Parts),
	pairwise_append(List_of_Parts, Parts).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                Printing Knowledge Base
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Starting from Nth stage, print the stage number and the KB learned on that stage
print_learning_stages(StageN, [KB|Rest]) :-
	!, format('~`-t Stage ~w ~`-t~100|~n', [StageN]),
	maplist(writeln, KB),
	NextStage is StageN + 1,
	print_learning_stages(NextStage, Rest).

print_learning_stages(_, []).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% write induced knowledge in file that is readable by prolog
write_induced_kb_in_file(KB_cnt_srt, FileName, Config) :-
	open(FileName, write, S, [encoding(utf8), close_on_abort(true)]),
	% parlist parameters and config
	log_parameters(S, Config),
	% induced knowledge
	format(S, '~`%t Induced Knowledge ~`%t~50|~n', []),
	maplist(write_kb_as_term(S, 'ind_rel'), KB_cnt_srt),
	close(S).

%---------------------------
% Write a term built from functor and args to the Stream
write_kb_as_term(S, Func, Term) :-
	format(S, '~w(', Func),
	write_term(S, Term, [quoted(true)]),
	writeln(S, ').').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                     Heuristics for detecting a bad Fact wrt KB
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% List includes a bad fact wrt KB
% Lex keeps POS-tags of constants that can be informative for constant comparability check
has_rel_against_kb(List, Lex, KB) :-
	member(X, List),
	once(bad_fact(X, Lex, KB)),
	!.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% identifies bad/nonsensical facts
bad_fact(Fact, _Lex, KB) :-
	Fact =.. [F, A, B],
	memberchk(F, ['disj', 'ant_wn']),
	positively_rel_p_p(KB, A, B).

% isa_wn(full, empty)	for SICK-train-90
% are isa_wn relations added during abduction?
bad_fact(isa_wn(A, B), _Lex, KB) :-
	  memberchk(ant_wn(A, B), KB)
	; memberchk(disj(A, B), KB).

% don't learn knowkedge about determiners
% avoid learning isa_wn(a, s) from 3122
bad_fact(Fact, Lex, _KB) :-
	Fact =.. [_, A, B],
	member((A, Pos), Lex),
	member((B, Pos), Lex),
	memberchk(Pos, ['DT']).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% every word in A is positively related to some word in B
% symmetric
positively_rel_w_w(KB, A, B) :-
	( A = B
	; memberchk(isa_wn(A, B), KB)
	; memberchk(isa_wn(B, A), KB)
	; memberchk(sim_wn(A, B), KB)
	; memberchk(sim_wn(B, A), KB)
	), !.
	%! der_wn?

% Word is positively related to some word in a phrase
% non-symmetric,
% relates (young boy, boy), (young boy, kid) SICK-train-3
positively_rel_p_w(KB, P, W) :-
	atomic_list_concat(List, ' ', P),
	member(L, List),
	positively_rel_w_w(KB, W, L),
	!.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% symmetric positive relatedness of phrases
% relates (smile nearby, nearby smile)
positively_rel_p_p(KB, P1, P2) :-
	( pos_rel_p_p_(KB, P1, P2)
	; pos_rel_p_p_(KB, P2, P1)
	), !.

% all words in the first phrase is positively related to some word in another phrase
% non-symmetric
pos_rel_p_p_(KB, P1, P2) :-
	atomic_list_concat(Ws1, ' ', P1),
	maplist(positively_rel_p_w(KB, P2), Ws1).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
has_rel_incomparables(List, Lex) :-
	member(X, List),
	rel_incomparables(X, Lex),
	!.

%!!! This blocks disj(put@on, remove)
% disj(two, woman)	but bit risky !!
rel_incomparables(Fact, Lex) :-
	Fact =.. [_, A, B],
	% being in lexicon is a pre-condition for checking incomparability
	once(( member((A,_), Lex), member((B,_), Lex) )),
	findall(0, (
		member((A, PosA), Lex),
	   	member((B, PosB), Lex),
		comparable_pos_tags(PosA, PosB)
	), Incomp_Num),
	% makes findall more transparent
	Incomp_Num = [].

% this bloks examples like
% 305(walk, covered); 305(walk, nude);
comparable_pos_tags(A, B) :-
	atom_chars(A, [A1,A2|_]),
	atom_chars(B, [B1,B2|_]),
	( A = B
	; [A1, A2] = [B1, B2]
	; memberchk(A, ['CD', 'DT']),
	  memberchk(B, ['CD', 'DT'])
	; memberchk(A, ['JJ', 'RB']), % lone biker & jumps alone 87
	  memberchk(B, ['JJ', 'RB'])
	), !.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                     Rest of auxiliary predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%
% Keep those elements of PrAnsList that have labels from AnswerList
filterAns_prIDs_Ans(PrAnsList, AnswerList, Filtered_PrAnsList) :-
	findall( PrId-Ans, (
		member(PrId-Ans, PrAnsList),
		memberchk(Ans, AnswerList)
		), Filtered_PrAnsList).

%%%%%%%%%%%%%%%%%%%%%%%%
% Find what are differences between
prID_Ans_diff(PrIDs_A1:FL1:N1, PrIDs_A2:FL2:N2, PrIDs_A1_2:FL1_2:N1_2, PrIDs_A2_1:FL2_1:N2_1) :-
	length(PrIDs_A1, N1),
	length(PrIDs_A2, N2),
	prID_Ans_distribution(PrIDs_A1, FL1),
	prID_Ans_distribution(PrIDs_A2, FL2),
	subtract(PrIDs_A1, PrIDs_A2, PrIDs_A1_2),
	subtract(PrIDs_A2, PrIDs_A1, PrIDs_A2_1),
	length(PrIDs_A1_2, N1_2),
	length(PrIDs_A2_1, N2_1),
	prID_Ans_distribution(PrIDs_A1_2, FL1_2),
	prID_Ans_distribution(PrIDs_A2_1, FL2_1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% print problems sorted according to their solved/unsolved statuses and labels
print_learning_phase_stats(Failed0-Failed, Solved0-Solved, Cnt_Fact) :-
	format('~`-t Induced knowledge ~`-t~80|~n'),
	maplist(writeln, Cnt_Fact),
	% List of problems with different statuses Solved & Failed now/before
	length(Solved, S_N),
	format('~`-t Solved (~w) ~`-t~80|~n', [S_N]),
	print_phase_stats(Solved, Solved0, SS_Message, SS_N),
	format('~`-t Now Solved & Before Solved (~w) ~`-t~50|~n~w', [SS_N, SS_Message]),
	print_phase_stats(Solved, Failed0, SF_Message, SF_N),
	format('~`-t Now Solved & Before Failed (~w) ~`-t~50|~n~w', [SF_N, SF_Message]),
	length(Failed, F_N),
	format('~`-t Failed (~w) ~`-t~80|~n', [F_N]),
	print_phase_stats(Failed, Solved0, FS_Message, FS_N),
	format('~`-t Now Failed & Before Solved (~w) ~`-t~50|~n~w', [FS_N, FS_Message]),
	print_phase_stats(Failed, Failed0, FF_Message, FF_N),
	format('~`-t Now Failed & Before Failed (~w) ~`-t~50|~n~w', [FF_N, FF_Message]).

%%%%%%%%%%%%%%%%%%%%%%%%%%
% print as
% label (N): 213, 2324, 434, 5435
print_phase_stats(IDA1, IDA2, Message, N) :-
	maplist([(ID,A), ID-A]>>true, IDA1, PrIDA1),
	maplist([(ID,A), ID-A]>>true, IDA2, PrIDA2),
	intersection(PrIDA1, PrIDA2, PrIDA),
	length(PrIDA, N),
	transpose_pairs(PrIDA, APrID0),
	sort(APrID0, APrID),
	group_pairs_by_key(APrID, A_PrIDs),
	findall( M, (
		member(A-PrIDs, A_PrIDs),
		length(PrIDs, Len),
		format(atom(M), '~w~t(~w):~15| ~w~n', [A, Len, PrIDs])
		), Ms),
	atomic_list_concat(Ms, Message).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Print learned knowledge according to the stages
print_kb_learning_stages(List_of_Cnt_KB, Cnt_KB_srt, KB) :-
	length(List_of_Cnt_KB, Stages),
	format('~`=t All Learned Knowledge (~w stages) ~`=t~100|~n', [Stages]),
	print_learning_stages(1, List_of_Cnt_KB),
	% print all learned knowledge together
	append(List_of_Cnt_KB, Cnt_KB),
	sort(1, @>=, Cnt_KB, Cnt_KB_srt), % sort according to the 1st arg and descending
	maplist([A,B,A-B]>>true, _, KB, Cnt_KB_srt),
	length(Cnt_KB_srt, Len),
	format('~`=t All together (~w rels) ~`=t~100|~n', [Len]),
	maplist(writeln, Cnt_KB_srt).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% record configuration and parameters
log_parameters(Config) :-
	current_output(Source),
	log_parameters(Source, Config).


log_parameters(Source, Config) :-
	findall(P, (
		debMode(P), P \= anno_dict(_)
	), Pars),
	format(Source, '~`%t Parameters of parList ~`%t~50|~n%%% ~w~n~n', [Pars]),
	format(Source, '~`%t Induction config ~`%t~50|~n%%% ~w~n', [Config]).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
format_pairs(_Format, []) :- !.

format_pairs(Format, [A-B | L_AB]) :-
	format(Format, [A, B]),
	format_pairs(Format, L_AB).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
waif_cv3(Train, Dev, Eval) :-
	debMode(waif(FileName)), !,
	format(atom(Train), '~w.T',[FileName]),
	format(atom(Dev), '~w.D',  [FileName]),
	format(atom(Eval), '~w.E', [FileName]).

waif_cv3('exp.T', 'exp.D', 'exp.E').


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Add lexicon and kb to problem id and answer pair
add_lex_to_id_ans(ID_Ans, (ID,Ans,Lex)) :-
	ID_Ans =.. [_, ID, Ans],
	%write(ID),
	( problem_to_ttTerms('both', ID, PTT, HTT, AlPTT, AlHTT, _KB) ->
		append([PTT, HTT, AlPTT, AlHTT], TTterms),
		extract_lex_NNPs_ttTerms(TTterms, LexPos, _, _Names),
		findall(L, member((L,_), LexPos), LexList),
		list_to_ord_set(LexList, Lex)
	; Lex = []
	).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Get IDAs from IDAs or IDALs
get_IDAs(IDALs, IDAs) :-
	findall((ID,A), (
		member(E, IDALs),
		once((E = (ID,A,_); E = (ID,A); E = (ID-A-_); E = (ID-A)))
	), IDAs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Calculate length of KB as a sum of lengths of its relations
% Length of a relation is 1 + sum of arg lengths
% this is a length in terms of constants not characters
kb_length(KB, N) :-
	maplist(rel_length, KB, Ls),
	sum_list(Ls, N).

rel_length(Rel, N) :-
	Rel =.. [R|Args],
	maplist(llf_atom_length, [R|Args], Ls),
	sum_list(Ls, N).

llf_atom_length(Atom, L) :-
	atom_char_occur('@ ', Atom, N),
	L is N + 1. % splitting into N+1 piecies
