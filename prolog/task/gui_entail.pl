% should be loaded with entail.pl

:- use_module('../printer/gui_tree', [displayTree/3]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checks on GUI entailment a problem with its Id
% uses a single reading
gentail(Problem_Id) :-
	gentail('no_align', Problem_Id).

gentail(Align, Problem_Id) :-
	gentail(Align, [], Problem_Id).

gentail(Align, KB0, Problem_Id) :-
	set_rule_eff_order, % defines an effciency order of rules
	once(sen_id(_, Problem_Id, _, Answer, _)),
	%problem_id_TTterms(Problem_Id, Prem_TTterms, Hypo_TTterms),
	( Align == 'align' ->
		problem_to_ttTerms(Align, Problem_Id, _, _, Prem_TTterms, Hypo_TTterms, KB1)
	  ; problem_to_ttTerms('no_align', Problem_Id, Prem_TTterms, Hypo_TTterms, _, _, KB1)
	),
	append(KB0, KB1, KB01),
	list_to_ord_set(KB01, KB),
	append(Prem_TTterms, Hypo_TTterms, TTterms),
	atomic_list_concat(['LLF_Prob-', Problem_Id], FileName),
	( debMode('tex') -> latex_probs_llfs([Problem_Id], FileName); true ),
	( Prem_TTterms = [], Hypo_TTterms = [] ->
		writeln('Problem with this id plausibly does not exist!')
	; Prem_TTterms = [] ->
		writeln('No premises found for this problem!')
	; Hypo_TTterms = [] ->
		writeln('No hypothesis found for this problem!')
	;	% Reason! problem is ok
	  Answer = 'no' ->
		greason(KB-XP, TTterms, [], [Problem_Id, 'no', Align])
	; Answer = 'yes' ->
		greason(KB-XP, Prem_TTterms, Hypo_TTterms, [Problem_Id, 'yes', Align])
	; greason(KB-XP, Prem_TTterms, Hypo_TTterms, [Problem_Id, 'yes', Align]) ->
		true
	; greason(KB-XP, TTterms, [], [Problem_Id, 'no', Align])
	),
	format('XP: ~w~n', [XP]).

% TODO: remove redundancy from this predicate
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% doesnt take into account answer of the problem
gentail_no_answer(Problem_Id) :-
	gentail_no_answer('no_align', Problem_Id).

gentail_no_answer(Align, Problem_Id) :-
	gentail_no_answer(Align, [], Problem_Id).

gentail_no_answer(Align, KB0, Problem_Id) :-
	set_rule_eff_order, % defines an effciency order of rules
	once(sen_id(_, Problem_Id, _, Answer, _)),
	%problem_id_TTterms(Problem_Id, Prem_TTterms, Hypo_TTterms),
	( Align == 'align' ->
		problem_to_ttTerms(Align, Problem_Id, _, _, Prem_TTterms, Hypo_TTterms, KB1)
	  ; problem_to_ttTerms('no_align', Problem_Id, Prem_TTterms, Hypo_TTterms, _, _, KB1)
	),
	append(KB0, KB1, KB01),
	list_to_ord_set(KB01, KB),
	atomic_list_concat(['LLF_Prob-', Problem_Id], FileName),
	( debMode('tex') -> latex_probs_llfs([Problem_Id], FileName); true ),
	append(Prem_TTterms, Hypo_TTterms, TTterms),
	( Prem_TTterms = [], Hypo_TTterms = [] ->
		writeln('Problem with this id plausibly does not exist!')
	; Prem_TTterms = [] ->
		writeln('No premises found for this problem!')
	; Hypo_TTterms = [] ->
		writeln('No hypothesis found for this problem!')
	;	% Reason! problem is ok
	  Answer = 'no' ->
		%append(Prem_TTterms, Hypo_TTterms, TTterms),
		ignore(greason(KB-_, Prem_TTterms, Hypo_TTterms, [Problem_Id, 'yes', Align])),
		greason(KB-XP, TTterms, [], [Problem_Id, 'no', Align])
	; Answer = 'yes' ->
		ignore(greason(KB-_, TTterms, [], [Problem_Id, 'no', Align])),
		greason(KB-XP, Prem_TTterms, Hypo_TTterms, [Problem_Id, 'yes', Align])
	; greason(KB-XP, Prem_TTterms, Hypo_TTterms, [Problem_Id, 'yes', Align]) ->
		true
	; %append(Prem_TTterms, Hypo_TTterms, TTterms),
	  greason(KB-XP, TTterms, [], [Problem_Id, 'no', Align])
	),
	format('XP: ~w~n', [XP]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Take a problem id and a sign and assign this sign to all sentences in the problem
% used for analysis of single sentences
ganalysis(Sign, Problem_Id) :-
	problem_to_ttTerms('no_align', Problem_Id, Prem_TTterms, Hypo_TTterms, _, _, KB),
	%findall(ccg(Id, CCGTree),
	%		( sen_id(Id, Problem_Id, _, _, _),  ccg(Id, CCGTree) ),
	%		CCG_IDs
	%),
	%ccgs_to_llfs_latex(CCG_IDs),
	atomic_list_concat(['LLF_Prob-', Problem_Id], FileName),
	( debMode('tex') -> latex_probs_llfs([Problem_Id], FileName); true ),
	append(Prem_TTterms, Hypo_TTterms, TTterms),
	( Sign = 'true' ->
		greason(KB-XP, TTterms, [], Problem_Id)
	; Sign = 'false' ->
		greason(KB-XP, [], TTterms, Problem_Id)
	),
	format('XP: ~w~n', [XP]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checks on GUI entailment a problem with its Id
% uses several readings
% list_gentail(Problem_Id) :-
% 	list_gentail('no_align', Problem_Id).
%
% list_gentail(Align, Problem_Id) :-
% 	once(sen_id(_, Problem_Id, _, Answer, _)),
% 	%problem_id_list_TTterms(Problem_Id, List_Prem_TTterms, List_Hypo_TTterms),
% 	( Align == 'align' ->
% 		problem_to_list_ttTerms(Align, Problem_Id, _, _, List_Prem_TTterms, List_Hypo_TTterms, KB)
% 	  ; problem_to_list_ttTerms('no_align', Problem_Id, List_Prem_TTterms, List_Hypo_TTterms, _, _, KB)
% 	),
% 	%once(list_reason(List_of_Lists)).
% 	maplist(member, Prem_TTterms, List_Prem_TTterms),
% 	maplist(member, Hypo_TTterms, List_Hypo_TTterms),
% 	%once(append(TextList, [Hypo], TTterms)),
% 	( Answer = 'no' ->
% 		append(Prem_TTterms, Hypo_TTterms, New_Prem_TTterms),
% 		New_Hypo_TTterms = []
% 	  ; New_Prem_TTterms = Prem_TTterms,
% 		New_Hypo_TTterms = Hypo_TTterms
% 	),
% 	greason(KB-_, New_Prem_TTterms, New_Hypo_TTterms, Problem_Id).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/*list_reason(List_of_Lists) :-
	maplist(member, TTterms, List_of_Lists),
	once(append(TextList, [Hypo], TTterms)),
	reason(TextList, [Hypo]).

list_greason(List_of_Lists) :-
	maplist(member, TTterms, List_of_Lists),
	once(append(TextList, [Hypo], TTterms)),
	greason(TextList, [Hypo]).*/


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Takes list of TTterms with True and a list of
% TTterms with sign False, generates tableau tree
% and branch list, and checks the input on closure
% with GUI
greason(KB_XP, T_TermList, F_TermList, Info) :- % remove problem ID from arg list
	( debMode('proof_tree') -> true; assertz(debMode('proof_tree')) ),
	Info = [Problem_Id, Mode, Align],
	generateTableau(KB_XP, T_TermList, F_TermList, BrList, Tree, Status), !,
	( theUsedrules_in_tree(Tree, [H|T]) -> report([Problem_Id, ': ', [H|T]]); true ),
	%length(BrList, BrNumber), write('# Branches: '), write(BrNumber),
	report(['Tableau for "', Mode, '" checking is generated with ', Status, ' ruleapps']),
	%stats_from_tree(Tree, s(Br_Num, Len, Max_Id)),
	%report(['NumOfBranches: ', Br_Num, '; NumOfRuleApp: ', Len, '; NumOfNodes: ', Max_Id]),
	atomic_list_concat(['tableau', Problem_Id, Mode, Align], '-', FileName),
	( debMode('xml'); debMode('html') -> output_XML(Tree, Problem_Id, FileName); true ),
	displayTree(Tree, 12, Problem_Id),
	!,
	BrList = [].
	%gclosed(BrList, Tree, _). % what about the last argument?