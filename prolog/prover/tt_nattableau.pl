%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: Tableau Prover for Natural Logic
%     Version: 12.06.12
%      Author: lasha.abzianidze{at}gmail.com
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%    Defining operators and loading files
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module('../xml/xml_output', [output_XML/3]).
% swipl -q --goal=main --toplevel=halt --stand_alone=true --foreign=save -o langpro -c llf2.pl
:- use_module('../printer/gui_tree', [displayTree/3]).
:- use_module('../rules/rule_hierarchy', [sub_rule/2, rule_eff_order/1]).
:- use_module('../lambda/lambda_tt', [op(605, xfy, ~>)]).
:- use_module('../lambda/type_hierarchy', [sub_type/2]).
:- use_module('tableau_analysis', [stats_from_tree/2, theUsedrules_in_tree/2]).
:- use_module('../printer/reporting', [report/1]).
:- use_module('../rules/rules', [op(610, xfx, ===>), r/6, admissible_rules/1]).
:- use_module('../utils/generic_preds', [rotate_list/2]).
:- use_module('../utils/user_preds', [
	ttExp_to_ttTerm/2, uList2List/2, uList_to_ord_set/2, choose/3, match_remove/3,
	ul_append/2, patt_remove/3, add_new_elements/3, list_substitution/4
	]).
:- use_module('../llf/ttterm_preds', [
	ttTerms_same_type/2, extract_lex_NNPs_ttTerms/4
	]).
:- use_module('tableau_utils', [
	assignIds/4, subtract_nodes/4, select_relevant_rules/3, ttTerms_to_nodes_sig/6,
	get_closure_rules/2, single_branch_model_rules/2
	]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%				Tableau Proof
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Takes list of TTterms with True and a list of
% TTterms with sign False, generates tableau tree
% and branch list, and checks the input on closure
% without GUI
reason(KB_XP, T_TermList, F_TermList) :-
	reason(KB_XP, T_TermList, F_TermList, _Status).

reason(KB_XP, T_TermList, F_TermList, Status) :-
	generateTableau(KB_XP, T_TermList, F_TermList, BrList, _Tree, Status), !,
	%( theUsedrules_in_tree(Tree, [H|T]) -> report([[H|T]]); true ),
	%length(BrList, BrNumber), write('# Branches: '), write(BrNumber),
	%closed(BrList).
	BrList = [].


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Takes list of TTterms with True and a list of
% TTterms with sign False, generates tableau tree
% and branch list, and checks the input on closure
% with GUI
greason(KB_XP, T_TermList, F_TermList, Info) :- % remove problem ID from arg list
	Info = [Problem_Id, Mode, Align],
	( debMode('proof_tree') -> true; assertz(debMode('proof_tree')) ),
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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% generateTableau(Prem, Concl, BrList, Tree)
% generates tableau proof in styles of
% a list of branches and a tree
generateTableau(KB-XP1, T_TermList, F_TermList, BrList, Tree, Status) :-
	/*F_TermList = [], T_TermList = [] ->
		writeln('No premise & hypothesis'), fail;
	F_TermList = [] ->
		writeln('No hypothesis'), fail;
	T_TermList = [] ->
		writeln('No premise'), fail; */
	maplist(ttExp_to_ttTerm, T_TermList, T_TTlist), % allows to abreviate ttterms in test suite
	maplist(ttExp_to_ttTerm, F_TermList, F_TTlist), % allows to abreviate ttterms in test suite
	append(T_TTlist, F_TTlist, List), %print_ttTerm_to_gqtTerms(List), % debug printing
	(ttTerms_same_type(List, Type) ->
		ttTerms_to_nodes_sig(T_TTlist, F_TTlist, Type, Nodes, Sig, (Ent_Id, Con_Id)),
		% temporal, needs only names
		extract_lex_NNPs_ttTerms(Nodes, Lexicon, _, Names), %term_to_atom(Lexicon, At), writeln(At),
		append(Names, Sig, Signature), %!!! John from term, is added to Signature and doesnt have to wait for Arg push application
		%append(Names, Sig, Signa), findall(X, (member(X, Signa), \+atomic_list_concat([_,_|_], '@', X)), Signature), % avoids 's@man'
		nodes_to_SigBranch_tree_id(Nodes, Signature, Br, Tree, Node_Id),
		%( debMode('prlex') -> report([Lexicon]); true),
		%( debMode('subWN') -> subWN_from_wn(Lexicon); rels_from_wn(Lexicon) ),
		Count = [const_id(Ent_Id, _, Con_Id, _), node_id(Node_Id, _)],
		%catch( call_with_time_limit(5, once(expand([Br], BrList, Tree, Count))), _, (writeln('time_limit_exceeded'), fail) ).
		get_closure_rules(Lexicon, RelClRules),
		%rule_priority(EffRules),
		rule_eff_order(EffRules),
		( debMode('no_gq_llfs') ->
			%gq_rules(GQrules),
			append(_GQrules, EffRules, Rules)
		  ; Rules = EffRules
		),
		admissible_rules(AdmissRules),
		( debMode('noAdmissRules') -> subtract(Rules, AdmissRules, Rules1); Rules1 = Rules ),
		( debMode('single_branch_model') -> single_branch_model_rules(Rules1, Rules2); Rules2 = Rules1 ),
		select_relevant_rules(Lexicon, Rules2, RelRules),
		%RelRules = Rules,
		%report(['All Rules: ', Rules]),
		%report(['Relevant Rules: ', RelRules]),
		% check if tableau closes initially
		numlist(1, Node_Id, IdList),
		debMode(ral(RAL)),
		( debMode('complete_tree') -> Limit = RAL-'comp'; Limit = RAL-'part' ),
		( apply_closure_rules(IdList, Br, RelClRules, Cl_IDs, Cl_Rule, KB-XP) ->
			(BrList, Status, XP) = ([], ('Ter', 1), _UList),
			findSubTree(Tree, Node_Id, tree(_, closer([Cl_IDs, Cl_Rule])))
		; once(expand([Br], BrList, Tree, _Closing_IDs, KB-XP, Count, (RelRules, RelClRules), 0, Status, Limit)) %, % ClosingIDs is unspecified
		),
		uList_to_ord_set(XP, XP1)
	;	writeln('Inconsistency in node types - generateTableau'),
		fail
	)%,
	%stats_from_tree(Tree, s(Br_Num, Len, Max_Id)),
	%report(['NumOfBranches: ', Br_Num, '; NumOfRuleApp: ', Len, '; NumOfNodes: ', Max_Id])
	.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Creates Branch with Signature (BrSig) and Tree structure
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
nodes_to_SigBranch_tree_id(Nodes, Signature, BrSig, Tree, Last_Id) :-
	nodes_to_branch_tree_id(Nodes, RevBranch, Tree, node_id(0, Last_Id)),
	reverse(RevBranch, Branch),
	/*(Sig = [] ->
		Signature = [('c0', e)] % add default constant
	  ; Signature = Sig
	),*/
	BrSig = br(Branch, [], Signature), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% creates List of (node ID) pairs for branch and a tree with nodes as its leaves
nodes_to_branch_tree_id([Node | RestNodes], Branch, Tree, node_id(Old_Id, Last_Id)) :-
	!, Id is Old_Id + 1,
	Root = trnd(Node, Id, [], _),
	Tree = tree(Root, ChildList),
	Branch = [ndId(Node, Id) | RestBranch], % when addeing new nodes in the beginning of the branch
	%append(RestBranch, [ndId(Node, Id)], Branch), % when addeing new nodes in the end of the branch
	nodes_to_branch_tree_id(RestNodes, RestBranch, Child, node_id(Id, Last_Id)),
	( nonvar(Child) ->
		ChildList = [Child]
	; true ).

nodes_to_branch_tree_id([], [], _, node_id(Old_Id, Old_Id)).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% expands BranchList to NewBranchList (by multi steps) and
% constructively builds the structure Tree via matching
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/*expand(BranchList, NewBranchList, Tree, Closing_IDs, Count, Rules, RuleAppNum, Steps) :-
	nonvar(Closing_IDs),
	BranchList = [Branch | RestBranches],

*/
%expand(BranchList, NewBranchList, Tree, Closing_IDs, Count, Rules, RuleAppNum, Steps) :-

expand([], [], _Tree, _Closing_IDs, _, [const_id(E,E,C,C), node_id(N,N)], _Rules, Steps, ('Ter', Steps), _Limit) :-
	!.
/*
expand([Branch | RestBranches], RestBranches, Tree, UL_Closing_IDs, [const_id(E,E,C,C), node_id(N,N)], _Rules, Steps, Steps) :-
	Branch = br(BrNodes, _Hist, _Sig),
	uList2List(UL_Closing_IDs, Closing_IDs),
	member(ClIDs, Closing_IDs),
	findHeadNodes(BrNodes, _ClosureNodes, ClIDs),
	!, report(['Closure IDs: ', ClIDs, 'are closing a branch without rule application']),
	BrNodes = [ndId(_, BrId) | _], % when new nodes are added in the begining of the branch
	%append(_, [ndId(_, BrId)], BrNodes), % when new nodes are added in the end of the branch
	findSubTree(Tree, BrId, SubTree),
	SubTree = tree(_Root, ChildList),
	var(ChildList),
	!,
	ChildList = closer(ClIDs).
*/

expand(InitBrList, NewBrList, Tree, Cl_IDs, KB_XP, Count, Rules, RuleAppNum, Steps, Limit) :-
	Limit = AppLimit-Mode,
	%(0 is N mod 100 -> display(N), nl; true),
	Count = [const_id(Eid1, Eid, Cid1, Cid), node_id(Nid1, Nid)],
	Count1 = [const_id(Eid1, Eid2, Cid1, Cid2), node_id(Nid1, Nid2)],
	( ( Mode == 'comp' -> rotate_list(InitBrList, BrList); BrList = InitBrList ),
	  dirExpand(BrList, TempBrList, Tree, Cl_IDs, KB_XP, Count1, Rules, NewRules, RAppNum)
	), !,
	Count2 = [const_id(Eid2, Eid, Cid2, Cid), node_id(Nid2, Nid)],
	NewRuleAppNum is RuleAppNum + RAppNum,
	%report('Rule app: ', NewRuleAppNum),
	( (NewRuleAppNum < AppLimit; TempBrList = []) ->
		expand(TempBrList, NewBrList, Tree, Cl_IDs, KB_XP, Count2, NewRules, NewRuleAppNum, Steps, Limit)
	;	NewBrList = TempBrList,
		( debMode('prlim') -> report(['Rule application limit reached: ', AppLimit]); true),
		Steps = ('Lim', NewRuleAppNum) %'Limited'
	).


% if no more rule applications is possivbel then this clause assigns Model
expand(BrList, BrList, Tree, _Cl_IDs, _KB_XP,  [const_id(E,E,C,C), node_id(N,N)], _Rules, Steps, ('Ter', Steps), _Limit) :-
	BrList = [br([ndId(_,Id)|_], _, _) | _],
	%writeln('Model found'),
	( debMode('proof_tree') ->
		findSubTree(Tree, Id, tree(_, 'Model')) % marks open branch
	  ; true
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% dirExpand(BranchList, NewBranchList, Tree)
% expands BranchList to NewBranchList by single step
dirExpand([ br([],_,_) | Tail], Tail, _, _Closing_IDs, _KB_XP, [const_id(E,E,C,C), node_id(N,N)], Rules, Rules, 0) :-
	writeln('Should not happene but happened!').



dirExpand([Branch | RestBranches], NewBranchList, Tree, Closing_IDs, KB_XP, Count, (Rules,ClRules), (NewRules,ClRules), RAppNum) :-
	Branch = br(BrNodes, _Hist, _Sig),
	Count = [ConstId, NodeId],
	findRule(Branch, RuleType, IDs, Body, ConstId, Rules, RuleApp, NewHistory, KB_XP), %!!! _RuleId
	%(member(RuleId, [abst_dist, arg_dist]) -> report('New rule used: ', RuleId); true),
	%remove_first(RuleId, Rules, SubtrRules), append(SubtrRules, [RuleId], NewRules), % priority of rules change
	NewRules = Rules, % priority of rules doent change
	( RuleType = equi ->
		pruneBranch(BrNodes, IDs, CutBrNodes, _)
	  %Body = br([], _) -> %when there are no node sfor addition, mods_noun rule e.g.
		%CutBrNodes = BrNodes;
	% leave alone old nodes in the beginning of the branch
		%CutBrNodes = BrNodes
	% throw used nodes in the end of the branch
	; pruneBranch(BrNodes, IDs, TempBrNodes, Removed),
		reverse(Removed, RevRemoved),
		append(TempBrNodes, RevRemoved, CutBrNodes)
	),
	CutBranch = br(CutBrNodes, NewHistory, _),
	( debMode('proof_tree') ->
        BrNodes = [ndId(_, BrId) | _], % when new nodes are added in the begining of the branch
	    %append(_, [ndId(_, BrId)], BrNodes), % when new nodes are added in the end of the branch
		findSubTree(Tree, BrId, SubTree),
		SubTree = tree(_Root, ChildList),
		var(ChildList)
	  ; true
	),
	!,
	%( var(AppInfo) ->
	%	RuleApp =.. [RuleId, IDs]
	%  ;	RuleApp =.. [RuleId, IDs, AppInfo]
	%),
	growBranches(Body, CutBranch, NewBranches, SubTree, RuleApp, NodeId, KB_XP, ClRules, UL_New_Closing_IDs, New_Node_IDs),
	RuleApp = h(_RuleId, _, _, _, New_Node_IDs),
	%report('rule: ', RuleId),
	%append(RuleAppPart, [New_Node_IDs], RuleAppAsList),
	%RuleApp =.. [h | RuleAppAsList],
	%updateHistory(RuleApp, Hist, NewHistory),
	uList2List(UL_New_Closing_IDs, New_Closing_IDs),
	%expand_closure_ids(New_Closing_IDs, NewHistory, Ext_New_Closing_IDs),
	Ext_New_Closing_IDs = New_Closing_IDs, % temporally
	ul_append(Closing_IDs, Ext_New_Closing_IDs),
	%append(NewBranches, RestBranches, NewBranchList).% procesed branch is put at the beginning, may loop
	patt_remove(br([],_,_), NewBranches, Clean_NewBranches),
	length(NewBranches, N1),
	length(Clean_NewBranches, N2),
	RAppNum is N1 - N2 + 1,
	append(RestBranches, Clean_NewBranches, NewBranchList). % procesed branch is put in the end
	%append(Clean_NewBranches, RestBranches, NewBranchList). % order of branches doesn't change


% if the first branch is not closed that terminate
%dirExpand([Branch | Tail], [Branch | NewTail], Tree) :-
%	dirExpand(Tail, NewTail, Tree).

findRule(Branch, RuleType, IDs, Body, Cids, Rules, RuleApp, NewHist, KB_XP) :-
	Branch = br(BrNodes, Hist, Sig),
	%Cids = const_id(_,Eid,_,_),
	%BrHead = br(Head, Sig),
	%!!! no preference to equivalent rules wrt impl and gamma rules?
	member(RuleId, Rules),
	clause( r(RuleId, RuleType:_, (OldArgs, NewArgs, Cids), _, _, br(Head, Sig) ===> Body),   _Constraints),
	%findBestRule(RuleType, Body, Cids, Rules, RuleId, AppInfo, Head, Sig),
	findHeadNodes(BrNodes, Head, IDs),
	% gamma rule conditions might need backtracking and trying other old constants
	% while non-gamma rules doesn't need backtracking
	( RuleType = gamma ->
	    r(RuleId, RuleType:_, (OldArgs, NewArgs, Cids), _, KB_XP, br(Head, Sig) ===> Body)
	; %\+memberchk(h(RuleId, [], IDs, _, _), Hist), % weak pre-check for efficiency (not really)
	  % newArgs are _ to avoid a formula introducing fresh constants several times
	  once( r(RuleId, RuleType:_, (OldArgs, NewArgs, Cids), _, KB_XP, br(Head, Sig) ===> Body) )
    ),
	\+memberchk(h(RuleId, OldArgs, IDs, _NewArgs, _), Hist), %CHECK moving before testing constraints?
	RuleApp = h(RuleId, OldArgs, IDs, NewArgs, _),
	updateHistory(RuleApp, Hist, NewHist),
	ignore(Cids = const_id(Eid, Eid, Cid, Cid)),
	!.
	%genAllFreshArgs(ListFresh, Sig, TempLexicon, ConstId),    %!!! temporarily only one lexicon
	%union(ListConst, TempLexicon, NewLexicon).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% very first priority order

findBestRule(RuleType, Body, Cids, Rules, RuleId, AppInfo, Head, Sig) :-
	member(RuleId, Rules), % searching nonBranching nonFreshConstant
	  	clause( r(RuleId, RuleType:non, (AppInfo, Cids), _, _, br(Head, Sig) ===> br(N, S)),   _Constraints),
		Body = br(N, S)
	; member(RuleId, Rules), % searching Branching nonFreshConstant
	    clause( r(RuleId, RuleType:non, (AppInfo, Cids), _, _, br(Head, Sig) ===> [H|T]),   _Constraints),
		Body = [H|T]
	;	  %member(RuleId, Rules),
		%r(RuleId, RuleType:_, (AppInfo, Cids), br(Head, Sig) ===> Body, Constraints)
	  member(RuleId, Rules), % searching nonBranching FreshConstant
	  	clause( r(RuleId, RuleType:new, (AppInfo, Cids), _, _, br(Head, Sig) ===> br(N, S)),   _Constraints),
		Body = br(N, S)
	; member(RuleId, Rules), % searching Branching FreshConstant
	    clause( r(RuleId, RuleType:new, (AppInfo, Cids), _, _, br(Head, Sig) ===> [H|T]),   _Constraints),
		Body = [H|T].




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% findHeadNodes(BrNodes, RuleHead, IDs),
% finds IDs of first(!) nodes of BrNodes matching to
% the nodes of RuleHead - the head of the rule
findHeadNodes(BrNodes, [Head | Tail], [Id | ID_tail]) :- % also usable in reverse
	% select guarantees that each head node will be matched different nodes
	select(ndId(Head, Id), BrNodes, RestBrNodes),
	\+cyclic_term(Head), % can be solved by introducing Var(x) for X
	findHeadNodes(RestBrNodes, Tail, ID_tail).

findHeadNodes(_, [], []).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checks a branch against a list of closure ids
%check_nodes_for_closureIDs(BrNodes, ListClosureIDs) :-
%	member(ClIDs, ListClosureIDs),
%	findHeadNodes(BrNodes, _ClosureNodes, ClIDs).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% updateHistory(RuleType, IDs, AllOldConst, Id, History, NewHistory)
% If the record (applying Id rule to IDs nodes)
% is not in old History, than updates to NewHistory
% according to the Type of the rule % type is not used yet
updateHistory(RuleApp, History, NewHistory) :-
	add_ruleApp_to_history(RuleApp, History, TempHistory),
	%( is_list(Info) ->
	%findall( R_App, sub_rule(RuleApp, R_App), RuleApps),
	( bagof( R_App, sub_rule(RuleApp, R_App), RuleApps) -> true; RuleApps = [] ),
	%  ;	findall( h(Rule, Inf), sub_rule([RuleId, Info], [Rule, Inf]), RuleApps)
	%),
	add_new_elements(RuleApps, TempHistory, NewHistory).


add_ruleApp_to_history(RuleApp, History, NewHistory) :-
	memberchk(RuleApp, History) -> % not necessary
	%Info = ID_list ->     				%!!! permutation(IDs, ID_list)
		false
	;	NewHistory = [RuleApp | History].





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% pruneBranch(BrNodes, IDs, CutBrNodes, Removed)
% CutBrNodes are list of nodes after removing
% nodes with IDs from the list of nodes BrNodes
pruneBranch(BrNodes, [ID_h | ID_t], CutBrNodes, Removed) :-
	match_remove(ndId(Node, ID_h), BrNodes, NewBrNodes),
	( nonvar(Node) ->
		Removed = [ndId(Node, ID_h) | RestRemoved];
		true ),
	pruneBranch(NewBrNodes, ID_t, CutBrNodes, RestRemoved).

pruneBranch(BrNodes, [], BrNodes, []).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% findSubTree(Tree, Id, SubTree)
% finds SubTree of Tree such that
% Id is assigned to the root node of SubTree and
%
findSubTree(Tree, Id, SubTree) :-
	nonvar(Tree), nonvar(Id), %!!! subtree should become effiient
	Tree = tree(trnd(_,Id1,_,_), ChildList),
	(	Id1 == Id,
		SubTree = Tree % var(Childlist)?
	; 	nonvar(ChildList),
		member(Child, ChildList),
	  	findSubTree(Child, Id, SubTree)
	).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% growBranches(NewNodes, CutBranch, NewBranches, SubTree, SourceIDs)
% NewBranches are produced from CutBranch by adding NewNodes,
% SubTree is updated and new nodes are notated by SourceIDs
growBranches(Brs, CutBranch, NewBranches, SubTree, RuleApp, NodeId, KB_XP, ClRs,  Closing_IDs, New_Node_IDs) :-
	is_list(Brs), !,
	SubTree = tree(_, ChildList),
	growBranch_list(Brs, CutBranch, NewBranches, ChildList, RuleApp, NodeId, KB_XP, ClRs, Closing_IDs, New_Node_IDs).

%growBranches(br([], _), CutBranch, [CutBranch], _SubTree, _RuleApp, node_id(Nid, Nid)) :- % when there are no nodes for addition
%	!.

growBranches(Br, CutBranch, NewBranches, SubTree, RuleApp, NodeId, KB_XP, ClRs, Closing_IDs, [New_Node_IDs]) :-
	Br = br(NewNodes, _),
	is_list(NewNodes), !,
	SubTree = tree(_, [LeftTree]),
	growBranch(Br, CutBranch, NewBranch, LeftTree, RuleApp, NodeId, KB_XP, ClRs, Closing_IDs, New_Node_IDs),
	NewBranches = [NewBranch].



growBranch_list([Br|Rest], CutBranch, [NewBr|NewRest], [Tree|RestTrees], RuleApp, NodeId, KB_XP, ClRs, Closing_IDs, New_Node_IDs) :-
	NodeId = node_id(Nid1, Nid),
	growBranch(Br, CutBranch, NewBr, Tree, RuleApp, node_id(Nid1, Nid2), KB_XP, ClRs, Closing_IDs, New_Node_IDs_1),
	growBranch_list(Rest, CutBranch, NewRest, RestTrees, RuleApp, node_id(Nid2, Nid), KB_XP, ClRs, Closing_IDs, New_Node_IDs_2),
	append([New_Node_IDs_1], New_Node_IDs_2, New_Node_IDs).

growBranch_list([], _CutBranch, [], [], _RuleApp, node_id(Nid, Nid), _KB_XP, _ClRs, _Closing_IDs, []).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% growBranch(NodeList, CutBranch, NewBranch, SubTree, SourceIDs)
% NewBranch is produced from CutBranch by adding NodeList,
% SubTree is updated and new nodes are notated by SourceIDs
growBranch(Br, CutBranch, NewBranch, SubTree, RuleApp, NodeId, KB_XP, ClRs, Closing_IDs, New_Node_IDs) :-
	Br = br(NodeList, Sig),
	CutBranch = br(CutBrNodes, History, _),
	is_list(NodeList),
	% deletes new redundant nodes
	once(subtract_nodes(NodeList, CutBrNodes, FilteredCutBrNodes, NodeList_pId)), % iff branching adds nothing dont branch
	assignIds(NodeList_pId, NodeList_id, IdList, NodeId),
	findall(Loc_Id, member(ndId(_,Loc_Id), NodeList_id), New_Node_IDs),
% adding new nodes at the beginning of the branch
	reverse(NodeList_id, RevNodeList_id),
	append(RevNodeList_id, FilteredCutBrNodes, NewTabNodes),
% adding new nodes in the end of the branch
	%append(FilteredCutBrNodes, NodeList_id, NewTableauNodes),
	( apply_closure_rules(IdList, br(NewTabNodes,_,_), ClRs, Cl_IDs, Cl_Rule, KB_XP) ->
		ClRuleApp = [Cl_IDs, Cl_Rule],
		TableauNodes = [],
		ul_append(Closing_IDs, [Cl_IDs])
	; TableauNodes = NewTabNodes ),
	%remove_be_node_from_branch(br(TableauNodes, History, Sig), NewBranch), % ignoring be rule,maybe not necessary anymore
	NewBranch = br(TableauNodes, History, Sig),
	( debMode('proof_tree') ->
		growLeftistTree(NodeList_id, RuleApp, ClRuleApp, SubTree)
	  ; true
	).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% growLeftistTree(NodeList, SourceIDs, ClosureIDs, SubTree)
% grows SubTree in leftist fashion by NodeList, annotates nodes by SourceIDs
% and annotates the branch by ClosureIDs if it is closed
growLeftistTree( [ndId(Nd, Id) | Tail], RuleApp, ClRuleApp, SubTree) :-
	RuleApp = h(RuleId, OldArgs, IDs, NewArgs, _),
	( OldArgs = [] ->
	    ( NewArgs = [] ->
	        Rule_App =.. [RuleId, IDs]
	      ; Rule_App =.. [RuleId, IDs, NewArgs]
	    )
	  ; ( NewArgs = [] ->
	        Rule_App =.. [RuleId, OldArgs, IDs]
	      ; Rule_App =.. [RuleId, OldArgs, IDs, NewArgs]
	    )
	),
	SubTree = tree(trnd(Nd, Id, Rule_App,_), ChildList),
	growLeftistTree(Tail, RuleApp, ClRuleApp, Child),
	( nonvar(Child), Child =.. [tree|_] ->
		ChildList = [Child]
	; nonvar(Child) ->
		ChildList = closer(ClRuleApp)
	; 	ChildList = Child
	).

growLeftistTree([], _, ClosureIDs, ClosureIDs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% if Branch has a be:[a,b]:T node than only one of a or b is remaind in Branch
remove_be_node_from_branch(br(TableauNodes, History, Sig), NewBranch) :-
	TTterm = (tlp(_,'be',_,_,_), np:_~>np:_~>s:_),
	member( ndId(nd(_, TTterm, [(C1,Ty1),(C2,Ty2)], true), _),  TableauNodes ), !, % removing causes problem in subtree searching
	( Ty2 = e ->
		TT1 = (C1,Ty1), TT2 = (C2,Ty2);
		TT2 = (C1,Ty1), TT1 = (C2,Ty2)
    ),
	list_substitution(TableauNodes, TT1, TT2, New_TableauNodes),
	list_substitution(History, TT1, TT2, New_History),
	list_substitution(Sig, TT1, TT2, Sig1),
	list_to_set(Sig1, New_Sig),
	NewBranch = br(New_TableauNodes, New_History, New_Sig).


remove_be_node_from_branch(Branch, Branch).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%	  	Checking Tableau on Closure
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Checks if Branch is closed and returns IDs of closing nodes

apply_closure_rules(IdList, Branch, ClRs, Cl_IDs, ClRule, KB_XP) :-
	Branch = br(BrNodes, _Hist, Sig),
	member(Id, IdList),
	member(ClRule, ClRs),
	clause( r(ClRule, closure, _, _Lex, _KB_XP, br(Head, Sig) ===> Body), _Constraints ),
	find_head_nodes_with_ids(BrNodes, Head, [Id | Rest]),
	\+memberchk(Id, Rest),
	r(ClRule, closure, _, _, KB_XP, br(Head, Sig) ===> Body),
	Cl_IDs = [Id | Rest],
	!.


find_head_nodes_with_ids(_, [], []).

find_head_nodes_with_ids(BrNodes, Head, [Id | ID_tail]) :- % also usable in reverse
	member(ndId(Node, Id), BrNodes),
	%once(choose(Head, Node, Rest)), %sick train-4063 not proved due to this
	choose(Head, Node, Rest),
	\+cyclic_term(Node), % can be solved by introducing Var(x) for X
	find_head_nodes_with_ids(BrNodes, Rest, ID_tail).
