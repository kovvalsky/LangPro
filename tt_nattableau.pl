%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: Tableau Prover for Natural Logic
%     Version: 12.06.12
%      Author: lasha.abzianidze{at}gmail.com 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%    Defining operators and loading files 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:-op(610, xfx, ===>).

:- dynamic tree_structure/1.
tree_structure(nil).

:- ensure_loaded([%lambda,
				  lambda_tt, % new	
				  counters,	
				  knowledge,
				  lexicon,	
				  rules,
				  closure_rules,
				  %gq_rules,
				  rule_hierarchy,
				  gui_tree, % remove for compilation for online		
				  latex, 
				  test_suite,
				  user_preds,
				  xml_output,
				  closure_ids
				 ]).
				 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%           Auxiliary Predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% splitOldFresh(Constants, Old, Fresh, Const)	
% a list of Constants used by rules are splitted in three lists:
% Old constants list, Fresh constant list, Constants from the same formula 
/*splitOldFresh([], [], [], []).

splitOldFresh([H | T], Old, [H | RestFresh], Const) :-
	H = fresh(_,_),
	splitOldFresh(T, Old, RestFresh, Const).
	
splitOldFresh([H | T], [H | RestOld], Fresh, Const) :-
	H = old(_,_),
	splitOldFresh(T, RestOld, Fresh, Const).

splitOldFresh([H | T], Old, Fresh, Const) :-
	H = const(Atom),
	(atom(Atom), % ignore non atom constants and untapable ones (they are already in lexicon), formal proof
	 [] '|-' Atom :: Type ->
		Const = [Atom::Type | RestConst];
		Const = RestConst),
	splitOldFresh(T, Old, Fresh, RestConst).*/	
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% genAllFreshArgs(ListFresh, Lexicon, NewLexicon)
% goes through ListFresh = [fresh(Type1, Args1), fresh(Type2, Args2), ...]
% and generates Args_n list of constants Feeding Type_n
% and adds these typed constants to Lexicon	
/*genAllFreshArgs([], Lexicon, Lexicon, const_id(Eid, Eid, Cid, Cid)).

genAllFreshArgs(ListFresh, Lexicon, NewLexicon, ConstId) :-
	ListFresh = [fresh(Type, Args) | RestFresh],
	ConstId = const_id(Eid1, Eid, Cid1, Cid),
	ConstId1 = const_id(Eid1, Eid2, Cid1, Cid2),
	genFreshArgs(Type, Args, Lexicon, TempLexicon, ConstId1),
	ConstId2 = const_id(Eid2, Eid, Cid2, Cid),
	genAllFreshArgs(RestFresh, TempLexicon, NewLexicon, ConstId2).*/
	




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% genAllOldArgs(ListOld, Lexicon, AllOldConst)
% picks lists of old arguments from lexicon and
% returns in AllOldConst	
/*genAllOldArgs([], _, []).	
	
genAllOldArgs(ListOld, Lexicon, AllOldConst) :-
	ListOld = [old(Type, Args) | RestOld],
	genOldArgs(Type, Args, Lexicon), 
	genAllOldArgs(RestOld, Lexicon, OldConst),
	append(Args, OldConst, AllOldConst).*/
	
	

	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% assignIds(ListOfNodes, ID_ListOfNodes) 	
% ID_ListOfNodes is a ListOfNodes with IDs
assignIds([Nd | NdRest], [Nd | NdIdRest], IdList, NodeId) :-
	Nd = ndId(_,_),
	assignIds(NdRest, NdIdRest, IdList, NodeId).

assignIds([Nd | NdRest], [NdId | NdIdRest], [Id | IdList], node_id(Nid1, Nid)) :-
	nonvar(Nd),	
	Nd = nd(_,_,_,_),
	Id is Nid1 + 1,
	NdId = ndId(Nd, Id),
	assignIds(NdRest, NdIdRest, IdList, node_id(Id, Nid)).
	
assignIds([], [], [], node_id(Nid, Nid)).	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Nodes, Branch, Branch\Nodes, Nodes with ids taken from Branch 
subtract_nodes([], X, X, []).

subtract_nodes(NodeList, [], [], NodeList).

subtract_nodes(NodeList, CutBrNodes, NewFilteredCutBrNodes, NodeList_pId) :-
	NodeList = [Formula | Rest],
	( memberchk(ndId(Formula, Id), CutBrNodes), 
	  acyclic_term(Formula), %!!! checking on cycles, sick-3275 eccg
	  delete(CutBrNodes, ndId(Formula, Id), FilteredCutBrNodes) -> 
		NodeList_pId = [ndId(Formula, Id) | RestNodeList_pid],
		  subtract_nodes(Rest, FilteredCutBrNodes, NewFilteredCutBrNodes, RestNodeList_pid);
		NodeList_pId = [Formula | RestNodeList_pId],
		  subtract_nodes(Rest, CutBrNodes, NewFilteredCutBrNodes, RestNodeList_pId)).
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% type(Term, Type)
% Types Term as of type Type;
% used for typing inside the branches and uses
% local branch signature as environment
%:- dynamic branch_signature/1.
/*
type(Term, Type) :-
	branch_signature(Br_Sig),
	Br_Sig '|-' Term :: Type.
*/	

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%				Tableau Proof    
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% Takes list of TTterms with True and a list of
% TTterms with sign False, generates tableau tree
% and branch list, and checks the input on closure
% without GUI  
reason(T_TermList, F_TermList) :-
	reason(T_TermList, F_TermList, _Status).

reason(T_TermList, F_TermList, Status) :-
	generateTableau(T_TermList, F_TermList, BrList, _Tree, Status), !,
	%length(BrList, BrNumber), write('# Branches: '), write(BrNumber),
	%closed(BrList).
	BrList = [].


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% Takes list of TTterms with True and a list of
% TTterms with sign False, generates tableau tree
% and branch list, and checks the input on closure
% with GUI	
greason(T_TermList, F_TermList, Problem_Id) :- % remove problem ID from arg list	
	( debMode('proof_tree') -> true; assertz(debMode('proof_tree')) ),
	generateTableau(T_TermList, F_TermList, BrList, Tree, _Status), !,
	%length(BrList, BrNumber), write('# Branches: '), write(BrNumber),
	writeln('Tableau is generated'),
	%stats_from_tree(Tree, s(Br_Num, Len, Max_Id)),
	%report(['NumOfBranches: ', Br_Num, '; NumOfRuleApp: ', Len, '; NumOfNodes: ', Max_Id]),
	output_XML(Tree, Problem_Id, 'greason'),
	displayTree(Tree, 12, Problem_Id), 
	!,
	BrList = [].
	%gclosed(BrList, Tree, _). % what about the last argument?
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% generateTableau(Prem, Concl, BrList, Tree)
% generates tableau proof in styles of
% a list of branches and a tree
generateTableau(T_TermList, F_TermList, BrList, Tree, Status) :-
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
		extract_lex_NNPs_ttTerms(Nodes, _Lexicon, Names), %term_to_atom(Lexicon, At), writeln(At), 
		append(Names, Sig, Signature), %!!! John from term, is added to Signature and doesnt have to wait for Arg push application
		nodes_to_SigBranch_tree_id(Nodes, Signature, Br, Tree, Node_Id),
		%( debMode('lex') -> report([Lexicon]); true),
		%( debMode('subWN') -> subWN_from_wn(Lexicon); rels_from_wn(Lexicon) ), 
		Count = [const_id(Ent_Id, _, Con_Id, _), node_id(Node_Id, _)],
		%catch( call_with_time_limit(5, once(expand([Br], BrList, Tree, Count))), _, (writeln('time_limit_exceeded'), fail) ).
		%findall(Rule_name, r(Rule_name,_,_,_,_), Rules), % automatic retival of rules
		rule_priority(RulePr),
		%( debMode('no_gq_llfs') ->
		%	gq_rules(GQrules),
		%	append(GQrules, RulePr, Rules)
		%  ; 
		Rules = RulePr,
		%),
		% check if tableau closes initially
		numlist(1, Node_Id, IdList),
		rule_app_limit(Limit),
		( apply_closure_rules(IdList, Br, Cl_IDs) ->
			(BrList, Status) = ([], 1),
			findSubTree(Tree, Node_Id, tree(_, closer(Cl_IDs)))
		; once(expand([Br], BrList, Tree, _Closing_IDs, Count, Rules, 0, Status, Limit))%, % ClosingIDs is unspecified
			%remove_varTail_from_uList(Closing_IDs, Cl_IDs),
		    %report(['Closing ids: ', Cl_IDs])
		)			
	;	writeln('Inconsistency in node types - generateTableau'), 
		fail
	)%,
	%stats_from_tree(Tree, s(Br_Num, Len, Max_Id)),
	%report(['NumOfBranches: ', Br_Num, '; NumOfRuleApp: ', Len, '; NumOfNodes: ', Max_Id])
	.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% generateTableau_align(Prem, Concl, BrList, Tree)
% generates tableau proof in styles of
% a list of branches and a tree over aligned input
%generateTableau_with_align(T_TermList, F_TermList, BrList, Tree, Status) :-



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% converts list of true and false TTterms into list of nodes
% and creates a signature for the branch, assumes that types of TTs are the same
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
ttTerms_to_nodes_sig(T_TTlist, F_TTlist, Type, Nodes, Sig, (Ent_Id, Con_Id)) :-
	genFreshArgs(Type, Args, [], Sig, const_id(0, Ent_Id, 0, Con_Id)), %!!! John from term, must be added to Signature and mustnt wait for Arg push application
	( 	(Type = n:_; Type = pp) ->
			T_List = T_TTlist,
			F_List = F_TTlist,
			ArgList = Args
		;	maplist(apply_ttFun_to_ttArgs(Args), T_TTlist, T_List), 	
			maplist(apply_ttFun_to_ttArgs(Args), F_TTlist, F_List),
			ArgList = [] ),	
	maplist(ttTerm_to_node(true, ArgList), T_List, T_Nodes),
	maplist(ttTerm_to_node(false, ArgList), F_List, F_Nodes),
	append(T_Nodes, F_Nodes, Nodes).
	%list_to_ord_set(Sig, Signature), not necessary

ttTerms_to_nodes_sig(T_TTlist, F_TTlist, Type, Nodes, Sig, (Ent_Id, Con_Id)) :-
	genFreshArgs(Type, Args, [], Sig, const_id(0, Ent_Id, 0, Con_Id)), %!!! John from term, must be added to Signature and mustnt wait for Arg push application
	maplist(apply_ttFun_to_ttArgs(Args), T_TTlist, T_List),
	maplist(apply_ttFun_to_ttArgs(Args), F_TTlist, F_List),
	maplist(ttTerm_to_node(true, []), T_List, T_Nodes),
	maplist(ttTerm_to_node(false, []), F_List, F_Nodes),
	append(T_Nodes, F_Nodes, Nodes).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Converts a sign TF and TTexpression into a Node
ttTerm_to_node(TF, Args, TTExp, Node) :- % to be changed
	ttExp_to_ttTerm(TTExp, TTterm), % not necessary
	Node = nd([], TTterm, Args, TF).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% picks a list of old arguments from Signature, which feeds Type
genOldArgs(Type, [], _) :-
	sub_type(Type, t).

genOldArgs(Type, Args, Sig) :-
	nonvar(Type),
	sub_type(Type, Type1~>Type2),
	member((Term, Type1), Sig),
	Args = [ (Term, Type1) | RestArgs],
	genOldArgs(Type2, RestArgs, Sig).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% creates a list of constant arguments feeding Type
% and adds these constant::its_type to Signature  
genFreshArgs(Type, [], Sig, Sig, const_id(Eid, Eid, Cid, Cid)) :-
	sub_type(Type, t), !.
	
genFreshArgs(Type, Args, Sig, NewSig, const_id(Eid1, Eid2, Cid1, Cid2)) :- 
	nonvar(Type),
	sub_type(Type, Type1~>Type2),
	( 	sub_type(Type1, np:_) ->  % np:_ since np:_ subsumes e type
		I is Eid1 + 1, 
			atomic_list_concat([c, I], X),
			TT = (X, e),
	  		ConstId = const_id(I, Eid2, Cid1, Cid2);
	  	I is Cid1 + 1,
	  		atomic_list_concat(['P', I], X),
			TT = (X, Type1),
	  		ConstId = const_id(Eid1, Eid2, I, Cid2) ),  
	Args = [TT | RestArgs],
	%TempSig = [TT | Sig],
	append(Sig, [TT], TempSig), % motivates using old constant than new ones
	genFreshArgs(Type2, RestArgs, TempSig, NewSig, ConstId).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% feed_nodes_with_args(+Nodes, +Args); deterministic 
% matches arglist of Nodes to Args
feed_nodes_with_args([nd(_, _, Args, _) | Rest], Args) :-
	feed_nodes_with_args(Rest, Args), !.

feed_nodes_with_args([], _).	



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
	
expand([], [], _Tree, _Closing_IDs, [const_id(E,E,C,C), node_id(N,N)], _Rules, Steps, Steps, _Limit) :-
	!.
/*
expand([Branch | RestBranches], RestBranches, Tree, UL_Closing_IDs, [const_id(E,E,C,C), node_id(N,N)], _Rules, Steps, Steps) :-
	Branch = br(BrNodes, _Hist, _Sig),
	remove_varTail_from_uList(UL_Closing_IDs, Closing_IDs),
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

expand(BranchList, NewBranchList, Tree, Closing_IDs, Count, Rules, RuleAppNum, Steps, Limit) :-
	%length(BranchList, N), 
	%(0 is N mod 100 -> display(N), nl; true), 
	Count = [const_id(Eid1, Eid, Cid1, Cid), node_id(Nid1, Nid)],
	Count1 = [const_id(Eid1, Eid2, Cid1, Cid2), node_id(Nid1, Nid2)],
	dirExpand(BranchList, TempBranchList, Tree, Closing_IDs, Count1, Rules, NewRules),
	!,
	Count2 = [const_id(Eid2, Eid, Cid2, Cid), node_id(Nid2, Nid)],
	NewRuleAppNum is RuleAppNum + 1,
	AppLimit is Limit,  % ruleapp limit
	%report('Rule app: ', NewRuleAppNum),
	( (NewRuleAppNum < AppLimit; TempBranchList = []) -> 
		expand(TempBranchList, NewBranchList, Tree, Closing_IDs, Count2, NewRules, NewRuleAppNum, Steps, Limit)
	;	NewBranchList = TempBranchList, 
		( debMode('prlim') -> report(['Rule application limit reached: ', AppLimit]); true),
		Steps = 'Limited' 
	). 
	%length(TempBranchList, L), 
	%(L < 100 -> 
		%expand(TempBranchList, NewBranchList, Tree, Count2, NewRules); 
		%NewBranchList = TempBranchList, writeln('Limit reached')). 
	%expand(TempBranchList, NewBranchList, Tree, Count2).

% if no more rule applications is possivbel then this clause assigns Model	
expand(BranchList, BranchList, Tree, _Closing_IDs, [const_id(E,E,C,C), node_id(N,N)], _Rules, Steps, Steps, _Limit) :-
	BranchList = [br([ndId(_,Id)|_], _, _) | _],
	%writeln('Model found'), 
	( debMode('proof_tree') -> 
		findSubTree(Tree, Id, tree(_, 'Model')) % marks open branch
	  ; true
	). 
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% dirExpand(BranchList, NewBranchList, Tree)
% expands BranchList to NewBranchList by single step
dirExpand([ br([],_,_) | Tail], Tail, _, _Closing_IDs, [const_id(E,E,C,C), node_id(N,N)], Rules, Rules) :-
	writeln('Should not happene but happened!').



dirExpand([Branch | RestBranches], NewBranchList, Tree, Closing_IDs, Count, Rules, NewRules) :-
	Branch = br(BrNodes, _Hist, _Sig),
	Count = [ConstId, NodeId],
	findRule(Branch, RuleType, IDs, Body, ConstId, Rules, RuleApp, NewHistory), %!!! _RuleId
	%(member(RuleId, [abst_dist, arg_dist]) -> report('New rule used: ', RuleId); true),
	%remove_first(RuleId, Rules, SubtrRules), append(SubtrRules, [RuleId], NewRules), % priority of rules change
	NewRules = Rules, % priority of rules doent change
	( RuleType = equi -> 
		pruneBranch(BrNodes, IDs, CutBrNodes, _);
	  %Body = br([], _) -> %when there are no node sfor addition, mods_noun rule e.g.
		%CutBrNodes = BrNodes; 
	% leave alone old nodes in the beginning of the branch	
		%CutBrNodes = BrNodes 
	% throw used nodes in the end of the branch
		pruneBranch(BrNodes, IDs, TempBrNodes, Removed), 
		reverse(Removed, RevRemoved),
		append(TempBrNodes, RevRemoved, CutBrNodes)   
	),  
	CutBranch = br(CutBrNodes, NewHistory, _),
	BrNodes = [ndId(_, BrId) | _], % when new nodes are added in the begining of the branch
	%append(_, [ndId(_, BrId)], BrNodes), % when new nodes are added in the end of the branch
	( debMode('proof_tree') ->
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
	growBranches(Body, CutBranch, NewBranches, SubTree, RuleApp, NodeId, UL_New_Closing_IDs, New_Node_IDs),
	RuleApp = h(_RuleId,_,_,New_Node_IDs),	
	%report('rule: ', RuleId),
	%append(RuleAppPart, [New_Node_IDs], RuleAppAsList),
	%RuleApp =.. [h | RuleAppAsList], 
	%updateHistory(RuleApp, Hist, NewHistory),
	remove_varTail_from_uList(UL_New_Closing_IDs, New_Closing_IDs),
	expand_closing_ids(New_Closing_IDs, NewHistory, Ext_New_Closing_IDs), 
	ul_append(Closing_IDs, Ext_New_Closing_IDs), 
	%append(NewBranches, RestBranches, NewBranchList).% procesed branch is put at the beginning, may loop
	%remove(br([],_,_), NewBranches, Clean_NewBranches),
	discard(br([],_,_), NewBranches, Clean_NewBranches),
	append(RestBranches, Clean_NewBranches, NewBranchList). % procesed branch is put in the end


% if the first branch is not closed that terminate	
%dirExpand([Branch | Tail], [Branch | NewTail], Tree) :-
%	dirExpand(Tail, NewTail, Tree).	

findRule(Branch, RuleType, IDs, Body, Cids, Rules, RuleApp, NewHist) :-
	Branch = br(BrNodes, Hist, Sig),
	%Cids = const_id(_,Eid,_,_),
	%BrHead = br(Head, Sig),	
	( member(RuleId, Rules), % searching nonBranching nonFreshConstant
	  	clause( r(RuleId, RuleType:non, (AppInfo, Cids), br(Head, Sig) ===> br(N, S)),   _Constraints), 
		Body = br(N, S);
	  member(RuleId, Rules), % searching Branching nonFreshConstant	
	    clause( r(RuleId, RuleType:non, (AppInfo, Cids), br(Head, Sig) ===> [H|T]),   _Constraints), 
		Body = [H|T];

	  %member(RuleId, Rules),
		%r(RuleId, RuleType:_, (AppInfo, Cids), br(Head, Sig) ===> Body, Constraints)/* 

	  member(RuleId, Rules), % searching nonBranching FreshConstant
	  	clause( r(RuleId, RuleType:_, (AppInfo, Cids), br(Head, Sig) ===> br(N, S)),   _Constraints), 
		Body = br(N, S);
	  member(RuleId, Rules), % searching Branching FreshConstant	
	    clause( r(RuleId, RuleType:_, (AppInfo, Cids), br(Head, Sig) ===> [H|T]),   _Constraints), 
		Body = [H|T] %*/
	),
	findHeadNodes(BrNodes, Head, IDs),
	( RuleType = gamma -> 
		r(RuleId, RuleType:_, (AppInfo, Cids), br(Head, Sig) ===> Body)
		%(Constraints)
	  ; \+memberchk(h(RuleId, IDs, _), Hist),
		%once(Constraints)
		r(RuleId, RuleType:_, (AppInfo, Cids), br(Head, Sig) ===> Body)
	),
	%assert(branch_signature(Sig)),
	%Constraints,
	%retract(branch_signature(_)),
	%splitOldFresh(Constants, ListOld, ListFresh, ListConst),
	%genAllOldArgs(ListOld, Sig, AllOldConst),
	( RuleType = gamma -> 
		RuleApp = h(RuleId, AppInfo, IDs, _),
		\+memberchk(h(RuleId, AppInfo, IDs, _), Hist)
	; var(AppInfo) -> 
		RuleApp = h(RuleId, [], IDs, _)
	; RuleApp = h(RuleId, AppInfo, IDs, _)
	),
	updateHistory(RuleApp, Hist, NewHist),
	ignore(Cids = const_id(Eid, Eid, Cid, Cid)),
	!.
	%genAllFreshArgs(ListFresh, Sig, TempLexicon, ConstId),    %!!! temporarily only one lexicon
	%union(ListConst, TempLexicon, NewLexicon).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% findHeadNodes(BrNodes, RuleHead, IDs),
% finds IDs of first(!) nodes of BrNodes matching to 
% the nodes of RuleHead - the head of the rule	
findHeadNodes(BrNodes, [Head | Tail], [Id | ID_tail]) :- % also usable in reverse
	member(ndId(Head, Id), BrNodes),
	\+cyclic_term(Head), % can be solved by introducing Var(x) for X
	findHeadNodes(BrNodes, Tail, ID_tail).
	
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
		false;
		%write(RuleId), term_to_atom(Info, At), write('-'), writeln(At), % prints used rule
		NewHistory = [RuleApp | History].



	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% pruneBranch(BrNodes, IDs, CutBrNodes, Removed)	
% CutBrNodes are list of nodes after removing
% nodes with IDs from the list of nodes BrNodes
pruneBranch(BrNodes, [ID_h | ID_t], CutBrNodes, Removed) :-
	remove(ndId(Node, ID_h), BrNodes, NewBrNodes),
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
growBranches(Brs, CutBranch, NewBranches, SubTree, RuleApp, NodeId, Closing_IDs, New_Node_IDs) :-
	is_list(Brs), !,
	SubTree = tree(_, ChildList),
	growBranch_list(Brs, CutBranch, NewBranches, ChildList, RuleApp, NodeId, Closing_IDs, New_Node_IDs).

%growBranches(br([], _), CutBranch, [CutBranch], _SubTree, _RuleApp, node_id(Nid, Nid)) :- % when there are no nodes for addition
%	!.

growBranches(Br, CutBranch, NewBranches, SubTree, RuleApp, NodeId, Closing_IDs, New_Node_IDs) :-
	Br = br(NewNodes, _), 	
	is_list(NewNodes), !,
	SubTree = tree(_, [LeftTree]),
	growBranch(Br, CutBranch, NewBranch, LeftTree, RuleApp, NodeId, Closing_IDs, New_Node_IDs),
	NewBranches = [NewBranch].



growBranch_list([Br|Rest], CutBranch, [NewBr|NewRest], [Tree|RestTrees], RuleApp, NodeId, Closing_IDs, New_Node_IDs) :-
	NodeId = node_id(Nid1, Nid),
	growBranch(Br, CutBranch, NewBr, Tree, RuleApp, node_id(Nid1, Nid2), Closing_IDs, New_Node_IDs_1),
	growBranch_list(Rest, CutBranch, NewRest, RestTrees, RuleApp, node_id(Nid2, Nid), Closing_IDs, New_Node_IDs_2),
	append(New_Node_IDs_1, New_Node_IDs_2, New_Node_IDs).

growBranch_list([], _CutBranch, [], [], _RuleApp, node_id(Nid, Nid), _Closing_IDs, []).

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% growBranch(NodeList, CutBranch, NewBranch, SubTree, SourceIDs)
% NewBranch is produced from CutBranch by adding NodeList,
% SubTree is updated and new nodes are notated by SourceIDs  	
growBranch(Br, CutBranch, NewBranch, SubTree, RuleApp, NodeId, Closing_IDs, New_Node_IDs) :-
	Br = br(NodeList, Sig), 
	CutBranch = br(CutBrNodes, History, _),
	is_list(NodeList),
	% deletes new redundant nodes
	once(subtract_nodes(NodeList, CutBrNodes, FilteredCutBrNodes, NodeList_pId)), % iff branching adds nothing dont branch
	assignIds(NodeList_pId, NodeList_id, IdList, NodeId),
	findall(Loc_Id, member(ndId(_,Loc_Id), NodeList_id), New_Node_IDs), 
% adding new nodes at the beginning of the branch
	reverse(NodeList_id, RevNodeList_id), 
	append(RevNodeList_id, FilteredCutBrNodes, NewTableauNodes),
% adding new nodes in the end of the branch
	%append(FilteredCutBrNodes, NodeList_id, NewTableauNodes), 
	( findall(Cl_IDs,  apply_closure_rules(IdList, br(NewTableauNodes,_,_), Cl_IDs),  List_of_ClosureIDs),
	  List_of_ClosureIDs = [ClosureIDs | _]  -> 
		TableauNodes = [],
		ul_append(Closing_IDs, List_of_ClosureIDs)
	  ; 
		TableauNodes = NewTableauNodes 
	), 
	%remove_be_node_from_branch(br(TableauNodes, History, Sig), NewBranch), % ignoring be rule,maybe not necessary anymore
	NewBranch = br(TableauNodes, History, Sig),
	( debMode('proof_tree') -> 
		growLeftistTree(NodeList_id, RuleApp, ClosureIDs, SubTree)
	  ; true
	).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% growLeftistTree(NodeList, SourceIDs, ClosureIDs, SubTree)
% grows SubTree in leftist fashion by NodeList, annotates nodes by SourceIDs
% and annotates the branch by ClosureIDs if it is closed 
growLeftistTree( [ndId(Nd, Id) | Tail], RuleApp, ClosureIDs, SubTree) :-
	RuleApp = h(RuleId, Args, IDs, _),
	( Args \= [] ->
		Rule_App =.. [RuleId, IDs, Args]
	  ; Rule_App =.. [RuleId, IDs] 	 
	),
	SubTree = tree(trnd(Nd, Id, Rule_App,_), ChildList),
	growLeftistTree(Tail, RuleApp, ClosureIDs, Child),
	( nonvar(Child), Child =.. [tree|_] -> 
		ChildList = [Child]
	; nonvar(Child) ->	
		ChildList = closer(ClosureIDs)
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

apply_closure_rules(IdList, Branch, Cl_IDs) :-
	Branch = br(BrNodes, _Hist, Sig),
	member(Id, IdList),
	clause( r(RuleId, closure, _, br(Head, Sig) ===> Body), _Constraints ),
	find_head_nodes_with_ids(BrNodes, Head, [Id | Rest]),
	\+memberchk(Id, Rest),
	r(RuleId, closure, _, br(Head, Sig) ===> Body),
	Cl_IDs = [Id | Rest], 
	!.


find_head_nodes_with_ids(_, [], []). 

find_head_nodes_with_ids(BrNodes, Head, [Id | ID_tail]) :- % also usable in reverse
	member(ndId(Node, Id), BrNodes),
	once(choose(Head, Node, Rest)),
	\+cyclic_term(Node), % can be solved by introducing Var(x) for X
	find_head_nodes_with_ids(BrNodes, Rest, ID_tail).
	




		
		
		
		
		
		
		

	
