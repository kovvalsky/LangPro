%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: Tableau Prover for Natural Logic
%     Version: 12.06.12
%      Author: lasha.abzianidze{at}gmail.com 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%    Defining operators and loading files 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:-op(610, xfx, ===>).

:- ensure_loaded([lambda,
				  counters,	
				  knowledge,
				  lexicon,	
				  rules,
				  gui_tree,		
				  latex, 
				  test_suite,
				  user_preds
				 ]).


				 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%           Auxiliary Predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% mon(Term, MonotonicityValue)
% takes Term and generates its MonotonicityValue
% MonotonicityValue is one of the atoms: up, dw, non
mon(Term, Mon) :-
	mon(Term, [], [Mon | _]).	
	
mon(Const, _, Mon) :-
	atom(Const),
	!,
	Const :: _ :: Mon.
	
mon(abst, Vars, [Mon | TermMon]) :-
	nonvar(abst),
	abst = abst(X, Term),
	!,
	mon(Term, [X :: Mon | Vars], TermMon).	
	
mon(Appl, Vars, Mon) :-
	nonvar(Appl),
	Appl = Fun @ Arg,
	!,
	mon(Fun, Vars, [ArgMon | Mon]),
	(var(Arg), member(X :: ArgMon, Vars), X == Arg, !; !).	
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% neg(Value1, Value2)
% true if negation of Value1 is Value2
neg(true, false).
neg(false, true).
	
	
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
% genFreshArgs(Type, Args, Sig, NewSig)
% creates a list of constant arguments feeding Type
% and adds these constant::its_type to Signature  
genFreshArgs(t, [], Sig, Sig, const_id(Eid, Eid, Cid, Cid)).
	
genFreshArgs(Type, Args, Sig, NewSig, const_id(Eid1, Eid2, Cid1, Cid2)) :- 
	nonvar(Type),
	Type = A ~> B,
	%(A == e -> new_entity_index(I), atomic_list_concat([c, I], X);
	%		   new_const_index(I), atomic_list_concat(['P', I], X)),
	(A == e -> 
		I is Eid1 + 1, 
		atomic_list_concat([c, I], X),
		ConstId = const_id(I, Eid2, Cid1, Cid2);
		I is Cid1 + 1,
		atomic_list_concat(['P', I], X),
		ConstId = const_id(Eid1, Eid2, I, Cid2)),  
	Args = [X | RestArgs],
	TempSig = [ X::A | Sig],
	genFreshArgs(B, RestArgs, TempSig, NewSig, ConstId).


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
% genOldArgs(Type, Args, Lexicon)
% picks a list of old arguments from lexicon, which feeds Type
genOldArgs(t, [], _).

genOldArgs(Type, Args, Lexicon) :-
	nonvar(Type),
	Type = A ~> B,
	member(C::A, Lexicon),
	Args = [C | RestArgs],
	genOldArgs(B, RestArgs, Lexicon).
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% assignIds(ListOfNodes, ID_ListOfNodes) 	
% ID_ListOfNodes is a ListOfNodes with IDs
assignIds([Nd | NdRest], [Nd | NdIdRest], NodeId) :-
	Nd = ndId(_,_),
	assignIds(NdRest, NdIdRest, NodeId).

assignIds([Nd | NdRest], [NdId | NdIdRest], NodeId) :-
	Nd = nd(_,_,_),
	NodeId = node_id(Nid1, Nid),
	Id is Nid1 + 1,
	NdId = ndId(Nd, Id),
	assignIds(NdRest, NdIdRest, node_id(Id, Nid)).
	
assignIds([], [], node_id(Nid, Nid)).	



subtract_nodes([], X, X, []).

subtract_nodes(NodeList, [], [], NodeList).

subtract_nodes(NodeList, CutBrNodes, NewFilteredCutBrNodes, NodeList_pId) :-
	NodeList = [Formula | Rest],
	( memberchk(ndId(Formula, Id), CutBrNodes), 
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
% feed_nodes_with_args(+Nodes, +Args) 
% Specifies a list of nodes by matching their
% arguments with Args
% deterministic;
feed_nodes_with_args([nd(_, Args, _) | Rest], Args) :-
	feed_nodes_with_args(Rest, Args),
	!.

feed_nodes_with_args([], _).		








%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% Takes list of TTterms with True and a list of
% TTterms with sign False, generates tableau tree
% and branch list, and checks the input on closure
% without GUI  
reason(T_TTlist, F_TTlist) :-
	generateTableau(T_TTlist, F_TTlist, BrList, _),
	!,
	closed(BrList).

/*
sub_reason(T_LLF, F_LLF, Sig) :- %not for list yet
	%maplist(Sig '|-', T_LLFlist, T_Types),
	%maplist(Sig '|-', T_LLFlist, T_Types), 
	Sig '|-' T_LLF :: Type, % restrict Sig later
	Sig '|-' F_LLF :: Type,
	genFreshArgs(Type, Args, Sig, NewSig, const_id(0, Ent_Id, 0, Con_Id)),
	Node1 = nd(T_LLF, Args, true),
	Node2 = nd(F_LLF, Args, false), 
	Branch = [ndId(Node2, 2), ndId(Node1, 1)],
	BrList = [br(Branch, [], NewSig)], 
	Root = trnd(Node1, 1, [], _),
	Left = trnd(Node2, 2, [], _),
	Tree = tree(Root, Left, _),
	Count = [const_id(Ent_Id, _, Con_Id, _), node_id(2, _)],
	once(expand(BrList, NewBrList, Tree, Count)),
	closed(NewBrList).
*/		

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% Takes list of TTterms with True and a list of
% TTterms with sign False, generates tableau tree
% and branch list, and checks the input on closure
% with GUI	
greason(T_TTlist, F_TTlist) :-
	generateTableau(T_TTlist, F_TTlist, BrList, Tree),
	!,
	display('Tableau is generated'), nl,
	displayTree(Tree, 12),
	!,
	gclosed(BrList, Tree, _). % what about the last argument?

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% generateTableau(Prem, Concl, BrList, Tree)
% generates tableau proof in styles of
% a list of branches and a tree
generateTableau(T_TTlist, F_TTlist, BrList, Tree) :-
	ttTerms_to_nodes_sig(T_TTlist, F_TTlist, Nodes, Signature, (Ent_Id, Con_Id)),
	nodes_to_SigBranch_tree_id(Nodes, Signature, Br, Tree, Node_Id),
	Count = [const_id(Ent_Id, _, Con_Id, _), node_id(Node_Id, _)],
	catch(call_with_time_limit(2, 
							once(expand([Br], BrList, Tree, Count)) ),
		_,
		(writeln('time_limit_exceeded'), fail)	
	).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ttTerms_to_nodes_sig(T_TTlist, F_TTlist, Nodes, NewSig)
% converts list of true and false TTterms into list of nodes
% and creates a signature for the branch
ttTerms_to_nodes_sig(T_TTlist, F_TTlist, Nodes, Signature, Const_Ids) :-
	%retractall(event_index(_)),
	%retractall(lex),
	%reset_id_count,
	%reset_const_index,
	maplist(ttTerm_to_node(true, Type), T_TTlist, T_Nodes, T_Knows, T_Sigs),
	maplist(ttTerm_to_node(false, Type), F_TTlist, F_Nodes, F_Knows, F_Sigs),
	append(T_Sigs, F_Sigs, TF_Sigs),
	append(TF_Sigs, List_Sig),
	list_to_ord_set(List_Sig, Sig),
	genFreshArgs(Type, Args, Sig, NewSig, const_id(0, Ent_Id, 0, Con_Id)),
	Const_Ids = (Ent_Id, Con_Id),
	append(T_Nodes, F_Nodes, Nodes),
	feed_nodes_with_args(Nodes, Args),
	append(T_Knows, F_Knows, TF_Knows),
	append(TF_Knows, List_Know),
	append(List_Know, NewSig, List_Signature),
	list_to_ord_set(List_Signature, Signature). 
	%list_to_ord_set(List_Know, Know),
	%assert_list(Know, noclean).


ttTerm_to_node(TF, Type, TTExp, Node, Know, Lex) :- % to be changed
	ttExp_to_ttTerm(TTExp, TTterm), % allows to abreviate ttterms in test suite
	ttTerm_to_norm_term(TTterm, BENorm, Know, Lex, _), % to be changed
	TTterm =.. [_, _, Type],
	Node = nd(BENorm, _, TF).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% nodes_to_branch_tree(Nodes, Sig, Br, Tree)
% creates a branch with Signature and a Tree 
nodes_to_SigBranch_tree_id(Nodes, Sig, BrSig, Tree, Last_Id) :-
	nodes_to_branch_tree_id(Nodes, RevBranch, Tree, node_id(0, Last_Id)),
	reverse(RevBranch, Branch),
	BrSig = br(Branch, [], Sig),
	!.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% nodes_to_branch_tree(Nodes, Branch, Tree)
% creates List of (node ID) pairs for Branch
% and a Tableau tree with nodes as its leaves 
nodes_to_branch_tree_id([Node | RestNodes], Branch, Tree, node_id(Old_Id, Last_Id)) :-
	!,
	Id is Old_Id + 1,
	Root = trnd(Node, Id, [], _),
	Tree = tree(Root, Left, _),
	Branch = [ndId(Node, Id) | RestBranch],
	nodes_to_branch_tree_id(RestNodes, RestBranch, Left, node_id(Id, Last_Id)).

% if no nodes, a branch has empty list of nodes and tree is unbound
nodes_to_branch_tree_id(EmptyList, EmptyList, _, node_id(Old_Id, Old_Id)).


	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% expand(BranchList, NewBranchList, Tree)
% expands BranchList to NewBranchList (by multi steps) and
% constructively builds the structure Tree via matching 

expand(BranchList, NewBranchList, Tree, Count) :-
	%length(BranchList, N), 
	%(0 is N mod 100 -> display(N), nl; true), 
	Count = [const_id(Eid1, Eid, Cid1, Cid), node_id(Nid1, Nid)],
	Count1 = [const_id(Eid1, Eid2, Cid1, Cid2), node_id(Nid1, Nid2)],
	dirExpand(BranchList, TempBranchList, Tree, Count1),
	Count2 = [const_id(Eid2, Eid, Cid2, Cid), node_id(Nid2, Nid)],
	%length(TempBranchList, L), 
	%(L < 3000 -> expand(TempBranchList, NewBranchList, Tree)). 
	expand(TempBranchList, NewBranchList, Tree, Count2).
	
expand(BranchList, BranchList, _, [const_id(E,E,C,C), node_id(N,N)]).	

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% dirExpand(BranchList, NewBranchList, Tree)
% expands BranchList to NewBranchList by single step
dirExpand([ br([],_,_) | Tail], Tail, _, [const_id(E,E,C,C), node_id(N,N)]). %:-
	%writeln('Closed Branch').

dirExpand([Branch | RestBranches], NewBranchList, Tree, Count) :-
	Branch = br(BrNodes, _, _),
	Count = [ConstId, NodeId],
	/*( r(RuleId, RuleType, Head ===> Body, Constraints, Constants), is_list(Body);
	  r(RuleId, RuleType, Head ===> Body, Constraints, Constants) ),
	findHeadNodes(BrNodes, Head, IDs),
	call(Constraints),
	splitOldFresh(Constants, ListOld, ListFresh, ListConst),
	genAllOldArgs(ListOld, Lexicon, AllOldConst),
	updateHistory(RuleType, IDs, AllOldConst, RuleId, History, NewHistory),
	!,
	genAllFreshArgs(ListFresh, Lexicon, TempLexicon),    %!!! temporarily only one lexicon
	append(ListConst, TempLexicon, NewLexicon),*/
	findRule(Branch, RuleType, IDs, Body, NewHistory, ConstId),
	(RuleType = equi -> 
		pruneBranch(BrNodes, IDs, CutBrNodes);
		CutBrNodes = BrNodes),
	CutBranch = br(CutBrNodes, NewHistory, _),
	BrNodes = [ndId(_, BrId) | _],
	findSubTree(Tree, BrId, SubTree),
	SubTree = tree(_, LeftTree, RightTree),
	var(LeftTree), 
	var(RightTree),
	!,
	growBranches(Body, CutBranch, NewBranches, SubTree, IDs, NodeId),
	append(NewBranches, RestBranches, NewBranchList).

% if the first branch is not closed that terminate	
%dirExpand([Branch | Tail], [Branch | NewTail], Tree) :-
%	dirExpand(Tail, NewTail, Tree).	

findRule(Branch, RuleType, IDs, Body, NewHist, Cids) :-
	Branch = br(BrNodes, Hist, Sig),
	%Cids = const_id(Eid1, Eid, Cid1, Cid),
	BrHead = br(Head, Sig),	
	( r(RuleId, RuleType, (AppInfo, Cids), BrHead ===> br(N, S), Constraints), 
		Body = br(N, S);
	  r(RuleId, RuleType, (AppInfo, Cids), BrHead ===> v(B1, B2), Constraints), 
		Body = v(B1, B2)),
	findHeadNodes(BrNodes, Head, IDs),
	(RuleType = gamma -> true; \+member(h(RuleId, IDs), Hist)),
	%assert(branch_signature(Sig)),
	Constraints,
	%retract(branch_signature(_)),
	%splitOldFresh(Constants, ListOld, ListFresh, ListConst),
	%genAllOldArgs(ListOld, Sig, AllOldConst),
	updateHistory(RuleType, IDs, AppInfo, RuleId, Hist, NewHist),
	ignore(Cids = const_id(Eid, Eid, Cid, Cid)),
	!.
	%genAllFreshArgs(ListFresh, Sig, TempLexicon, ConstId),    %!!! temporarily only one lexicon
	%union(ListConst, TempLexicon, NewLexicon).



%call_constrints(Constraints) :-
%	Constraints =.. [_, Head, Rest],
	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% findHeadNodes(BrNodes, RuleHead, IDs),
% finds IDs of first(!) nodes of BrNodes matching to 
% the nodes of RuleHead - the head of the rule	
findHeadNodes(BrNodes, [Head | Tail], IDs) :-
	member(ndId(Head, Id), BrNodes),
	findHeadNodes(BrNodes, Tail, ID_tail),
	IDs = [Id | ID_tail].
	
findHeadNodes(_, [], []). 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% updateHistory(RuleType, IDs, AllOldConst, Id, History, NewHistory)
% If the record (applying Id rule to IDs nodes)
% is not in old History, than updates to NewHistory
% according to the Type of the rule % type is not used yet
updateHistory(RuleType, IDs, AppInfo, RuleId, History, NewHistory) :-
	(RuleType = gamma -> 
		Info = (IDs, AppInfo);
		Info = IDs),
	(member(h(RuleId, ID_list), History),
	Info = ID_list ->     				%!!! permutation(IDs, ID_list)
		false;
		NewHistory = [h(RuleId, Info) | History] ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% pruneBranch(BrNodes, IDs, CutBrNodes)	
% CutBrNodes are list of nodes after removing
% nodes with IDs from the list of nodes BrNodes
pruneBranch(BrNodes, [ID_h | ID_t], CutBrNodes) :-
	remove(ndId(_, ID_h), BrNodes, NewBrNodes),
	pruneBranch(NewBrNodes, ID_t, CutBrNodes).
		
pruneBranch(BrNodes, [], BrNodes).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% findSubTree(Tree, Id, SubTree)
% finds SubTree of Tree such that 
% Id is assigned to the root node of SubTree
findSubTree(Tree, Id, SubTree) :-
	nonvar(Tree),
	Tree = tree(trnd(_,Id1,_,_), LeftTree, RightTree),
	( ( Id1 == Id, SubTree = Tree ); 
	  findSubTree(LeftTree, Id, SubTree); 
	  findSubTree(RightTree, Id, SubTree)
	).	
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% growBranches(NewNodes, CutBranch, NewBranches, SubTree, SourceIDs)
% NewBranches are produced from CutBranch by adding NewNodes,
% SubTree is updated and new nodes are notated by SourceIDs    
growBranches(Brs, CutBranch, NewBranches, SubTree, SourceIDs, NodeId) :-
	Brs = v(A, B),
	!,
	SubTree = tree(_, LeftTree, RightTree),
	NodeId = node_id(Nid1, Nid),
	NodeId1 = node_id(Nid1, Nid2),
	growBranch(A, CutBranch, Branch_A, LeftTree, SourceIDs, NodeId1),
	NodeId2 = node_id(Nid2, Nid),
	growBranch(B, CutBranch, Branch_B, RightTree, SourceIDs, NodeId2),
	NewBranches = [Branch_A, Branch_B] .


growBranches(Br, CutBranch, NewBranches, SubTree, SourceIDs, NodeId) :-
	Br = br(NewNodes, _), 	
	is_list(NewNodes),
	!,
	SubTree = tree(_, LeftTree, _),
	growBranch(Br, CutBranch, NewBranch, LeftTree, SourceIDs, NodeId),
	NewBranches = [NewBranch] .	

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% growBranch(NodeList, CutBranch, NewBranch, SubTree, SourceIDs)
% NewBranch is produced from CutBranch by adding NodeList,
% SubTree is updated and new nodes are notated by SourceIDs  	
growBranch(Br, CutBranch, NewBranch, SubTree, SourceIDs, NodeId) :-
	Br = br(NodeList, Sig), 
	CutBranch = br(CutBrNodes, History, _),
	is_list(NodeList),
	% deletes new redundant nodes
	once(subtract_nodes(NodeList, CutBrNodes, FilteredCutBrNodes, NodeList_pId)),
	assignIds(NodeList_pId, NodeList_id, NodeId),
	reverse(NodeList_id, RevNodeList_id),
	append(RevNodeList_id, FilteredCutBrNodes, NewTableauNodes),
	(closedBranch(NewTableauNodes, ClosureIDs) -> TableaNodes = []; 
									TableaNodes = NewTableauNodes), 
	NewBranch = br(TableaNodes, History, Sig),
	growLeftistTree(NodeList_id, SourceIDs, ClosureIDs, SubTree).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% growLeftistTree(NodeList, SourceIDs, ClosureIDs, SubTree)
% grows SubTree in leftist fashion by NodeList, annotates nodes by SourceIDs
% and annotates the branch by ClosureIDs if it is closed 
growLeftistTree( [ndId(Nd, Id) | Tail], SourceIDs, ClosureIDs, SubTree) :-
	SubTree = tree(trnd(Nd, Id, SourceIDs,_), LeftTree, _),
	growLeftistTree(Tail, SourceIDs, ClosureIDs, LeftTree).
	
growLeftistTree([], _, ClosureIDs, ClosureIDs).
	

	
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%	  	Checking Tableau on Closure    
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% closed(ListOfBranches)
% succeeds if all branches of ListOfBranches are closed	
closed([ Branch | Tail ]) :-
	Branch = br(BrNodes, _, _),
	closedBranch(BrNodes, _),
	closed(Tail).
	
closed([]).	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% closedBranch(NodesOfBranch, ClosureIDs)
% succeeds if nodes of a branch are inconsistent,
% e.i. NodesOfBranch is closed, where ClosureIDs saves
% the IDs of nodes causing the closure
closedBranch(BrNodes, ClosureIDs) :-
	member( ndId(nd(LLF, Args, false),Id), BrNodes),
	%betaEtaNorm(LLF, Norm)
	atom(LLF),
	list_of_atoms(Args),
	instance(Args, LLF), 
	!,
	ClosureIDs = [Id].
 	
closedBranch(BrNodes, ClosureIDs) :-
	member( ndId(nd(LLF1, Args1, true),Id1), BrNodes),
	member( ndId(nd(LLF2, Args2, false),Id2), BrNodes),
	Id1 \== Id2,
	%Args1 == Args2,
	match_list_ttTerms(Args1, Args2),
	betaEtaNorm(LLF1, Norm1),  %!!! probably can be omitted
	betaEtaNorm(LLF2, Norm2),  %!!! probably can be omitted
	(%Norm1 == Norm2; 
	 match_ttTerms(Norm1, Norm2);
	 isa(Norm1, Norm2); 
	 alpha(Norm1, Norm2)),
	!,
	ClosureIDs = [Id1, Id2].
	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% gclosed(ListOfBranches, Tree, Closed)
% checks if all branches of ListOfBranches are closed,
% if all of them are closed than Closed=true, otherwise false,
% marks a pair of nodes which result a closed branch
gclosed([ Branch | Tail ], Tree, Closed) :-
	gclosedBranch(Branch, Tree) -> 
		gclosed(Tail, Tree, Closed); 
		(Closed = false,
		 gclosed(Tail, Tree, Closed)
		).
	
gclosed([],_,Closed) :- 
	Closed = true.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% gclosedBranch(Branch, Tree)
% if Branch is closed marks the pair of nodes of Tree
% which results Branch to close
gclosedBranch(Branch, Tree) :-
	Branch = br(BrNodes, _, _),
	%reverse(BrNodes, RevBrNodes), 
	member( ndId(nd(LLF1, Args1, true),Id1), BrNodes),
	member( ndId(nd(LLF2, Args2, false),Id2), BrNodes),
	%Args1 == Args2,
	match_list_ttTerms(Args1, Args2),
	betaEtaNorm(LLF1, Norm1),   %!!! probably can be omitted
	betaEtaNorm(LLF2, Norm2),   %!!! probably can be omitted
	(%Norm1 == Norm2; 
	 match_ttTerms(Norm1, Norm2);
	 isa(Norm1, Norm2); 
	 alpha(Norm1, Norm2)),
	!,
	findSubTree(Tree, Id1, tree(trnd(_,_,_,Ref1),_,_)),
	findSubTree(Tree, Id2, tree(trnd(_,_,_,Ref2),_,_)),
	get(Ref1, font, font(Family, _, Points)),
	send(Ref1, font, font(Family, bold, Points)),
	send(Ref2, font, font(Family, bold, Points)).
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% boldClosureNodes(ClosureIDs, Tree)
% Finds closure nodes by their ids in Tree and makes them bold
boldClosureNodes([Id | RestIds], Tree) :-
	findSubTree(Tree, Id, tree(trnd(_,Id,_,Ref),_,_)),
	get(Ref, font, font(Family, _, Points)),
	send(Ref, font, font(Family, bold, Points)),
	!,
	boldClosureNodes(RestIds, Tree).

boldClosureNodes([], _).	










		
		
		
		
		
		
		

	
