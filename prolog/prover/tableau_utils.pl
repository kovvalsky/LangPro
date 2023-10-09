%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%        Predicates for natural tableau
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module('tableau_utils',
	[
		assignIds/4,
		subtract_nodes/4,
		single_branch_model_rules/2,
		select_relevant_rules/3,
		ttTerms_to_nodes_sig/6,
		genOldArgs/3,
		genFreshArgs/5,
		get_closure_rules/2
	]).

:- use_module('../lambda/type_hierarchy', [sub_type/2]).
:- use_module('../lambda/lambda_tt', [op(605, xfy, ~>)]).
:- use_module('../rules/rules', [op(610, xfx, ===>)]).
:- use_module('../llf/ttterm_preds', [apply_ttFun_to_ttArgs/3]).

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
	  delete(CutBrNodes, ndId(Formula, Id), FilteredCutBrNodes) ->   %!!! [A]:B:T doesnt take id from []:B:T
		NodeList_pId = [ndId(Formula, Id) | RestNodeList_pid],
		  subtract_nodes(Rest, FilteredCutBrNodes, NewFilteredCutBrNodes, RestNodeList_pid);
		NodeList_pId = [Formula | RestNodeList_pId],
		  subtract_nodes(Rest, CutBrNodes, NewFilteredCutBrNodes, RestNodeList_pId)).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Filter the inventory of rules based on lexicon
select_relevant_rules(_Lexicon, [], []) :- !.

select_relevant_rules(Lexicon, [R | Rest], Filtered) :-
	rule_is_relevant(Lexicon, R)
	->	Filtered = [R | FilteredRest],
		select_relevant_rules(Lexicon, Rest, FilteredRest)
	; 	select_relevant_rules(Lexicon, Rest, Filtered).




rule_is_relevant(_, R) :-
	clause( r(R,_,_,Lex,_,_), _),
	var(Lex),
	!.

rule_is_relevant(Lexicon, R) :-
	clause( r(R,_,_,DNF,_,_), _),
	member(Conditions, DNF),
	maplist(rule_condition_is_sat(Lexicon), Conditions), !.

rule_condition_is_sat(Lexicon, A) :-
	( A = pos(P) ->
		L = (_,P)
	; atom(A) ->
		L = (A,_)
	; A = ty(pp) ->
	  ( L = (_,'IN'); L = (_,'RP'); L = (_,'TO'); L = (_,'RB') )
	; report('Unknown Rule lex item!!!'), fail ),
	memberchk(L, Lexicon),
	!.


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
		;	maplist({Args}/[T_TT1,T_TT2]>>apply_ttFun_to_ttArgs(T_TT1,Args,T_TT2),
				T_TTlist, T_List),
			maplist({Args}/[F_TT1,F_TT2]>>apply_ttFun_to_ttArgs(F_TT1,Args,F_TT2),
				F_TTlist, F_List),
			ArgList = [] ),
	maplist(ttTerm_to_node(true, ArgList), T_List, T_Nodes),
	maplist(ttTerm_to_node(false, ArgList), F_List, F_Nodes),
	append(T_Nodes, F_Nodes, Nodes).
	%list_to_ord_set(Sig, Signature), not necessary
%
% ttTerms_to_nodes_sig(T_TTlist, F_TTlist, Type, Nodes, Sig, (Ent_Id, Con_Id)) :-
% 	genFreshArgs(Type, Args, [], Sig, const_id(0, Ent_Id, 0, Con_Id)), %!!! John from term, must be added to Signature and mustnt wait for Arg push application
% 	maplist(apply_ttFun_to_ttArgs(Args), T_TTlist, T_List),
% 	maplist(apply_ttFun_to_ttArgs(Args), F_TTlist, F_List),
% 	maplist(ttTerm_to_node(true, []), T_List, T_Nodes),
% 	maplist(ttTerm_to_node(false, []), F_List, F_Nodes),
% 	append(T_Nodes, F_Nodes, Nodes).

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
% feed_nodes_with_args([nd(_, _, Args, _) | Rest], Args) :-
% 	feed_nodes_with_args(Rest, Args), !.
%
% feed_nodes_with_args([], _).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Extract relevant closure rules
get_closure_rules(Lexicon, ClRules) :-
	findall(RuleN, clause(r(RuleN,closure,_,_,_,_),_), ListClRules),
	list_to_set(ListClRules, SetClRules), % list_to_ord_set changes ordering, while this preserves rule priority
	select_relevant_rules(Lexicon, SetClRules, ClRules).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% keep the rules that are relevant for creating a single branch model
single_branch_model_rules(Rules1, Rules2) :-
	findall(R, (
		member(R, Rules1),
		clause(r(R, Type, _, _, _, _Head ===> Body), _Constraints),
		Type \= 'closure',
		\+is_list(Body)
	), Rules2).
