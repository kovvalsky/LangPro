%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Predicates for processing tableau proof tree
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

stats_from_tree(Tree, Stats) :-
	Init_Stats = s(1, [], _), 
	stats_from_tree_step(Init_Stats, Tree, St),
	St = s(Br_Num, RuleApps, Max_Id),
	list_to_set(RuleApps, RuleApps_Set),
	remove([], RuleApps_Set, RuleApps_Set_1),
	length(RuleApps_Set_1, Len),
	Stats = s(Br_Num, Len, Max_Id). 


stats_from_tree_step(Stats_0, tree(TerminalNode, NoChildren), Stats_1 ) :-
	( var(NoChildren) 
	; NoChildren \= [_|_]), 
	!,
	TerminalNode = trnd(_Node, Node_ID, Note, _Ref),
	%Node = nd(Mods, LLF, Args, TF),
	%Note = h(Rule_Id, RuleInfo, SrcIDs, _TrgIDs),
	Stats_0 = s(Br_Num, RuleApps_0, _),
	Stats_1 = s(Br_Num, [Note | RuleApps_0], Node_ID). % will be empty list of rule apps for root nodes


stats_from_tree_step( Stats_0, tree(MotherNode, SubTrees), Stats_1) :-
	Stats_0 = s(_, RuleApps_0, _),
	MotherNode = trnd(_Node, Node_ID, Note, _Ref),
	%Node = nd(Mods, LLF, Args, TF),
	%Note = h(Rule_Id, RuleInfo, SrcIDs, _TrgIDs),
	maplist(stats_from_tree_step(s(1, [], _)), SubTrees, SubTrees_Stats),
	list_of_tuples_to_list_of_positions(SubTrees_Stats, [Br_N_List, R_App_List, Id_List]),
	sum_list(Br_N_List, Br_Num_1),
	append(R_App_List, R_App),
	append(RuleApps_0, [Note | R_App], RuleApps_1),
	max_list([Node_ID | Id_List], Max_Id),
	Stats_1 = s(Br_Num_1, RuleApps_1, Max_Id).
			


	
