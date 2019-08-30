%:- ensure_loaded([main]).

:- use_module('../utils/user_preds', [true_member/2]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% makes Closing_IDs more specific based on the information from History

%expand_closure_ids(_NewIDs, ClosureIDs, _Hist, ClosureIDs) :- !.
%	var(List_of_Cl_IDs).

%expand_closure_ids(_NewIDs, [], _Hist, []) :-
%	!.
	
	
test_expand_closure_ids(ExtListOfClIDs) :-
	rule_app_history(Hist),
	include(ground, Hist, Hist1),
	old_closing_ids(OldListOfClIDs),
	new_closing_ids(NewListOfClIDs),
	append(NewListOfClIDs, OldListOfClIDs, ListOfClIDs),
	expand_closure_ids(NewListOfClIDs, ListOfClIDs, Hist1, ExtListOfClIDs).	

% +new_closure_ids, +list_of_all_closure_ids, +history, -extended_list_of_closure_ids
expand_closure_ids(NewListOfClIDs, ListOfClIDs, Hist, ExtListOfClIDs) :-
	findall( DerClIDs, 
			 ( 	member(NewClIDs, NewListOfClIDs), 
				derive_closure_ids(NewClIDs, ListOfClIDs, Hist, DerClIDs) 
			 ), 
			 ListOfDerClIDs),
	append(ListOfClIDs, ListOfDerClIDs, ExtListOfClIDs).
	%list_to_ord_set(UO_ExtListOfClIDs, ExtListOfClIDs).


derive_closure_ids(NewClIDs, ListOfClIDs, Hist, DerClIDs) :-
	derive_closure_ids(NewClIDs, [], [], [], ListOfClIDs, Hist, DerClIDs),
	DerClIDs \== NewClIDs. % prevents trivially derived rules 
	
	
derive_closure_ids(NewClIDs, AllIDs, _OldArgs, _RApps, ListOfClIDs, _Hist, NewClIDs) :-
	nonvar(AllIDs),
	AllIDs == [],
	once( ( member(ClIDs, ListOfClIDs),
			subset(ClIDs, NewClIDs) % arguments need to be sets
	) ).	

% non-branching
derive_closure_ids(NewClIDs, AllIDs, OldArgs, RApps, ListOfClIDs, Hist, DerClIDs) :-
	member(ID, NewClIDs),
	RuleApp = h(_RuleId, _Olds, SrcIDs, News, [TrgIDs]), % [TrgIDs] means non-branching
	member(RuleApp, Hist),
	%subsumes_term(RuleApp, RApp), % picks only ground ruleApps from history
	%RuleApp = RApp, 
	\+memberchk(RuleApp, RApps), % prevents redundant steps
	member(ID, TrgIDs),
	subtract(NewClIDs, TrgIDs, RestNewClIDs),    
	subset(News, OldArgs),
	append(SrcIDs, RestNewClIDs, NewClIDs1),
	( AllIDs == [],
	  DerClIDs = NewClIDs1 
	; append([AllIDs, NewClIDs1, TrgIDs], AllIDs1),
	  list_to_ord_set(AllIDs1, AllIDs2),   
	  derive_closure_ids(NewClIDs1, AllIDs2, OldArgs, [RuleApp|RApps], ListOfClIDs, Hist, DerClIDs)  
	).
	
% branching
derive_closure_ids(NewClIDs, AllIDs, OldArgs, RApps, ListOfClIDs, Hist, DerClIDs) :-
	member(ID, NewClIDs),
	RuleApp = h(_RuleId, _Olds, SrcIDs, News, [[H|R]|RBr]), % [[H|R]|RBr]) means branching
	member(RuleApp, Hist),
	Branches = [[H|R]|RBr], 
	
	%subsumes_term(RuleApp, RApp), % picks only ground ruleApps from history
	%RuleApp = RApp, 
	\+memberchk(RuleApp, RApps), % prevents redundant steps
	member(ID, TrgIDs),
	subtract(NewClIDs, TrgIDs, RestNewClIDs),    
	subset(News, OldArgs),
	append(SrcIDs, RestNewClIDs, NewClIDs1),
	( AllIDs == [],
	  DerClIDs = NewClIDs1 
	; append([AllIDs, NewClIDs1, TrgIDs], AllIDs1),
	  list_to_ord_set(AllIDs1, AllIDs2),   
	  derive_closure_ids(NewClIDs1, AllIDs2, OldArgs, [RuleApp|RApps], ListOfClIDs, Hist, DerClIDs)  
	).	




% get the new or the same closure IDs based on the history	
new_closure_ids(IDs, Hist, NewIDs) :-	
	select(ID, IDs, RestIDs),
	source_of_id(ID, Hist, SrcID),
	new_closure_ids([SrcID|RestIDs], Hist, NewIDs). 
	
new_closure_ids(IDs, _, IDs).	

% get source node IDs for a node ID based on the history	
source_of_id(ID, Hist, AntIDs) :-
	member(RApp, Hist),
	RApp =.. [_, AntIDs, _, [ConIDs]], % non-branching rule application
	memberchk(ID, ConIDs).
	
	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% non-eflexive relation
source_of_ids(Cl_IDs, Hist, Source) :-
	dir_src_of_ids(Cl_IDs, Hist, Source_1),
	source_of_ids_w_path(Source_1, Hist, [Source_1], Source).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% gives a direct saurce for an id or two ids 
dir_src_of_ids([ID], Hist, Src) :-
	!, 
	dir_src_of_id(ID, Hist, Src).

dir_src_of_ids([ID1, ID2], Hist, Src) :- %both elements needs dir source, could be improved 
	!, 
	dir_src_of_id(ID1, Hist, Src1),
	dir_src_of_id(ID2, Hist, Src2),
	append(Src1, Src2, Source),
	sort(Source, Src).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% gives all direct saources for an id or two ids 
dir_sources_of_ids([ID], Hist, Sources) :-
	!, 
	dir_sources_of_id(ID, Hist, Sources).

dir_sources_of_ids([ID1, ID2], Hist, Sources) :- 
	!, 
	dir_sources_of_id(ID1, Hist, Sources1),
	dir_sources_of_id(ID2, Hist, Sources2),
	sources_from_two_sources(Sources1, Sources2, Sources).

%dir_sources_of_ids(_, _Hist, []).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% gives all direct sources for one id
dir_sources_of_id(ID, Hist, Sources) :-
	findall(Src, dir_src_of_id(ID, Hist, Src), Sources).

% gives one direct source for one id
dir_src_of_id(ID, Hist, Src_IDs) :-   %!!! fails when there is no direct source fix it!
	member( h(RuleId, _AppInfo, Src_IDs, Target_IDs), Hist ),
	true_member(ID, Target_IDs), % guarantees that target ids are really existing in History and avoids matcheing with free vars
	clause( r(RuleId, _:_, _, _Lex, br(_,_) ===> br(_,_)), _Constraints ).  %!!! what about new? & equivalence?

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% reflexive version of source_of_ids/3
source_of_ids_w_path(Target, Hist, Path, Source) :-
	dir_src_of_ids(Target, Hist, Source_1),
	\+member(Source_1, Path),
	source_of_ids_w_path(Source_1, Hist, [Source_1|Path], Source). 

source_of_ids_w_path(Target, _Hist, _Path, Target).

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% creates all possble sources from elements of two source lists
sources_from_two_sources(Sources1, Sources2, Sources) :-
	findall(SrtSrc,
			(member(S1, Sources1),
			 member(S2, Sources2),
			 append(S1, S2, S),
			 sort(S, SrtSrc)),
			All_Src),
	sort(All_Src, Sources).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% filter sources - if min_List1 > max_List2 throw List1
remove_high_sources(Sources, Filtered) :-
	findall(Src,
		( member(Src, Sources),
		  \+src_is_not_maximum(Src, Sources)
		),
	Filtered).


% There is an element in source that is greater than Src
src_is_not_maximum(Src, Sources) :-
	member(X, Sources),
	is_greater_src(X, Src),
	!.
	


is_greater_src(Src1, Src2) :-
	max_list(Src1, N1),	
	min_list(Src2, N2),
	N1 < N2.





rule_app_history(
[ h(pull_arg,[],[25],[],[[27]]),
  h(tr_no,[(c2,e)],[5],[],[[23],[24,25]]),
  h(tr_no,[(c1,e)],[5],[],[[20],[21,22]]),
  h(by_mod,[],[19],[],[[18]]),
  h(mod_vac,[],[18],[],[[19]]),
  h(push_mod,[],[18],[],[[19]]),
  h(vp_pass2,[],[18],[],[[14]]),
  h(by_mod,[],[17],[],[[18]]),
  h(aux_verb,[],[16],[],[[17]]),
  h(aux_verb,[],[15],[],[[16]]),
  h(mod_vac,[],[11],[],[[15]]),
  h(push_mod,[],[11],[],[[15]]),
  h(aux_verb,[],[13],[],[[14]]),
  h(aux_verb,[],[12],[],[[13]]),
  h(vp_pass2,[],[11],[],[[12]]),
  h(push_arg,[],[10],[],[[11]]),
  h(pull_arg,[],[8],[],[[10]]),
  h(fl_a,[(c2,e)],[7],[],[[_],[9,8]]),
  h(the_c,[(c2,e)],[7,9],[],[[8]]),
  h(the,[],[7],[(c2,e)],[[8,9]]),
  h(pull_arg,[],[6],[],[[7]]),
  h(fl_a,[(c1,e)],[1],[],[[_],[4,6]]),
  h(the,[],[1],[(c1,e)],[[6,4|_]]),
  h(the_c,[(c1,e)],[1,4],[],[[6]]),
  h(pull_arg,[],[3],[],[[5]]),
  h(fl_a,[(c1,e)],[2],[],[[_],[4,3]]),
  h(the_c,[(c1,e)],[2,4],[],[[3]]),
  h(the,[],[2],[(c1,e)],[[3,4]])
]).

old_closing_ids([[23,9]]).

new_closing_ids([[27,10]]).






