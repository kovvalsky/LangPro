%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% makes Closing_IDs more specific based on the information from History

expand_closing_ids(List_of_Cl_IDs, _Hist, List_of_Cl_IDs) :- !.
%	var(List_of_Cl_IDs).

expand_closing_ids([], _Hist, []) :-
	!.

expand_closing_ids(List_of_Cl_IDs, Hist, Extension) :-
	findall( Source, 
			 ( 	member(Cl_IDs, List_of_Cl_IDs), 
				source_of_ids(Cl_IDs, Hist, Source) 
			 ), 
			 SourceList),
	%append(List_of_Cl_IDs, SourceList, All_Cl_IDs),
	append(List_of_Cl_IDs, SourceList, All_Cl_IDs1), remove_high_sources(All_Cl_IDs1, All_Cl_IDs),
	sort(All_Cl_IDs, Extension).


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













