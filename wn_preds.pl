:- ensure_loaded(['WNProlog/wn_hyp',
				  %'wn_h_',	
 				  'WNProlog/wn_sim',
				  'WNProlog/wn_ant',	
				  'WNProlog/wn_der',
				  'WNProlog/wn_s'
				 ]).
				
% checks if two words can have synonymous senses
word_synonyms(W1, W2) :-
	nonvar(W1), 
	nonvar(W2),
	%s(SS, _, W1, _, _, _), 	s(SS, _, W2, _, _, _), 
	isa(W1, W2), isa(W2, W1),  % more efficient
	!.
 

% given word(s) finds or checks hypernym relation between their SynSets
word_hyp(W1, W2, Num) :-
	(nonvar(W1), nonvar(W2)) ->
		s(SS1, _, W1, _, _, _),
		atom_chars(SS1, [Num |_]),
		s(SS2, _, W2, _, _, _),
		hypernym(SS1, SS2);
	nonvar(W1) ->
		s(SS1, _, W1, _, _, _),
		atom_chars(SS1, [Num |_]),
		hypernym(SS1, SS2),	
		s(SS2, _, W2, _, _, _);
	nonvar(W2) ->
		s(SS2, _, W2, _, _, _),
		atom_chars(SS2, [Num |_]),
		hypernym(SS1, SS2),	
		s(SS1, _, W1, _, _, _);
	fail.
/*
word_h_(W1, W2, Num) :-
	(nonvar(W1), nonvar(W2)) ->
		s(SS1, _, W1, _, _, _),
		atom_chars(SS1, [Num |_]),
		s(SS2, _, W2, _, _, _),
		h_(SS1, SS2, _);
	nonvar(W1) ->
		s(SS1, _, W1, _, _, _),
		atom_chars(SS1, [Num |_]),
		h_(SS1, SS2, _),	
		s(SS2, _, W2, _, _, _);
	nonvar(W2) ->
		s(SS2, _, W2, _, _, _),
		atom_chars(SS2, [Num |_]),
		h_(SS1, SS2, _),	
		s(SS1, _, W1, _, _, _);
	fail.	
*/	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% Finds Hypernym SynSet as a list for a word	
word_hyp_ss(W1, W_List, Num) :-
	nonvar(W1),
	s(SS1,_,W1,_,_,_),
	atom_chars(SS1, [Num |_]),
	hypernym(SS1, SS2),	
	findall(W, s(SS2,_,W,_,_,_), W_List).
	
word_dir_hyper_ss(W1, W_List, Num) :-
	nonvar(W1),
	s(SS1,_,W1,_,_,_),
	atom_chars(SS1, [Num |_]),
	hyp(SS1, SS2),	
	findall(W, s(SS2,_,W,_,_,_), W_List).
	
word_dir_hypon_ss(W1, W_List, Num) :-
	nonvar(W1),
	s(SS1,_,W1,_,_,_),
	atom_chars(SS1, [Num |_]),
	hyp(SS2, SS1),	
	findall(W, s(SS2,_,W,_,_,_), W_List).

% prints Synsets of all senses of the word 
word_ss(W1, W_List, Num) :-
	nonvar(W1),
	s(SS1,_,W1,_,_,_),
	atom_chars(SS1, [Num |_]),
	findall(W, s(SS1,_,W,_,_,_), W_List).	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% Find commom hyponyms of SynSets
common_ss(SSList, Banned, Commons) :-
	(maplist(hypernym_ban(Com, Banned), SSList), !,
	 Banned_New = [Com | Banned],
	 writeln(Com),
	 common_ss(SSList, Banned_New, Commons)
	), !;
	Commons = Banned.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% Lists kinds of SynSets
kind_ss(Kind, SynSet, Num) :-
	Pred =.. [Kind, X, Num], 
	findall(X, Pred, SSList),
	list_to_set(SSList, SS_set),
	length(SS_set, N), writeln(N),
	member(SS, SS_set),
	findall(W, s(SS,_,W,_,_,_), SynSet).	
	
% Searching for Max, Min and Alone synsets
max_ss(Top, Num) :-
	%s(Top,_,_,_,_,_),
	hyp(_, Top),
	atom_chars(Top, [Num |_]),
	\+hyp(Top, _).

min_ss(Bot, Num) :-
	%s(Bot,_,_,_,_,_),
	hyp(Bot, _),
	atom_chars(Bot, [Num |_]),
	\+hyp(_, Bot).

alone_ss(Alone, Num) :-
	s(Alone,_,_,_,_,_),
	atom_chars(Alone, [Num |_]),
	\+hyp(Alone, _),
	\+hyp(_, Alone).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% Transitivity feature of Hyp/2 relation
hypernym(SS1, SS2) :- 
	nonvar(SS1), 
	nonvar(SS2),
	SS1 = SS2,
	!.

hypernym(SS, SS).	

hypernym(SS1, SS2) :-
	nonvar(SS1) -> 
		hyp(SS1, SSX),
		hyp_(SSX, SS2);
	nonvar(SS2) ->
		hyp(SSX, SS2),
		hyp_(SS1, SSX).
	
hyp_(X, X).	
	
hyp_(X, Y) :-
	nonvar(X) -> 
		hyp(X, Z),
		hyp_(Z, Y);
	nonvar(Y) ->
		hyp(Z, Y),
		hyp_(X, Z).	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% equivalence feature of sim/2 relation
similar(SS1, SS2) :- 
	nonvar(SS1), 
	nonvar(SS2),
	SS1 = SS2,
	!.
	
similar(SS1, SS2) :-
	nonvar(SS1) -> 
		sim(SS1, SSX),
		sim_(SSX, SS2);
	nonvar(SS2) ->
		sim(SSX, SS2),
		sim_(SS1, SSX).
	
sim_(X, X).	
	
sim_(X, Y) :-
	nonvar(X) -> 
		sim(X, Z),
		sim_(Z, Y);
	nonvar(Y) ->
		sim(Z, Y),
		sim_(X, Z).	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% Transitivity feature of Hyp/2 relation
% with list of banned SynSets	
% hypernym is not reflexive!!!
hypernym_ban(SS1, Banned, SS2) :-
	nonvar(SS1) -> 
		\+member(SS1, Banned),
		hyp(SS1, SSX),
		\+member(SSX, Banned),
		hyp_ban(SSX, Banned, SS2);
	nonvar(SS2) ->
		\+member(SS2, Banned),
		hyp(SSX, SS2),
		\+member(SSX, Banned),
		hyp_ban(SS1, Banned, SSX).
	
hyp_ban(X, Banned, X) :-
	\+member(X, Banned).	
	
hyp_ban(X, Banned, Y) :-
	nonvar(X) -> 
		\+member(X, Banned),
		hyp(X, Z),
		\+member(Z, Banned),
		hyp_ban(Z, Banned, Y);
	nonvar(Y) ->
		\+member(Y, Banned),
		hyp(Z, Y),
		\+member(Z, Banned),
		hyp_ban(X, Banned, Z).	
	

		

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% checks if two words have common children sysnsets
word_shared_children(W1, W2, Num, W_List) :-
	nonvar(W1), 
	nonvar(W2),
	s(SS1,_,W1,_,_,_),
	atom_chars(SS1, [Num  |_]),
	s(SS2,_,W2,_,_,_),
	atom_chars(SS2, [Num  |_]),
	( hypernym(SS1, SS2) -> 
		SSX = SS1, 
		findall(W, s(SSX,_,W,_,_,_), W_List);
	  hypernym(SS2, SS1) -> 
		SSX = SS2,
		findall(W, s(SSX,_,W,_,_,_), W_List);
	  findall(SS, hypernym(SS, SS1), SS_List),
	  member(SSX, SS_List),
	  hypernym(SSX, SS2),
	  findall(W, s(SSX,_,W,_,_,_), W_List) ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% W1 and W2 are derived from each other through path with depth
word_derivation(W1, W2, Depth, Path) :-
	nonvar(W1), 
	nonvar(W2),
	s(SS1,_,W1,_,_,_),
	s(SS2,_,W2,_,_,_),
	der_(SS1, [], Path1, SS2, Depth),
	append(Path1, [SS2], Path).	

% transitive version of der/2 
% also measures depth since relation is not pure e.g. der_(protective, guardian) 
der_(X, Path1, [], X, Depth) :-		% reflexive 
	length(Path1, N),    			% needs limit 
	N =< Depth.			

der_(X, Old_Path, [X | Path], Y, Depth) :-		% at least one step
	length(Old_Path, N),					% needs limit 
	N =< Depth,									
	der(X, _, Z, _),
	\+member(Z, Old_Path),
	append(Old_Path, [X], Temp_Path),
	%D is Depth - 1,
	der_(Z, Temp_Path, Path, Y, Depth).
	%append(Temp_Path, Path, New_Path).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% whether all senses of a word isa Word who has uniq sysnset
all_senses_hyp_uniq(Word, Num, Class) :-
	%pos_to_cat_num(POS, Num),
	( findall(SS2, s(SS2, _, Class, _, _, _), [SS_Class]) -> true
	; report(['Error: ', Class, ' has multi-SynSets']),  false 
	),
	atom_chars(SS_Class, [Num |_]),
	findall(SS1, 
			( s(SS1, _, Word, _, _, _), atom_chars(SS1, [Num |_]) ), 
			All_SS_Word ),
	findall(SS_Class, member(_,All_SS_Word), SS_Class_List),
	once(maplist(hypernym, All_SS_Word, SS_Class_List)).
 	/*findall(SS2,
			(member(SS2, All_SS_Word), hypernym(SS2, SS_Class)),
			All_SS_Word ).*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% whether none of senses of a word isa Word who has uniq sysnset
none_senses_hyp_uniq(Word, Num, Class) :-
	%pos_to_cat_num(POS, Num),
	( findall(SS2, s(SS2, _, Class, _, _, _), [SS_Class]) -> true
	; report(['Error: ', Class, ' has multi-SynSets']),  false 
	),
	atom_chars(SS_Class, [Num |_]),
	findall(SS1, 
			( s(SS1, _, Word, _, _, _), atom_chars(SS1, [Num |_]) ), 
			All_SS_Word ),
	%findall(SS_Class, member(_,All_SS_Word), SS_Class_List),
	%maplist(hypernym, All_SS_Word, SS_Class_List).
 	findall(SS2, (member(SS2, All_SS_Word), hypernym(SS2, SS_Class)), [] ).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% two words having antonimous senses
% ignore Wnum parameter and take antonym relatuion between sysnsets? 
% as a result grant and deny are now antonimes 
% 202212825-deny-refuse and 202255462-allow-grant and ant(202212825,1,202255462,1)
word_ant(W1, W2, Num) :- 
	(nonvar(W1), nonvar(W2)) ->
		s(SS1, _, W1, _, _, _),
		atom_chars(SS1, [Num |_]),	
		s(SS2, _, W2, _, _, _),
		ant(SS1,_, SS2,_);
	nonvar(W1) ->
		s(SS1, _, W1, _, _, _),
		atom_chars(SS1, [Num |_]),	
		ant(SS1,_, SS2,_),
		s(SS2, _, W2, _, _, _);
	nonvar(W2) ->
		s(SS2, _, W2, _, _, _),
		atom_chars(SS2, [Num |_]),	
		ant(SS1,_, SS2,_),
		s(SS1, _, W1, _, _, _);
	fail.	
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% extract relations from WordNet
% extract thise antonyms and those hypernyms and hyponyms that are found in Lexicon
rels_from_wn(Lex) :-
	include(lemPos_in_WordNet, Lex, Lexicon),
	retractall(isa_wn(_, _)),
	retractall(ant_wn(_, _)),
	retractall(dis_wn(_, _)),
	findall_pairs(Lexicon, Pairs),
	maplist(assert_wn_rels, Pairs),
	( debMode('wn_dis') -> 
		findall_pairSets(Lexicon, PairSets),
		maplist(assert_dis_wn, PairSets)
	; true
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checks if (Word, POS) is in wordnet
lemPos_in_WordNet((Lemma, POS)) :-
	pos_to_cat_num(POS, Num),
	s(SS, _, Lemma, _, _, _),
	atom_chars(SS, [Num |_]),
	!.	
	
	



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% extract sun_Wordnet from WordNet
% extract all antonyms and all hypernyms and hyponyms
subWN_from_wn(Lexicon) :-
	retractall(isa_wn(_, _)),
	retractall(ant_wn(_, _)),
	extract_sub_wn(Lexicon).
	

extract_sub_wn([(Lm,POS) | Rest]) :-
	pos_to_cat_num(POS, Num), 
	!,
	findall(isa_wn(Lm, Up), word_hyp(Lm, Up, Num), HyperList),
	findall(isa_wn(Dw, Lm), word_hyp(Dw, Lm, Num), HyponList), % filter from synonyms
	append(HyperList, HyponList, IsaList),
	list_to_set(IsaList, IsaSet),
	maplist(asserta, IsaSet),
	( debMode('wn_ant') ->
		findall(ant_wn(Lm, Ant), word_ant(Lm, Ant, Num), AntList),
		list_to_set(AntList, AntSet),
		maplist(asserta, AntSet)
	  ; true
	),
	extract_sub_wn(Rest).

extract_sub_wn([_ | Rest]) :-
	!,
	extract_sub_wn(Rest).
	
extract_sub_wn([]).		


:- dynamic isa_wn/2.
isa_wn(0, 0).
:- dynamic ant_wn/2.
ant_wn(0, 0).


assert_wn_rels((Lemma1, Lemma2, Num)) :-
	substitute_in_atom(Lemma1, '_', ' ', Lem1),
	substitute_in_atom(Lemma2, '_', ' ', Lem2),
	(word_hyp(Lem2, Lem1, Num) -> 
	 %word_h_(Lem2, Lem1, Num) -> 
		%write('new: '), term_to_atom(isa_wn(Lem2, Lem1), At), writeln(At),
	  	assert(isa_wn(Lemma2, Lemma1))
	; true),
	( debMode('wn_ant'), word_ant(Lem1, Lem2, Num) ->
	  	%assert(ant_wn(Lemma1, Lemma2)), %since paits are symetric
	  	assert(ant_wn(Lemma2, Lemma1))
	; true)
	.

:- dynamic dis_wn/2.
dis_wn(0, 0).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% check if all senses of a word are under/out of a big class
% if so then they are disjoint and assert it
assert_dis_wn_class(Lem1, Lem2, Num, Class) :-
	( all_senses_hyp_uniq(Lem1, Num, Class), 
      none_senses_hyp_uniq(Lem2, Num, Class),
	  asserta(dis_wn(Lem1, Lem2))  %, report([dis_wn(Lem1, Lem2)])
    ; none_senses_hyp_uniq(Lem2, Num, Class),
      all_senses_hyp_uniq(Lem1, Num, Class), 
	  asserta(dis_wn(Lem1, Lem2)) %, report([dis_wn(Lem1, Lem2)])
	; true
	), 
	!.

assert_dis_wn((Lem1, Lem2, Num)) :-
	Classes = ['physical object', 'craniate'],
	maplist(assert_dis_wn_class(Lem1, Lem2, Num), Classes).
		
	
	

findall_pairs(Lexicon, Pairs) :-
	findall((Lem1, Lem2, Num), 
	  ( member(P1, Lexicon), 
		member(P2, Lexicon), 
		P1 = (Lem1, Pos1), %!!! change use Type too
		P2 = (Lem2, Pos2),
		Lem1 \= Lem2,
		pos_to_cat_num(Pos1, Num),
		pos_to_cat_num(Pos2, Num)
	  ),
	  Pairs).  

% more efficient?
findall_pairSets(Lexicon, PairSets) :-
	%length(Lexicon, Len),
	findall((Lem1, Lem2, Num), 
	  ( nth1(N1, Lexicon, (Lem1, Pos1)),
		%Low is N1 + 1,
		%between(Low, N2, Len), 
		nth1(N2, Lexicon, (Lem2, Pos2)), 
		N1 < N2,
		Lem1 \= Lem2,
		pos_to_cat_num(Pos1, Num),
		pos_to_cat_num(Pos2, Num)
	  ),
	  PairSets). 


	
pos_to_cat_num(POS, Num) :-
	atom_chars(POS, [A1, A2 | _]), 
	( A1 = 'N', A2 = 'N' -> Num = '1';
	  A1 = 'V', A2 = 'B' -> Num = '2';
	  A1 = 'J', A2 = 'J' -> Num = '3';
	  A1 = 'R', A2 = 'B' -> Num = '4' ).

	
		
		
