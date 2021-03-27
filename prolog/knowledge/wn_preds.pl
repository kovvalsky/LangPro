%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% :- module(wn_preds,
% 	[
% 		kb_from_wn/2,
% 		word_hyp/3
% 	]).

:- use_module('disjoint', [disj_/2]).
:- use_module('../utils/generic_preds', [substitute_in_atom/4]).
:- use_module('../printer/reporting', [report/1]).

:- dynamic debMode/1.

:- multifile ant/4, der/4, hyp/2, ins/2, s/6, sim/2.
:- discontiguous ant/4, der/4, hyp/2, ins/2, s/6, sim/2.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Extracting relations from WordNet
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Extract semantic relations for KB from WordNet
kb_from_wn(Lex, KB) :-
	findall(Lem_Num,
		( member(Lem_Pos, Lex), lemPos_in_WordNet(Lem_Pos, Lem_Num) ),
		Lem_Nums),
	sort(Lem_Nums, Lexicon),
	findall_pairs(Lexicon, Pairs),
	findall(Fact,
		( member(X, Pairs), represents_wn_rel(X, Fact) ),
		KB).

% extract relations from WordNet
% extract these antonyms and those hypernyms and hyponyms that are found in Lexicon
/*rels_from_wn(Lex) :-
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
*/

ss_type_to_num(Type, Num) :-
	( Type == 'n' -> Num = '1'
	; Type == 'v' -> Num = '2'
	; Type == 'a' -> Num = '3'
	; Type == 's' -> Num = '3'
	; Type == 'r' -> Num = '4'
	; fail ).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checks if (Word, POS) is in wordnet
lemPos_in_WordNet((Lemma, POS), (Lemma, Num)) :-
	pos_to_cat_num(POS, Num),
	s(_,_,Lemma,Type,_,_),
	ss_type_to_num(Type, Num),
	!.

% Takes a lexicon and returns all possible pairs of different ellements
% sharing the same Wordnt class type
findall_pairs(Lexicon, Pairs) :-
	findall( P1-P2,
	  ( member(P1, Lexicon),
		member(P2, Lexicon),
		P1 \= P2
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

% conbert POS to number category of WN
pos_to_cat_num(POS, Num) :-
	atom_chars(POS, [A1, A2 | _]),
	( A1 = 'N', A2 = 'N' -> Num = '1';
	  A1 = 'V', A2 = 'B' -> Num = '2';
	  A1 = 'J', A2 = 'J' -> Num = '3';
	  A1 = 'R', A2 = 'B' -> Num = '4' ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Takes a pair and checks what relation holds on them
represents_wn_rel( (Lem1,Num1)-(Lem2,Num2), Fact ) :-
	substitute_in_atom(Lem1, '_', ' ', L1),
	substitute_in_atom(Lem2, '_', ' ', L2),
	( Num1 = Num2, word_hyp(L1, L2, Num1) ->
	  	Fact = isa_wn(L1, L2)
	; debMode('wn_ant'), Num1 = Num2, word_ant(L1, L2, Num1) ->
	  	%assert(ant_wn(Lemma1, Lemma2)), %since paits are symetric
	  	Fact = ant_wn(L1, L2)
	; debMode('wn_der'), word_der(L1, L2) ->
		Fact = der_wn(L1, L2)
	; debMode('wn_sim'), Num1 = Num2, word_sim(L1, L2, Num1) ->
		Fact = sim_wn(L1, L2)
	; debMode('disj'), disj_(L1, L2) ->
		Fact = disj(L1, L2)
	).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% check if all senses of a word are under/out of a big class
% if so then they are disjoint and assert it
/*
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
*/


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   Defining Semantic relations based on WN relations
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% given Lemmas, it check hypernym relation between their SynSets
% strict hypernymy, non-reflexive
word_hyp(W1, W2, Num) :-
	debMode(ss(List)) ->
	  word_hyp(List, W1, W2, Num, _, _, _Path)
	; word_hyp(_, W1, W2, Num, _, _, _Path).


word_hyp(SNs, W1, W2, Num, SN1, SN2, Path) :-
	( nonvar(W1), nonvar(W2) ->
		s(SS1, _, W1, Type1, SN1, _),
		ss_type_to_num(Type1, Num),
		memberchk(SN1, SNs),
		s(SS2, _, W2, _, SN2, _),
		memberchk(SN2, SNs),
		hyp_(SS1, Path, [], SS2)
	; nonvar(W1) ->
		s(SS1, _, W1, Type1, SN1, _),
		ss_type_to_num(Type1, Num),
		memberchk(SN1, SNs),
		hyp_(SS1, Path, [], SS2),
		s(SS2, _, W2, _, SN2, _),
		memberchk(SN2, SNs)
	; nonvar(W2) ->
		s(SS2, _, W2, Type2, SN2, _),
		ss_type_to_num(Type2, Num),
		memberchk(SN2, SNs),
		hyp_(SS1, Path, [], SS2),
		s(SS1, _, W1, _, SN1, _),
		memberchk(SN1, SNs)
	; false ).

% print all hypernyms or hyponyms of a given word
print_all_word_hyp(W1, W2) :-
	% exactly one is (non)var
	( var(W1) -> nonvar(W2), A = 1, W1 = Ord_NWs
	; var(W2), A = 2, W2 = Ord_NWs ),
	findall(W1-W2-N, word_hyp(W1, W2, N), WWNs),
	maplist({A}/[XY-L, L-Z]>>arg(A,XY,Z), WWNs, NWs),
	sort(0, @<, NWs, Ord_NWs),
	maplist(writeln, Ord_NWs).

%%%%%%%%%%%%%%%%%%%%%%%
% Transitive closure of hyp/2 WN relation
% non-reflexive
hypernym(SS1, SS2) :-
	nonvar(SS1) ->
		hyp(SS1, SSX),
		hyp_(SSX, _Path, [], SS2);
	nonvar(SS2) ->
		hyp(SSX, SS2),
		hyp_(SS1, _Path, [], SSX).

% reflexive and transitive hyp/2
% avoids loops (EN-WN has no loop but ODWN has "word_hyp(buurt, jongen, '1').")
hyp_(X, Path, Path, X).

hyp_(X, End, Start, Y) :-
	nonvar(X) ->
		hyp(X, Z),
		\+memberchk(Z, Start),
		append(Start, [Z], Start1),
		hyp_(Z, End, Start1, Y);
	nonvar(Y) ->
		hyp(Z, Y),
		\+memberchk(Z, Start),
		hyp_(X, End, [Z|Start], Z).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% given Lemmas, it check similarity relation between their SynSets
% it is not reflexive and transitive
word_sim(W1, W2, Num) :-
	debMode(ss(List)) ->
		word_sim(List, W1, W2, Num)
	; word_sim(_, W1, W2, Num).


word_sim(SNs, W1, W2, Num) :-
	( nonvar(W1), nonvar(W2) ->
		s(SS1, _, W1, Type1, SN1, _),
		ss_type_to_num(Type1, Num),
		memberchk(SN1, SNs),
		s(SS2, _, W2, _, SN2, _),
		%atom_chars(SS1, [Num |_]),
		memberchk(SN2, SNs),
		sim(SS1, SS2)
	; nonvar(W1) ->
		s(SS1, _, W1, Type1, SN1, _),
		ss_type_to_num(Type1, Num),
		memberchk(SN1, SNs),
		sim(SS1, SS2),
		s(SS2, _, W2, _, SN2, _),
		memberchk(SN2, SNs)
	; nonvar(W2) ->
		s(SS2, _, W2, Type2, SN2, _),
		ss_type_to_num(Type2, Num),
		memberchk(SN2, SNs),
		sim(SS1, SS2),
		s(SS1, _, W1, _, SN1, _),
		memberchk(SN1, SNs)
	 ; false ).

/*
%%%%%%%%%%%%%%%%%%%%
% non-reflexive similarity
similar(SS1, SS2) :-
	nonvar(SS1) ->
		sim(SS1, SSX),
		sim_(SSX, SS2);
	nonvar(SS2) ->
		sim(SSX, SS2),
		sim_(SS1, SSX).

% reflexive sim/2
sim_(X, X).

sim_(X, Y) :-
	nonvar(X) ->
		sim(X, Z),
		sim_(Z, Y);
	nonvar(Y) ->
		sim(Z, Y),
		sim_(X, Z).
*/


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% W1 and W2 are connected with symmetric wn_der
% non-reflexive and transitive
word_der(W1, W2) :-
	debMode(ss(List)) ->
		word_der(List, W1, _, W2, _)
	; word_der(_, W1, _, W2, _).

word_der(SNs, W1, N1, W2, N2) :-
	( nonvar(W1), nonvar(W2) ->
		s(SS1, N1, W1, _, SN1, _),
		s(SS2, N2, W2, _, SN2, _),
		memberchk(SN1, SNs), memberchk(SN2, SNs),
		der_(SS1, N1, [SS1-N1], SS2, N2)
		%der(SS1, N1, SS2, N2)
	; nonvar(W1) ->
		s(SS1, N1, W1, _, SN1, _),
		memberchk(SN1, SNs),
		der_(SS1, N1, [SS1-N1], SS2, N2),
		%der(SS1, N1, SS2, N2),
		s(SS2, N2, W2, _, SN2, _),
		memberchk(SN2, SNs)
	; nonvar(W2) ->
		s(SS2, N2, W2, _, SN2, _),
		memberchk(SN2, SNs),
		der_(SS1, N1, [SS2-N2], SS2, N2),
		%der(SS1, N1, SS2, N2),
		s(SS1, N1, W1, _, SN1, _),
		memberchk(SN1, SNs)
	; false ).

/*
derivation(SS1, N1, SS2, N2) :-
	nonvar(SS1), nonvar(N1) ->
		der(SS1, N1, SSX, NX),
		der_(SSX, NX, _, SS2, N2)
	; nonvar(SS2), nonvar(N2) ->
		der(SSX, NX, SS2, N2),
		der_(SS1, N1, _, SSX, NX).
*/
% reflexive and transitive der/2
% avoids loops with Path
der_(X, N, _Paths, X, N).

der_(X, NX, Path, Y, NY) :-
	length(Path, Len),
	Len =< 3, % can make things effcient
	( nonvar(X), nonvar(NX) ->
		der(X, NX, Z, NZ),
		\+memberchk(Z-NZ, Path),
		der_(Z, NZ, [Z-NZ|Path], Y, NY)
	; nonvar(Y), nonvar(NY) ->
		der(Z, NZ, Y, NY),
		\+memberchk(Z-NZ, Path),
		der_(Z, NZ, [Z-NZ|Path], Y, NY)
	).

% W1 and W2 are derived from each other through path with depth
% more complcated der, with transitive closure
/*
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
*/




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% two words having antonimous senses
% ignore Wnum parameter and take antonym relatuion between sysnsets?
% as a result grant and deny are now antonimes
% 202212825-deny-refuse and 202255462-allow-grant and ant(202212825,1,202255462,1)
word_ant(W1, W2, Num) :-
	debMode(ss(List)) ->
		word_ant(List, W1, W2, Num)
	; word_ant(_, W1, W2, Num).

word_ant(SNs, W1, W2, Num) :-
	( nonvar(W1), nonvar(W2)) ->
		s(SS1, _, W1, Type1, SN1, _),
		memberchk(SN1, SNs),
		ss_type_to_num(Type1, Num),
		s(SS2, _, W2, _, SN2, _),
		memberchk(SN2, SNs),
		ant(SS1,_, SS2,_) % relaxed
 	; nonvar(W1) ->
		s(SS1, _, W1, Type1, SN1, _),
		ss_type_to_num(Type1, Num),
		memberchk(SN1, SNs),
		ant(SS1,_, SS2,_),  % relaxed
		s(SS2, _, W2, _, SN2, _),
		memberchk(SN2, SNs)
	; nonvar(W2) ->
		s(SS2, _, W2, Type2, SN1, _),
		ss_type_to_num(Type2, Num),
		memberchk(SN1, SNs),
		ant(SS1,_, SS2,_), % relaxed
		s(SS1, _, W1, _, SN1, _),
		memberchk(SN1, SNs).










%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checks if two words have common children sysnsets
word_shared_children(W1, W2, Num, W_List) :-
	nonvar(W1),
	nonvar(W2),
	s(SS1,_,W1,Type1,_,_),
	ss_type_to_num(Type1, Num),
	s(SS2,_,W2,Type2,_,_),
	ss_type_to_num(Type2, Num),
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
% whether all senses of a word isa Word who has uniq sysnset
all_senses_hyp_uniq(Word, Num, Class) :-
	%pos_to_cat_num(POS, Num),
	( findall(SS2-Type, s(SS2, _, Class, Type, _, _), [SS_Class-Type_Class]) -> true
	; report(['Error: ', Class, ' has multi-SynSets']),  false
	),
	ss_type_to_num(Type_Class, Num),
	findall(SS1,
			( s(SS1, _, Word, Type, _, _), ss_type_to_num(Type, Num) ),
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
	( findall(SS2-Type, s(SS2, _, Class, Type, _, _), [SS_Class-Type_Class]) -> true
	; report(['Error: ', Class, ' has multi-SynSets']),  false
	),
	ss_type_to_num(Type_Class, Num),
	findall(SS1,
			( s(SS1, _, Word, Type, _, _), ss_type_to_num(Type, Num) ),
			All_SS_Word ),
	%findall(SS_Class, member(_,All_SS_Word), SS_Class_List),
	%maplist(hypernym, All_SS_Word, SS_Class_List).
 	findall(SS2, (member(SS2, All_SS_Word), hypernym(SS2, SS_Class)), [] ).



/*
have_sibling_senses(W1, W2) :-
	s
*/








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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%     Querying WordNet predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Finds Hypernym SynSet as a list for a word
word_hyp_ss(W1, W_List, Num) :-
	nonvar(W1),
	s(SS1,_,W1,Type1,_,_),
	ss_type_to_num(Type1, Num),
	hypernym(SS1, SS2),
	findall(W, s(SS2,_,W,_,_,_), W_List).

word_dir_hyper_ss(W1, W_List, Num) :-
	nonvar(W1),
	s(SS1,_,W1,Type1,_,_),
	ss_type_to_num(Type1, Num),
	hyp(SS1, SS2),
	findall(W, s(SS2,_,W,_,_,_), W_List).

word_dir_hypon_ss(W1, W_List, Num) :-
	nonvar(W1),
	s(SS1,_,W1,Type1,_,_),
	ss_type_to_num(Type1, Num),
	hyp(SS2, SS1),
	findall(W, s(SS2,_,W,_,_,_), W_List).

% prints Synsets of all senses of the word
word_ss(W1, W_List, Num) :-
	nonvar(W1),
	s(SS1,_,W1,Type1,_,_),
	ss_type_to_num(Type1, Num),
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

% Searching for Max, Min and Alone synsets
max_ss(Top, Num) :-
	%s(Top,_,_,_,_,_),
	hyp(_, Top),
	s(Top,_,_,Type,_,_),
	ss_type_to_num(Type, Num),
	\+hyp(Top, _).

min_ss(Bot, Num) :-
	%s(Bot,_,_,_,_,_),
	hyp(Bot, _),
	s(Bot,_,_,Type,_,_),
	ss_type_to_num(Type, Num),
	\+hyp(_, Bot).

alone_ss(Alone, Num) :-
	s(Alone,_,_,Type,_,_),
	ss_type_to_num(Type, Num),
	\+hyp(Alone, _),
	\+hyp(_, Alone).
