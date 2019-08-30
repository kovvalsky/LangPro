%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module('assign_term',
	[
		assign_term/7
	]).

:- use_module('../utils/user_preds', [ttExp_to_ttTerm_info/3]).
:- use_module('../lambda/lambda_tt', [op(605, yfx, @), op(605, xfy, ~>)]).
:- use_module('../knowledge/lexicon', [op(640, xfy, ::), '::'/2]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% assigns lambda term according to type cat and POS

% term = lemma, from lexicon
assign_term(_, Lemma, _, _, _, Type, Term) :-
	(Lemma :: Type :: _ -> 
		Term = Lemma;
	(Lemma, Type) == ( an, (e~>t)~>(e~>t)~>t ) ->
		Term = a;
	(Lemma, Type) == ( some, (e~>t)~>(e~>t)~>t ) ->
		Term = a;
	(Lemma, Type) == ( the, (e~>t)~>(e~>t)~>t ) ->
		Term = a;
	(Lemma, Type) == ( each, (e~>t)~>(e~>t)~>t ) ->
		Term = every;
	fail),
	!.
% term = lemma, e
assign_term(_, Lemma, POS, _, _, e, Term) :-
	( 	POS = 'CD';
		POS = 'NNP';
		POS = 'JJ'
	), !,
	Term = Lemma.
% term = lemma, (e~>t)~>(e~>t)~>t
assign_term(_, Lemma, POS, _, _, Type, Term) :-
	(POS, Type) = ('CD', (e~>t)~>(e~>t)~>t),
	!,
	Term = Lemma.
% term = lemma, e~>t
assign_term(_, Lemma, POS, _, _, e~>t, Term) :-
	( 	POS = 'NN';
		POS = 'NNS';
		%POS = 'UH'; % for "smash" - offspring album
		POS = 'DT'; % probably wrong
		atom_chars(POS, ['J','J'|_])		
	), !,
	Term = Lemma.

% Determiner a, the
assign_term(_, _, POS, _, _, Type, Term) :-
	( 	(POS, Type) = ('DT', (e~>t)~>(e~>t)~>t)
	), !,
	Term = a.

% comma as and
assign_term(_, Lemma, POS, _, Cat, Type, Term) :-
	( 	(POS, Cat) = (',', comma)
	), !,
	ttExp_to_ttTerm_info(and, (Term, Type), Lemma).

% Cardinals
assign_term(_, Lemma, 'CD', _, n~>n, Type, Term) :- 
	!, % add some details from TLP to avoid years
	_x = (_, e),
	_p = (_, e~>t),
	Result = (Lemma, (e~>t)~>(e~>t)~>t) @ _p @ 'Univ',
	ttExp_to_ttTerm_info( abst(_p, abst(_x, Result)), (Term, Type), Lemma).

% term = abst(X, is(X, lemma))
assign_term(_, Lemma, POS, _, _, Type, Term) :-
	( 	(POS, Type) = ('NNP', e~>t);
		(POS, Type) = ('NNPS', e~>t);
		(POS, Type) = ('CD', e~>t)
	), !,
	_x = (_, e),
	ttExp_to_ttTerm_info( abst(_x, is @ _x @ (Lemma, e)), (Term, Type), Lemma).

% Type rising: abst(P, P @ lemma)
assign_term(_, Lemma, POS, _, _, Type, Term) :- 
	(	(POS, Type) = ('CD', (e~>t)~>t);
		(POS, Type) = ('NNP', (e~>t)~>t);
		(POS, Type) = ('UH', (e~>t)~>t); % probably wrong, for "Smash"
		(POS, Type) = ('PRP', (e~>t)~>t); % temporar solution
		(POS, Type) = ('DT', (e~>t)~>t); % temporar solution
		(POS, Type) = ('JJR', (e~>t)~>t) % temporar solution
	), !,
	P = (_, e~>t),
	ttExp_to_ttTerm_info( abst(P, P @ (Lemma, e)), (Term, Type), Lemma).

% apply a: a @ lemma
assign_term(_, Lemma, POS, _, _, Type, Term) :- 
	(	(POS, Type) = ('NN', (e~>t)~>t)
	), !,
	ttExp_to_ttTerm_info( a @ (Lemma, e~>t), (Term, Type), Lemma).

% apply p: p @ lemma
assign_term(_, Lemma, POS, _, _, Type, Term) :- 
	(	(POS, Type) = ('NNS', (e~>t)~>t);  % incorrect semantics in negative context
		(POS, Type) = ('NNPS', (e~>t)~>t)
	), !,
	ttExp_to_ttTerm_info( p @ (Lemma, e~>t), (Term, Type), Lemma).

% adjectives: and @ lemma 
assign_term(_, Lemma, POS, _, _, Type, Term) :- 
	(	atom_chars(POS, ['J','J'|_]), 	 % very simple solution
			Type = (e~>t)~>e~>t; 		% not all adjectives
		(POS, Type) = ('NN', (e~>t)~>e~>t);
		(POS, Type) = ('NNS', (e~>t)~>e~>t);
		(POS, Type) = ('RB', (e~>t)~>e~>t); % e.g. there, very, only
		(POS, Type) = ('IN', (e~>t)~>e~>t)  % e.g. about
	), !,
	ttExp_to_ttTerm_info(and @ (Lemma, e~>t), (Term, Type), Lemma).

% Verbs: abst x. Lemma x e
assign_term(_, Lemma, POS, _, _, Type, Term) :- 
	(	atom_chars(POS, ['V','B'|_]), 	 % very simple solution
			Type = (e~>t)~>e~>t 		% not all verbs, VBG, VBN
	), !,
	_x = (_, e),
	_e = (_, e),
	ttExp_to_ttTerm_info(and @ abst(_x, (Lemma, e~>e~>e~>t) @_x@'*'@_e), (Term, Type), Lemma).

% nominal modifiers: 
assign_term(_, Lemma, POS, _, _, Type, Term) :- 
	(	%(POS, Type) = ('NN', (e~>t)~>e~>t); % NNS can be added
		(POS, Type) = ('NNP', (e~>t)~>e~>t);
		(POS, Type) = ('NNPS', (e~>t)~>e~>t)
	), !,
	_n = (_, e~>t),
	%_x = (_, e),	%_y = (_, e),
	%(POS = 'NN' -> 
		%Conjunct = a @ (Lemma,e~>t) @ (abst(_y,of @_y@_x));
	%atom_chars(POS, ['N','N','P'| _]) -> 
		Conjunct = of @ (Lemma,e),
	ttExp_to_ttTerm_info(abst(_n, and @ _n @ Conjunct), (Term, Type), Lemma).

% WH words of type (np~>s:dcl)~>np~>np
assign_term(_, Lemma, POS, _, Cat, Type, Term) :- 
	(Cat, Type) = ((np~>s:dcl)~>np~>np, VP~>NP~>NP),
	(	POS = 'WDT';
		POS = 'WP'
	), !,
	V = (_, VP),
	P = (_, NP),
	P1 = (_,(e~>t)~>NP),
	P2 = (_,e~>t),
	P0 = (P1 @ P2, NP),
	_q = (_, e~>t),
	_x = (_, e),
	Result2 = and @ (V @ P @ 'Univ') @ (P @ _q),
	Result1 = P1 @ (and @ P2 @ abst(_x, V @ abst(_q,_q@_x) @ 'Univ')),
	(ttExp_to_ttTerm_info(abst(V, abst(P0, Result1)), (Term, Type), Lemma);
	 ttExp_to_ttTerm_info(abst(V, abst(P, abst(_q, Result2))), (Term, Type), Lemma)
	).

% (N->N)->N->N, very bad approximation
assign_term(_, Lemma, POS, _, Cat, Type, Term) :- 
	(	(Cat, Type) = ((n~>n)~>n~>n, NN~>N~>N),
		member(POS, ['RB', 'NN', 'CD'])
	), !,
	M = (_, NN),
	_p = (_, N),
	Result = M @ (and @ _p @ (Lemma, N)),
	ttExp_to_ttTerm_info(abst(M, abst(_p, Result)), (Term, Type), Lemma).

% prepositions: IN: np-->(np-->s)-->(np-->s)
assign_term(_, Lemma, POS, _, Cat, Type, Term) :- 
	(	(POS, Cat, Type) = ('IN', np~>(np~>s)~>(np~>s), NP ~> VP ~> VP);
		(POS, Cat, Type) = ('IN', np~>(np~>s:dcl)~>(np~>s:dcl), NP ~> VP ~> VP);
		(POS, Cat, Type) = (_, np~>(np~>s:dcl)~>(np~>s:dcl), NP ~> VP ~> VP); % RB, VBG, FW *
		(POS, Cat, Type) = ('IN', np~>(np~>s:pss)~>(np~>s:pss), NP ~> VP ~> VP);
		(POS, Cat, Type) = ('IN', np~>(np~>s:pt)~>(np~>s:pt), NP ~> VP ~> VP);  % no VBG (including) 
		(POS, Cat, Type) = ('IN', np~>(np~>s:b)~>(np~>s:b), NP ~> VP ~> VP);
		(POS, Cat, Type) = ('IN', np~>(np~>s:ng)~>(np~>s:ng), NP ~> VP ~> VP)
	), !,
	P = (_, NP),	Q = (_, NP),
	_x = (_, e),	_e = (_, e),
	V = (_, VP),	
	_p = (_, e~>t),
	Event_mod = and @ _p @ abst(_e, P @ abst(_x, Lemma @ _x @ _e)), % lemma
	ttExp_to_ttTerm_info( abst(P, abst(V, abst(Q, abst(_p, V @ Q @ Event_mod)))), (Term, Type), Lemma).


% prepositions: IN: np-->n~>n
assign_term(_, Lemma, POS, _, Cat, Type, Term) :- 
	(	(POS, Cat, Type) = ('IN', np~>n~>n, NP ~> N ~> N) 
	), !,
	P = (_, NP),
	_x = (_, e),	_y = (_, e),
	_p = (_, N),
	Conjunct = P @ abst(_x, Lemma @ _x @ _y), % lemma
	ttExp_to_ttTerm_info( abst(P, abst(_p, abst(_y, and @ Conjunct @ (_p @ _y)))), (Term, Type), Lemma).


% prepositions: IN, TO: np-->pp
assign_term(_, Lemma, POS, _, Cat, Type, Term) :- 
	(	(POS, Cat, Type) = ('IN', np~>pp, NP ~> _);
		(POS, Cat, Type) = ('TO', np~>pp, NP ~> _)
	), !,
	P = (_, NP),
	_x = (_, e),	_y = (_, e),
	ttExp_to_ttTerm_info( abst(P, abst(_y, P @ abst(_x, Lemma@_x@_y))), (Term, Type), Lemma). 

% prepositions: IN: (np-->s:ng)~>pp
assign_term(_, Lemma, POS, _, Cat, Type, Term) :- 
	(	(POS, Cat, Type) = ('IN', (np~>s:ng)~>pp, VP ~> _)
	), !,
	V = (_, VP),
	_e = (_, e), 	_x = (_, e),
	_p = (_, e~>t),
	Result = V @ abst(_p, _p@'*') @ abst(_e, Lemma@_e@_x),
	ttExp_to_ttTerm_info( abst(V, abst(_x, Result)), (Term, Type), Lemma). 

% prepositions: IN: np-->s~>s
assign_term(_, Lemma, POS, _, Cat, Type, Term) :- 
	(	(POS, Cat, Type) = ('IN', np~>s:_~>s:_, NP ~> T ~> T) 
	), !,
	P = (_, NP),
	_x = (_, e),	_y = (_, e),
	_p = (_,e~>t),
	S = (_,T),
	Event_mod = and @ _p @ abst(_y, P @ abst(_x, Lemma@_x@_y)),
	ttExp_to_ttTerm_info( abst(P, abst(S, abst(_p, S @ Event_mod))), (Term, Type), Lemma). 

% adverb: RB: (NP~>S)~>NP~>S
assign_term(_, Lemma, POS, _, Cat, Type, Term) :- 
	(	(POS, Cat, Type) = ('RB', (np~>s:_)~>np~>s:_, VP~>TR~>TR);
		(POS, Cat, Type) = ('RB', (np~>s)~>np~>s, VP~>TR~>TR) 
	), !,
	V = (_, VP),
	P = (_, TR),
	_p = (_, e~>t),
	Conjunct = and @ (Lemma, e~>t) @ _p, 
	ttExp_to_ttTerm_info( abst(V, abst(P, abst(_p, V @ P @ Conjunct))), (Term, Type), Lemma).

% adverb: NN, NNP: (NP~>S:dcl)~>NP~>S:dcl
assign_term(_, Lemma, POS, (_, 'I-DAT'), Cat, Type, Term) :- 
	(	(POS, Cat, Type) = ('NN', (np~>s:dcl)~>np~>s:dcl, VP~>NP~>NP);
		(POS, Cat, Type) = ('NNP', (np~>s:dcl)~>np~>s:dcl, VP~>NP~>NP); 
		(POS, Cat, Type) = ('NN', (np~>s:pss)~>np~>s:pss, VP~>NP~>NP);
		(POS, Cat, Type) = ('NNP', (np~>s:pss)~>np~>s:pss, VP~>NP~>NP)
	), !,
	V = (_, VP),
	P = (_, NP),
	_t = (_, e~>t),
	Result = V @ P @ (and @ (event_time @ (Lemma, e~>t)) @ _t), 
	ttExp_to_ttTerm_info( abst(V, abst(P, abst(_t, Result))), (Term, Type), Lemma).

% adjective for adverb: JJ: ((NP~>S:dcl)~>NP~>S:dcl) ~> ((NP~>S:dcl)~>NP~>S:dcl)
assign_term(_, Lemma, POS, (_, Feat2), Cat, Type, Term) :-
	Cat = ((np~>s:dcl)~>np~>s:dcl) ~> (np~>s:dcl)~>np~>s:dcl, 
	Type = Mod~>VP~>NP~>NP,
	(POS = 'JJ', Feat2 = 'I-DAT' -> 
		Rel = event_time;
		Rel = rel), 
	!,
	V = (_, VP),
	P = (_, NP),
	M = (_, Mod),
	_t = (_, e~>t),
	Result = M @ V @ P @ (and @ (Rel @ (Lemma, e~>t)) @ _t), 
	ttExp_to_ttTerm_info( abst(M, abst(V, abst(P, abst(_t, Result)))), (Term, Type), Lemma).

% VBs, to: identity
assign_term(_, Lemma, POS, _, Cat, Type, Term) :- 
	(	(POS, Cat, Type) = ('TO', (np~>s:b)~>np~>s:to, X~>X);
		(POS, Cat, Type) = ('IN', s:dcl~>s:em, X~>X);
		(POS, Cat, Type) = ('RB', s:dcl~>s:dcl, X~>X);
		(POS, Cat, Type) = ('CC', s:dcl~>s:dcl, X~>X);
		(POS, Cat, Type) = ('NNP', s:dcl~>s:dcl, X~>X);
		atom_chars(POS, ['V', 'B' | _]),
			((Cat, Type) = ((np~>s:pss)~>np~>s:dcl, X~>X); %treat passives carefully
	 		 (Cat, Type) = ((np~>s:pt)~>np~>s:dcl, X~>X);  %tempral markers can be introduced
			 (Cat, Type) = ((np~>s:adj)~>np~>s:dcl, X~>X),
				Lemma = 'be'; %Gerunds
			 (Cat, Type) = ((np~>s:pss)~>np~>s:b, X~>X),
				Lemma = 'be'; % VB, be
			 (Cat, Type) = ((np~>s:pss)~>np~>s:pt, X~>X);  %verbnet info needed for passives
			 (Cat, Type) = ((np~>s:ng)~>np~>s:dcl, X~>X),
				Lemma = 'be') % to exclude: started doing ...
	), !,
	V = (_, X),
	(Term, Type) = (abst(V, V), X~>X). 

% Sentence conecctors adverbs: S~>(NP~>S)~>NP~>S
assign_term(_, Lemma, POS, _, Cat, Type, Term) :- 
	(	(POS, Cat, Type) = ('IN', s:dcl~>(np~>s:dcl)~>np~>s:dcl, T~>VP~>NP~>T);
		(POS, Cat, Type) = ('WRB', s:dcl~>(np~>s:dcl)~>np~>s:dcl, T~>VP~>NP~>T) 
	), !,
	V = (_, VP),
	S = (_, T),
	P = (_, NP),
	_q = (_, e~>t),
	_x = (_, e),	_y = (_, e),
	Event_mod = and @ _q @ abst(_x, S @ abst(_y, Lemma@_y@_x)), 
	ttExp_to_ttTerm_info( abst(S, abst(V, abst(P, abst(_q, V @ P @ Event_mod)))), (Term, Type), Lemma).

% 's , : POS : np~>(pp~>n)~>np
assign_term(_, Lemma, 'POS', _, Cat, Type, Term) :- 
	(	(Cat, Type) = (np~>(pp~>n)~>np, NP~>Mod~>N~>t),
			Pred = M @ '*',
			M = (_, Mod);
		(Cat, Type) = (np~>n~>np, NP~>N~>N~>t),
			Pred = M,
			M = (_, N)
	), !,
	P = (_, NP),
	_p = (_, N),
	_x = (_, e),	_y = (_, e),
	Result = a @ (and @ Pred @ abst(_x, P @ abst(_y, of@_y@_x))) @ _p, 
	ttExp_to_ttTerm_info( abst(P, abst(M, abst(_p, Result))), (Term, Type), Lemma).

% PRP$ : (pp~>n)~>np
assign_term(_, Lemma, 'PRP$', _, Cat, Type, Term) :- 
	(	(Cat, Type) = ((pp~>n)~>np, Mod~>N~>t)
	), !,
	M = (_, Mod),
	_p = (_, N),
	Result = a @ (and @ (M @ '*') @ (of @ (Lemma, e))) @ _p, 
	ttExp_to_ttTerm_info( abst(M, abst(_p, Result)), (Term, Type), Lemma).

% JJ : pp~>np~>s:adj
assign_term(_, Lemma, 'JJ', _, Cat, Type, Term) :- 
	(	(Cat, Type) = (pp~>np~>s:adj, N~>NP~>N~>t)
	), !,
	_t = (_, N),
	_q = (_, N),
	P = (_, NP),
	_e = (_,e),	_x = (_,e), 	_y = (_,e),
	%Result = P @ (and @ _q @ (Lemma, N)),
	Conjunct = P @ abst(_y, a @ (Lemma, e~>t) @ abst(_x, (Lemma, e~>e~>e~>t)@_x@_y@_e)),
	Result = and @ ((and@_t@_q) @_e) @ Conjunct,
	ttExp_to_ttTerm_info( abst(_q, abst(P, abst(_t, Result))), (Term, Type), Lemma).

% JJ or NNP : np~>s:adj
assign_term(_, Lemma, POS, _, Cat, Type, Term) :- 
	(	(Cat, Type) = (np~>s:adj, NP~>N~>t)
	),
	((atom_chars(POS, ['J','J'|_]); POS='RB') -> 
		SubTerm = a @ (Lemma, e~>t) @ abst(_x, IS@_x@_y@_e);
	POS = 'NNP' ->
		SubTerm = IS@(Lemma,e)@_y@_e),
	!,
	IS = (Lemma, e~>e~>e~>t),
	_t = (_, N),
	P = (_, NP),
	_e = (_,e),	_x = (_,e), 	_y = (_,e),
	Result = and @ (_t@_e) @ (P @ abst(_y, SubTerm)),
	ttExp_to_ttTerm_info( abst(P, abst(_t, Result)), (Term, Type), Lemma).

% NN : pp~>pp~>n
assign_term(_, Lemma, 'NN', _, Cat, Type, Term) :- 
	(	(Cat, Type) = (pp~>pp~>n, N~>N~>N)
	), !,
	_p = (_, N),	_q = (_, N),
	Result = and @ (and @ _p @ _q) @ (Lemma, N), 
	ttExp_to_ttTerm_info( abst(_p, abst(_q, Result)), (Term, Type), Lemma).

% NN(s) : (np~>s:to)~>n
assign_term(_, Lemma, POS, _, Cat, Type, Term) :- 
	(Cat, Type) = ((np~>s:to)~>n, VP~>N),
	(POS = 'NN';
	 POS = 'NNS'),
	!,
	V = (_, VP),	_p = (_, N),
	_e = (_, e), _x = (_, e),
	Result = and @ ((Lemma, N)@_x) @ (V @ abst(_p,_p@'*') @ abst(_e, of@_e@_x)), 
	ttExp_to_ttTerm_info( abst(V, abst(_x, Result)), (Term, Type), Lemma).

% WDT, WP, IN : (np~>s:dcl)~>n~>n
assign_term(_, Lemma, POS, _, Cat, Type, Term) :-
	(Cat, Type) = ((np~>s:dcl)~>n~>n, VP~>N~>N), 
	(	POS = 'WDT';
		POS = 'WP';
		POS = 'IN'
	), !,
	_x = (_, e),
	_p = (_, N),	_q = (_, N),
	V = (_, VP),
	Result = and @ _p @ abst(_x, V @ abst(_q, _q@_x) @ 'Univ'), 
	ttExp_to_ttTerm_info( abst(V, abst(_p, Result)), (Term, Type), Lemma).

% If, When, although:IN
assign_term(_, Lemma, POS, _, Cat, Type, Term) :- 
	(	(POS, Cat, Type) = ('IN', s:dcl~>s:dcl~>s:dcl, T~>T~>T);
		(POS, Cat, Type) = ('WRB', s:dcl~>s:dcl~>s:dcl, T~>T~>T) 
	), !,
	S1 = (_, T),
	S2 = (_, T),
	_x = (_, e),	_y = (_, e), _e = (_, e),
	_q = (_, e~>t),
	Result = Lemma @ (S1 @ abst(_x, part_of@_x@_e)) @ (S2 @ abst(_y, part_of@_y@_e)),
	ttExp_to_ttTerm_info( abst(S1, abst(S2, abst(_q, and @ Result @ (_q @ _e)))), (Term, Type), Lemma).

% while, by :IN  VP->VP->VP
assign_term(_, Lemma, POS, _, Cat, Type, Term) :- 
	(	(POS, Cat, Type) = ('IN', (np~>s:ng)~>(np~>s:dcl)~>(np~>s:dcl), VP~>VP~>NP~>N~>t)
	), !,
	V1 = (_, VP),
	V2 = (_, VP),
	_e1 = (_, e),	_e2 = (_, e), _e3 = (_, e),
	_t = (_, N),
	P = (_, NP),
	Conj1 = and @ (and @ (V1@P@(is@_e1)) @ (V2@P@(is@_e2))) @ (Lemma@_e1@_e2),
	Conj2 = and @ (and @ (part_of@_e3@_e1) @ (part_of@_e3@_e2)) @ (_t@_e3),
	ttExp_to_ttTerm_info( abst(V1, abst(V2, abst(_t, and @ Conj1 @ Conj2))), (Term, Type), Lemma).

% verbs: 
assign_term(Token, Lemma, POS, Feats, Cat, Type, Term) :-
	(	atom_chars(POS, ['V', 'B' | _]);
		POS = 'MD';
		POS = 'NN'  % e.g. date
	), !,    		
	verb_term(Token, Lemma, POS, Feats, Cat, Type, Term).
	%Term = Lemma.

% default: term = lemma
assign_term(Token, Lemma, POS, (Feat1,Feat2), Cat, _, _) :-
	term_to_atom(Cat, Atom_Cat),
	atomic_list_concat([Token, Lemma, POS, Feat1, Feat2, Atom_Cat], ', ', Message),
	write('Unable to process: '), write(Message), write('\n'),
	fail.
	%Term = Lemma.




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% detects the type of verb by its category
verb_term(_, Lemma, _, _, _, Type, Term) :-
	Type = ((e~>t)~>t) ~> ((e~>t)~>t), 
	P = (_, (e~>t)~>t),
	_e = (_, e),	% event into
	_x = (_, e),
	_p = (_, e~>t),
	T = (Lemma, e~>e~>t) @ _x @ _e, 
	ttExp_to_ttTerm_info( abst(P, abst(_p, and @ (_p @ _e) @ (P @ abst(_x, T)))), (Term, Type), Lemma ),
	!.
	
verb_term(_, Lemma, _, _, _, Type, Term) :-
	Type = ((e~>t)~>t) ~> ((e~>t)~>t) ~> ((e~>t)~>t), 
	P = (_, (e~>t)~>t),
	Q = (_, (e~>t)~>t),
	_x = (_, e),
	_y = (_, e),
	_e = (_, e),
	_p = (_, e~>t),
	Subj_S = abst(_y, P @ abst(_x, (Lemma, e~>e~>e~>t) @ _x @ _y @ _e)),
	ttExp_to_ttTerm_info( abst(P, abst(Q, abst(_p, and @ (_p @ _e) @ (Q @ Subj_S)))), (Term, Type), Lemma ),
    %Obj_S = abst(_x, Q @ abst(_y, (Lemma, e~>e~>e~>t) @ _x @ _y @ _e) ),
    %ttExp_to_ttTerm_info( abst(P, abst(Q, abst(_p, and @ (_p @ _e) @ (P @ Obj_S)))), (Term, Type), Lemma ).
	!.

verb_term(_, Lemma, _, _, Cat, Type, Term) :-
	(Cat = (np~>s:to)~>np~>s:dcl;
	 Cat = (np~>s:b)~>np~>s:dcl),
	Type = VP~>TR~>TR, 
	V = (_, VP),
	P = (_, TR),
	_e = (_, e),	% event
	_x = (_, e),	_y = (_,e),
	_p = (_, e~>t),
	Event_mod = abst(_y, P @ abst(_x, (Lemma,e~>e~>e~>t)@_y@_x@_e)), 
	ttExp_to_ttTerm_info( abst(V, abst(P, abst(_p, and @ (V@P@Event_mod) @ (_p@_e)))), (Term, Type), Lemma ),
	!.

verb_term(_, Lemma, _, _, Cat, Type, Term) :-
	(Cat = pp~>np~>s:dcl;
	 Cat = pp~>np~>s:pss;
	 Cat = pp~>np~>s:pt;
	 Cat = pp~>np~>s:b; % VB
	 Cat = pp~>np~>s:ng),	
	Type = PP~>NP~>_, 
	_q = (_, PP), _t = (_, PP),
	P = (_, NP),
	_x = (_, e), 	_e = (_, e),
	Result = and @ ((and@_q@_t) @ _e) @ (P @ abst(_x, (Lemma,e~>e~>t)@_x@_e)),
	ttExp_to_ttTerm_info( abst(_q, abst(P, abst(_t, Result))) , (Term, Type), Lemma ),
	!.

verb_term(_, Lemma, _, _, Cat, Type, Term) :-
	(Cat = np~>pp~>np~>s:dcl;
	 Cat = np~>pp~>np~>s:b),
	Type = NP~>PP~>_,  
	P = (_, NP),	Q = (_, NP),
	_x = (_, e),	_y = (_, e),
	_e = (_, e),
	_p = (_, PP), _q = (_, PP),
	Result = and @ ((and@_q@_p)@_e) @ (Q @ abst(_y, P @ abst(_x, (Lemma, e~>e~>e~>t) @ _x @ _y @ _e))),
	ttExp_to_ttTerm_info( abst(P, abst(_p, abst(Q, abst(_q, Result)))), (Term, Type), Lemma ),
	% missing second reading
	!.

verb_term(_, Lemma, _, _, Cat, Type, Term) :-
	(Cat = (np~>s:to)~>np~>s:pss),
	Type = VP~>TR~>TR, 
	V = (_, VP),
	P = (_, TR),
	_e1 = (_, e),	_e2 = (_,e), % event
	_x = (_, e),	
	_p = (_, e~>t),
	Result = and @ (_p@_e2) @ (and @ (V@P@(is@_e1)) @ (P@abst(_x, (Lemma,e~>e~>e~>e~>t)@_e1@_x@'*'@_e2))), 
	ttExp_to_ttTerm_info( abst(V, abst(P, abst(_p, Result))), (Term, Type), Lemma ),
	!.

verb_term(Token, Lemma, POS, (Feat1, Feat2), Cat, _, _) :-
	term_to_atom(Cat, Atom_Cat),
	atomic_list_concat([Token, Lemma, POS, Feat1, Feat2, Atom_Cat], ', ', Message),
	write('Unable to process: '), write(Message), write('\n'),
	fail.	


