%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module('ccgTerm_to_llf',
	[
		ccgTerm_to_llf/2
	]).

:- use_module('../knowledge/ling', [decompose_everyone/3, lemma_of_poss_pr/2]).
:- use_module('../latex/latex_ttterm', [latex_ttTerm_print_tree/3]).
:- use_module('../printer/reporting', [report/1]).
:- use_module('ttterm_to_term', [ttTerm_to_prettyTerm/2]).
:- use_module('ttterm_preds', [add_heads/2, set_type_for_tt/3]).
:- use_module('../lambda/lambda_tt', [op(605, yfx, @), op(605, xfy, ~>)]).
:- use_module('../lambda/type_hierarchy', [cat_eq/2]).

:- dynamic debMode/1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% beginings of ccgTree to LLF convertion
ccgTerm_to_llf(Term, LLF) :-
	%add_heads(Term, Term_H), % binds category features
	once(clean(Term, LLF)).
	%add_heads(LLF, LLF_H).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Cleans CCG_term by applying clean_list
clean(X,_) :-	var(X), writeln('Variable accounted'), !, fail.

clean((X,Ty), (X,Ty)) :-
	var(X), !.

clean(A, B) :-
	once(clean_list(A, C)),
	clean(C, B).

clean((A@B,Ty), (A1@B1,Ty)) :-
	clean(A, A1),
	clean(B, B1).

clean((abst(A,B),Ty), (abst(A1,B1),Ty)) :-
	clean(A, A1),
	clean(B, B1).

clean(((A,Ty1),Ty2), ((A1,Ty1),Ty2)) :-
	clean((A,Ty1), (A1,Ty1)).

clean(A, A).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
clean_list(A, B) :-
	%extract_samples(A, A);
	% lex_rule (A conj B) -> conj (lex_rule A) (lex_rule B)
	put_lex_rule_under_conj(A, B); % takes scope over others
	% plural the to s-morpheme
	the_nns_to_s_nns(A, B);
	% plural some to several
	some_nns_to_afew_nns(A, B);
	% two of NNS ---> two NNS
	numOfNNS_to_numNNS(A, B);
	% cat1=n, cat2=np, cat(Quant:JJ)=n~>n to (Quant, n~>np) @ n
	nn_to_n_np(A, B);
	%tlp NNP of cat1=n, cat2=np convert to tlp of cat=np
	nnp_n_np_to_np(A, B);
	%tlp NN of cat1=n, cat2=np convert to tlp of cat=np
	nn_n_np_to_np(A, B);
	%tlp NNS of cat1=n, cat2=np convert to tlp of cat=np
	nns_n_np_to_np(A, B);
	%tt of cat1=n, cat2=np convert to tt of cat=np
	n_np_to_np(A, B);
	np_pss_to_n_n(A, B);
	% climbing,VBG,n --> a/the climbing, np
	vb_n_np_to_np(A, B);
	% (owning X) (every man) --> who (owning X) (every man)
	lex_rule_np_s_to_np_np(A, B);
	%nnp_conj_n_np_to_np(A, B); % canceled by put_lex_rule_under_conj
	put_mod_inside_who(A, B);
	comma_to_and(A, B);
	attach_remote_DT_to_noun(A, B);
	n_mod_everyone(A, B);
	some_one(A, B); %sick-2405, 6146, 3258
	some_sleeping_one(A, B); %sick-2404
	% no@(one@typing)
	no_noun_typing(A, B); %sick-3439,2937
	% relative clause should modify noun not np
	put_rel_cl_under_det(A, B);
	% attach particle to verb
	attach_pr_to_verb(A, B);
	% put pp modifier under det and attached to noun
	put_ppMod_under_det(A, B);
	% inserts which:vp,np,np as np modifier (for wrong analyses mainly)
	np_which_mod(A, B);
	% all the dogs ---> all dogs
	pdt_rm_dt_noun(A, B);
	% poss_pr to pos@pr
	poss_pr_to_s_pr(A, B);
	% not (all dogs) ---> not all dogs
	not_all_NN(A, B);
	% not everybody ---> not every person
	not_everybody(A, B);
	% brown big a dog -> a brown big dog (NL: alpino)
	% mods_det_noun(A, B);
	%nn_n(A, B);
	%it_is_np(A, B);
	%it_is_mod(A, B);
	fail.


extract_samples(A, _) :-
	A = ((tlp(_,'by',_,_,_), _~>(np:_~>s:pss)~>_,_) @ (B, np:_, _), (np:_~>s:pss)~>_, _),
	ttTerm_to_prettyTerm((B, np:_), Pr),
	report([Pr]),
	fail.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% pull sinked determiner and put at the top
% brown big a dog -> a brown big dog (NL: alpino)
% mods_det_noun( ((ModTLP,np:_~>np:_,HMod) @ NP, np:_, _), New) :-
% 	ModTLP

tlp_pos_in_list(TLP, List) :-
	nonvar(TLP),
	TLP = tlp(_,_,POS,_,_),
	memberchk(POS, List).

tlp_pos_with_prefixes(TLP, Prefixes) :-
	nonvar(TLP),
	TLP = tlp(_,_,POS,_,_),
	findall(PF, (
		member(PF, Prefixes),
		atom_concat(PF, _, POS)
	), [_|_]).

is_tlp(TLP) :-
	nonvar(TLP),
	TLP =.. [tlp|_].

get_det_tlp(L, D) :-
	( debMode('the') ->
  	  D = tlp('the','the','DT','I-NP','Ins')
	; D = tlp(L,L,'DT','I-NP','Ins') ).

fix_report(Message) :-
	( is_list(Message) -> M = Message; M = [Message] ),
	( debMode('fix') -> report(M); true ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% attach a particle modifying verbphrase to a verb
% sick-192: up@stand -> stand_up, is this necessary after MWE look up in WN is done?
attach_pr_to_verb(
 	((tlp(TP,LP,'RP',_,_),(np:_~>s:_)~>np:_~>s:_) @ VP, _),
	( ((tlp(T,L,POS,F1,F2),V_Ty) @ Rest), VP_Ty )
) :-
	VP = ((tlp(TV,LV,POS,F1,F2),V_Ty) @ Rest, VP_Ty),
	atom_chars(POS, ['V','B'|_]),
	atomic_list_concat([TV, '_', TP], T),
	atomic_list_concat([LV, '_', LP], L).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% lex_rule (A conj B) -> conj (lex_rule A) (lex_rule B)
% is this necessary for vp->n,n lex rule? results in insertion of several "which"
put_lex_rule_under_conj(
	((((TLP_Conj,A~>A~>A) @ (T1,A), A~>A) @ (T2,A), A), B),
	((((TLP_Conj,B~>B~>B) @ S1, B~>B) @ S2, B), B)
) :- %!!! %+++
	is_tlp(TLP_Conj),
	set_type_for_tt(T1, B, S1),
	set_type_for_tt(T2, B, S2),
	fix_report('!!! Fix: put_lex_rule_under_conj').


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% e.g. who sleep ((most man, n), np)  ---> ((most (who man sleep, n), n), np)
% fracas-58,74 eccg
put_rel_cl_under_det(
	( (W@VP,np:_~>np:_) @ ((M@N,n:F1),np:F2), np:_),
	( (M @ ((W1@VP, n:_~>n:_) @ N, n:_), n:F1), np:F2 )
) :- %+++
	W = (WH_TLP, WTy~>_), % why not any modifier?
	tlp_pos_in_list(WH_TLP, ['WDT', 'WP']),
	VP = (_,np:_~>s:_),
	W1 = (WH_TLP, WTy~>n:_~>n:_),
	fix_report('!!! Fix: put_rel_cl_under det or modN').
	% if M is DEt then put_mod_under_det will fix this issue

% e.g. who (a woman) sleeps ---> a (who woman sleep)
% sick-2722, f %!!! a group of people dancing
put_rel_cl_under_det(
	( ((WH_TLP,VpTy~>np:_~>np:_) @ VP, np:_~>np:_) @ (Q@N,np:_), np:F2),
	( Q @ (((WH_TLP,VpTy~>n:_~>n:_) @ VP, n:_~>n:_) @ N, n:_), np:F2 )
) :- %+++
	tlp_pos_in_list(WH_TLP, ['WDT', 'WP']), % why not any modifier? instead of _~>np~>np
	Q = (tlp(_,_,'DT',_,_), n:_~>np:_),  % why lexical item only? why not any n~->np?
	fix_report('!!! Fix: put_rel_cl_under_det').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% e.g. (of:np,np,np) (s friend) (a group) ---> a ((of:np,n,n) (s friends) group)
% sick-140 eccg
put_ppMod_under_det(
	( ((Of,np:Z~>np:_~>np:_)@NP1,np:_~>np:_) @ NP2, np:_ ),
	( Det @ (((Of,np:Z~>n:X~>n:Y)@NP1, n:X~>n:Y) @ N, n:Y), np:U)
) :- %+++
	clean(NP2, (Det@N, np:U)),
	Det = (_,n:_~>np:_),
	tlp_pos_in_list(Of, ['IN']),
	fix_report('!!! Fix: put_ppMod_under_det').


%%%%%%%%%%%%%%%%%%% lex rule N->NP %%%%%%%%%%%%%%%%%%%%%%%%%
% e.g. Oracle,NNP,n -> np -----> Oracle,NNP,np
% something, everybody, 'DT'
% Jews, Americans, States, Airlines, 'NNPS'
% it,PRP; then,RB; more,JJR  n -> np --------> X,PRP,np
nnp_n_np_to_np(
	( (TLP, n:_), np:X ),
	( TLP, np:X )
) :- % +++
	tlp_pos_in_list(TLP, ['NNP','DT','NNPS','PRP','RB','JJR']),
	fix_report('!!! Fix: proper names as np').

% (south:n~>n @ Europe:NNP:n):np to (the @ (south:n~>n @ Europe:NNP:n)):np
% south Europe ~~> the south Europe, fracas-44
nnp_n_np_to_np(
	( (N, n:X), np:_),
	( The @ (N, n:X), np:_)
) :- % +++
	add_heads((N, n:X), (_,_,Head)),
	tlp_pos_in_list(Head, ['NNP']),
	The = (tlp('the','the','DT','I-NP','Ins'), n:_~>np:_),
	fix_report('!!! Fix: modified proper names as np').


%%%%%%%%%%%%%%%%%%% lex rule N->NP for verbs %%%%%%%%%%%%%%%%%%%%%%%%%
% e.g. seasoning,VBG,n, climbing:VBG,n, rule directly for compunds
vb_n_np_to_np(
	( (T,n:Y), np:X ),
	( (D, n:_~>np:X) @ (T,n:Y), np:X )
) :-
	add_heads((T,n:Y), (_,_,Head)),
	tlp_pos_with_prefixes(Head, ['VB']), % often VBG
	%(Cat = n:_; Cat = pp~>n:_), %why constraining category?
	get_det_tlp('a', D),
	fix_report('!!! Fix: insert DT for n:VB* complex term').


%%%%%%%%%%%%%%%%% lex rule N->NP %%%%%%%%%%%%%%%%%%%%%%%%%%%
% n with NN heads to np
% e.g. oil,NN,n -> np -----> a@oil,DT,np
% why compunds and constants are seprated? why not to treat them with the same rule?
nn_n_np_to_np(
	( (N, n:X), np:Y),
	( (D, n:_~>np:Y) @ (N,n:X), np:Y )
) :- % +++
	tlp_pos_in_list(N, ['NN']),
	get_det_tlp('a', D),
	fix_report('!!! Fix: insert DT for n:NN constant').

/*nn_n_np_to_np( (X, np:F, _),  (New_X, np:F, H) ) :- % version 2, all matching nouns are constants
	X = (tlp(Tk,Lm,'NN',F1,F2), n:_, _),
	New_X = tlp(Tk,Lm,'NN',F1,F2),
	H = tlp(np:F,Lm,'NN',F1,F2).
	*/

% e.g. crude@oil,NN,n ------> a@(cruid@oil),DT,np
% e.g. oil,NN,pp~>n for april delivery ----> a@(oil@for_april_delivery)
nn_n_np_to_np(
	( (N, n:X), np:Y ),
	( (D,n:_~>np:_) @ (N,n:X), np:Y)
) :-  % +++
	add_heads((N,n:X), (_,_,Head)),
	nonvar(Head),
	Head = tlp(Cat,_,'NN',_,_),
	(Cat = n:_; Cat = pp~>n:_), %why constraining category?
	get_det_tlp('a', D),
	fix_report('!!! Fix: insert DT for n:NN complex term').


%%%%%%%%%%%%%%%%%%% lex rule N->NP %%%%%%%%%%%%%%%%%%%%%%%%%
% n with NNS heads to np, NNS is changed in NN by simply/2 predicate
% e.g. dogs,NNS,n -> np -----> s@dogs,PL,np
nns_n_np_to_np(
	( (NNS,n:X), np:Y ),
	( (D,n:_~>np:_) @ (NNS,n:X), np:Y )
) :- % +++
	tlp_pos_in_list(NNS, ['NNS']),
	get_det_tlp('s', D),
	fix_report('!!! Fix: insert DT for n:NNS constant').

% e.g. hungry@dogs,NNS,n -> np -----> s@(hungry@dogs),PL,np
% e.g. apples,NNS,pp~>n for april delivery ----> s@(apples@for_april_delivery)
nns_n_np_to_np(
	( (NNS,n:X), np:Y ),
	( (D,n:_~>np:_) @ (NNS,n:X), np:Y )
) :- % +++
	add_heads((NNS,n:X), (_,_,Head)),
	nonvar(Head),
	Head = tlp(Cat,_,'NNS',_,_),
	( Cat = n:_; Cat = pp~>n:_ ), %why constraining the category?
	get_det_tlp('s', D),
	fix_report('!!! Fix: insert DT for n:NNS complex term').

%%%%%%%%%%%%%%%%%%% lex rule N->NP %%%%%%%%%%%%%%%%%%%%%%%%%
% type change from n to np
% e.g. $@37,CD,n:num -> np -----> $@37,CD,np
n_np_to_np(
	( (CD,n:num), np:_ ),
	( CD, np:Feat )
) :-
	is_tlp(CD),
	CD = tlp(_,_,'CD',_,F),
	( atom_chars(F, [_,_,'D','A','T']) ->
 	  Feat = 'dat'
	; Feat = 'num' ),
	fix_report('!!! Fix: make CD,n:num of category np').

% a girl in (white, n, np)
n_np_to_np(
	( (JJ,n:X), np:Y ),
	( (D,n:_~>np:_) @ (JJ,n:X), np:Y )
) :-
	tlp_pos_in_list(JJ, ['JJ']),
	get_det_tlp('a', D),
	fix_report('!!! Fix: insert DT for n:JJ constants').

%%%%%%%%%%%%%%%%% lex rule N->NP & VP->N,N %%%%%%%%%%%%%%%%%%%%%%%%%%%
% ((((M,np~>s),n~>n) @ Smith:n:NNP, n), np) --->  (which:(np~>s)~>np~>np @ M:np~>s) @ Smith:np
% Smith see X did Y, wrong analysis mainly, fracas-345
np_which_mod(
	( (((VP,np:X~>s:Y),n:_~>n:_) @ (N,n:_), n:_), np:_),
	((WH @ (VP,np:X~>s:Y), np:_~>np:_) @ (N,np:_), np:_)
) :- %+++
	is_tlp(N),  % constraint POS = NNP,NNPS,DT,PRP
	WH = (tlp('which','which','WDT','I-NP','Ins'), (np:_~>s:_)~>np:_~>np:_),
	fix_report('!!! Fix: insert Which:vp->np->np for modifying np').

%%%%%%%%%%%%%%%%%%% lex rule VP->N,N %%%%%%%%%%%%%%%%%%%%%%%%%
% X:np->s:pss/ng  -> n->n  ------>  which @ (is @ X)
% e.g. from@Canada@produced,np->s:pss -> n->n -----> which@(is@(from@Canada@produced))
np_pss_to_n_n(
	( (VP,np:X~>s:F), n:_~>n:_ ),
	( WH @ (VP,np:X~>s:F), n:_~>n:_ )
) :- %!!! how do you deal with the verb then? any rule fpr this? %+++
	memberchk(F, [ng, adj, pss, dcl]), % adj: full of X:np~>s:sdj--->n~>n, relax constrain with no checking?
	WH = (tlp('which','which','WDT','I-NP','Ins'), (np:_~>s:_)~>n:_~>n:_),
	fix_report(['!!! Fix: insert Which Is for lex_rule. Feature = ', F]).

% for ((owning cars) (evevry man)) -> ( who (owning cars) (evevry man))
lex_rule_np_s_to_np_np(
	( ((VP,np:A~>s:B), np:C~>np:D) @ QNP, np:E),
	( (WH @ (VP,np:A~>s:B), np:C~>np:D) @ QNP, np:E )
) :- %+++
	% define NP modifier "who", we dont use "is"
	WH = (tlp('which','which','WDT','I-NP','Ins'), (np:A~>s:B)~>np:C~>np:_),
	fix_report('!!! Fix: insert Which Is for lex_rule: vp->np->np').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% attach the modifier to the head of rlative clause or passive clause
% (X, n~>n) @ [(who @ Z, n~>n) @ (Y,n)] ~~~> (who @ Z, n~>n) @ [(X, n~>n) @ (Y,n)]
% (X, n~>n) @ [((VPpass:np~>s), n~>n) @ (Y,n)] ~~~>((VPpass:np~>s), n~>n) @ [(X, n~>n) @ (Y,n)]  %sick-2712, 7649
put_mod_inside_who(
	( Mod @ (WHC @ TTn, n:_), n:_ ),
	( WHC @ (Mod @ TTn, N), N )
) :- %+++
	nonvar(WHC),
	( WHC = ((tlp(_,'who',_,_,_),_) @ _VP, n:_~>n:_)
	; WHC = ((_, np:_~>s:_), n:_~>n:_)
	),
	Mod = (TTexp, _~>N),
	TTexp \= (_,_,_), % "posed slept man" will loop in commutation modifiers, sick-964
	fix_report('!!! Fix: put_mod_inside_who').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% change type n~>n to n~>np for JJ(S) words like many, several, most, few, etc
nn_to_n_np(
	( ((Q,n:X~>n:_) @ N, n:_), np:Y ),
	( (tlp(Tk,L,P1,F1,F2),n:X~>np:Y) @ N, np:Y )
) :- %+++
	is_tlp(Q),
	Q = tlp(Tk,L,P,F1,F2),
	( memberchk(L, ['several', 'many', 'few', 'most']) -> P1 = 'DT'
	; P = 'CD', P1 = P ),
	%!!! Check that this takes ito account plural cases too: several dogs
	fix_report('!!! Fix: identify modifiers as quantifiers').

% exactly,(n~>n)~>n~>n @ two,n~>n @ N,n : np ~~> exactly,(n~>np)~>n~>np @ two,n~>np @ N,n - fracas-85
nn_to_n_np(
	( (((RB,_) @ (CD,n:_~>n:_), n:X~>n:_) @ N, n:_), np:Y ),
	( ((RB, Ty~>Ty) @ (CD, Ty), Ty) @ N, np:Y )
) :- %+++
	tlp_pos_in_list(RB, ['RB']),
	tlp_pos_in_list(CD, ['CD']),
	Ty = n:X~>np:Y,
	fix_report('!!! Fix: change type to correct one').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Change plural-some to several
some_nns_to_afew_nns(
	( (Some,n:F1~>np:F2) @ TTn, np:F3 ),
	( (Afew,n:F1~>np:F2) @ TTn, np:F3 )
) :-
	is_tlp(Some),
	Some = tlp(_,'some','DT',_,_),
	add_heads(TTn, (_,_,Head)),
	tlp_pos_in_list(Head, ['NNS']),
	Afew = tlp('a_few','a_few','DT','0','Ins').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Change plural-the to s-morpehem
the_nns_to_s_nns(
	( (The,n:X~>np:Y) @ TTn, np:Z ),
	( (Det,n:X~>np:Y) @ TTn, np:Z )
) :-
	\+debMode('the'),
	is_tlp(The),
	The = tlp(_,'the','DT',_,_), % different from several, some
	add_heads(TTn, (_,_,Head)),
	tlp_pos_in_list(Head, ['NNS']),
	Det = tlp('s','s','DT','0','Ins').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% change conjunctive comma to and
comma_to_and(
	( tlp(',', ',', ',',F1,F2), Ty~>Ty~>Ty ),
	( tlp('and','and','CC',F1,F2), Ty~>Ty~>Ty )
) :-
	fix_report('!!! Fix: comma replaced by and').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% attach remote DT to the head of NP
% e.g. The [people who were at the meeting] [All] laughed
attach_remote_DT_to_noun(
	( ((DT,(np:_~>s:dcl)~>np:_~>s:dcl) @ VP, np:_~>s:dcl) @ NP, s:dcl ),
	( VP @ ((DT,DTy) @ TT_n, np:F3), STy )
) :-
	tlp_pos_in_list(DT, ['DT']),
	( NP = ( (tlp(_,'the','DT',_,_),DTy) @ TT_n, np:F3 ) %frac-93
	; NP = ( TT_n, np:F3 ), DTy = n:_~>np:F3, TT_n = (_, n:_) %%frac-99
	),
	VP = (_, np:_~>STy),
	fix_report('!!! Fix: attach remote DT to noun').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ((n->n @ everyone, n), np) ---> (every, n->np) @ (n->n @ person)
n_mod_everyone(
	( (Mod @ (tlp(_,L,'DT',_,_),n:_), n:_), np:F1 ),
	( (Quant,n:F2~>np:F1) @ (Mod @ (Noun,n:F2), n:F2), np:F1)
) :-
	nonvar(L),
	decompose_everyone(L, Q, N),
	Quant = tlp(Q,Q,'DT','Ins','Ins'),
	Noun = tlp(N,N,'NN','Ins','Ins'),
	fix_report('!!! Fix: decompose GQ').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% someone,np -> some:n->np @ person:n
some_one(
	( tlp(_,L,'DT',_Feat1,_),np:F1 ),
	( (Quant,n:F2~>np:F1) @ (Noun,n:F2), np:F1 )
) :-
	nonvar(L),
	decompose_everyone(L, Q, N),
	Quant = tlp(Q,Q,'DT','Ins','Ins'),
	Noun = tlp(N,N,'NN','Ins','Ins'),
	fix_report('!!! Fix: decompose GQ').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% no,n~>np (sleeping:n~>n one:n) -> no,n~>np (sleeping:n~>n person:n)
some_sleeping_one(
	( (Q,n:X~>np:Y) @ (Nmod @ (One,n:F), n:X), np:Z ),
	( (Q,n:X~>np:Y) @ (Nmod @ Person, n:X), np:Z )
) :-
	is_tlp(Q), Q = tlp(_,'no',_,_,_),
	is_tlp(One), One = tlp(_,'one','NN',_,_),
	Person = (tlp('person','person','NN','Ins','Ins'), n:F),
	fix_report('!!! Fix: GQ with verb').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% no,n~>np (one:n~>n typing:n) -> no,n~>np (typing:n~>n person:n) sick-3353, 3439
no_noun_typing(
	( (Q,n:X~>np:Y) @ ((N,n:_~>n:_) @ (V,n:_), n:F), np:Z ),
	( (Q,n:X~>np:Y) @ ( (Verb,n:F~>n:F) @ (N,n:F), n:F), np:Z )
) :-
	is_tlp(Q), Q = tlp(_,'no',_,_,_),
	tlp_pos_in_list(N, ['NNS', 'NN']),
	is_tlp(V), V = tlp(TV,LV,_,_,_), %!!! multiword noun and vping?
	atom_concat(_, 'ing', TV),
	Verb = tlp(TV,LV,'VBG','Ins','Ins'),
	fix_report('!!! Fix: Verb modifying noun').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [its, n,(np,s),s]  ---> [s, np,n,(np,s),s] @ [it, np]
% sick-5003
poss_pr_to_s_pr(
	( tlp(_,Lm,'PRP$',_,_), Type ),
	( (S,np:X~>Type) @ (It,np:X), Type )
) :-
	Type = n:_~>np:_, % type before type raising
	nonvar(Lm),
	lemma_of_poss_pr(Lm, Lm_pr),
	It = tlp(Lm_pr,Lm_pr,'PRP','Ins','Ins'),
	S = tlp('\'s','\'s','POS','Ins','Ins').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% N of [the] dogs,np ---> N dogs
% fracas-46
numOfNNS_to_numNNS(
	( (Num,_) @ ((tlp(_,'of',_,_,_),_:_~>pp) @ NP, pp), np:_),
	( (Num,n:_~>np:_) @ N, np:_ )
) :-
	NP = (Term, _), nonvar(Term),
	is_tlp(Num), Num = tlp(_,L,P,_,_), !,
	( P = 'CD' % fracas-46
	; member(L, ['none', 'all', 'each'])
	),
	once( ( NP = ((_,n:_~>np:_) @ N, np:_)
		  ; NP = (N, np:_), N = (_, n:_)
		  ; NP = (_, n:_),  N = NP ) ),
	fix_report('!!! Fix: 5 of Dogs -> 5 Dogs').

% None of [the] kids,n,np ---> None kids
%sick-122
numOfNNS_to_numNNS(
	( (((tlp(_,'of',_,_,_),_) @ NP, n:_~>n:_) @ (Num,_), n:_), np:_ ),
	( (Num,n:_~>np:_) @ N, np:_ )
) :-
	is_tlp(Num), Num = tlp(_,L,P,_,_),
	( P = 'CD' % fracas-46
	; member(L, ['none', 'all', 'each']) %sick-122
	),
	once( ( NP = ((_,n:_~>np:_) @ N, np:_)
		  ; NP = (N, np:_), N = (_, n:_)
		  ; NP = (_, n:_),  N = NP ) ),
	fix_report('!!! Fix: 5 of Dogs -> 5 Dogs').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% All:PDT:np~>np the:n~>np dogs:n ---> All dogs
%!!! should not be "not all", "not every"
% fracas-92
pdt_rm_dt_noun(
	( (tlp(T,L,'PDT',F1,F2),np:_~>np:_) @ ((DT,n:_~>np:_) @ N, np:_), np:_ ),
	( (tlp(T,L,'DT',F1,F2),n:_~>np:_) @ N, np:_)
) :-
	nonvar(L),
	tlp_pos_in_list(DT, ['DT']),
	fix_report('!!! Fix: attach pre determiner').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% not @ (all @ birds) -> not @ all @ birds
not_all_NN(
	( (NOT,_) @ ((ALL,n:_~>np:_) @ Noun, np:_), np:_ ),
	( ((NOT,Ty) @ (ALL,n:_~>np:_), n:_~>np:_) @ Noun, np:_ )
) :-
	tlp_pos_in_list(ALL, ['DT']), %urgent, fracas-134,
	% fracas-134, atomic list concat why removing this clause causes a problem?
	is_tlp(NOT), % pos = RB?
	Ty = (n:_~>np:_)~>n:_~>np:_,
	fix_report('!!! Fix: not (all dogs) -> (not all) dogs').

% not @ everybody -> not @ every @ person
not_everybody(
	( NOT @ (EB_TLP, np:_), np:_ ),
	NOT_EB
) :-
	is_tlp(EB_TLP),
	EB = (EB_TLP, np:_),
	once(clean(EB, EB1)),
	( EB \= EB1 ->
		once(clean((NOT@EB1, np:_), NOT_EB)),
		fix_report('!!! Fix: not everybody -> (not every) person')
	;	fail
	).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% make pp the most outter modifier of the head (pp is kinda intersective):
% e.g. (A,n~>n) @ ((N,pp~>n) @ (P,pp)) --~> (P',n~>n) @ ((A,n~>n) @ (N',n))
/*n_pp_to_pp_n( (TT1 @ TT2, n:F2, H), (, n:F2, H) ) :-
	move_pp_up(TT1, TT2)

move_pp_up( (Fun, n:F11~>n:F12, H1) @ (Arg, _, H2),  (Fun, n:F11~>n:F12, H1) @ (Arg1, Ty, H2)    ) :-
	!,
	move_pp_up( Arg, (Arg1,Ty), TTpp)

move_pp_up( (Noun, pp~>n:F1, H1) @ (PP, pp, H2),  TTnoun, TTpp ) :-
	!,
	set_type_for_tt( (Noun,pp~>n:F1), n:F1, TTnoun ),
	set_type_for_tt( (PP,pp), n:X~>n:X, TTpp ).
*/

/*
nn_n( (X1@X2, n),  (tlp('NN@N','NN@N',_,_,_), n)) :-
	X1 = (tlp(_,_,_,_,_),n:_~>n:_),
	X2 = (tlp(_,_,_,_,_),n),
	term_to_atom(X1, At1),
	term_to_atom(X2, At2),
	write(At1),
	write('\t\t'),
	writeln(At2).
*/


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
it_is_mod( A, B) :-
	A = ((_A1, T1~>T2) @ (A2, T1), T2),
	cat_eq(T1, T2),
	B = (A2, T2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
it_is_np( (X, np), (tlp(String,String,_,_,_),np) ) :-
	X \= tlp(_,_,_,_,_),
	tc_to_string((X,np), String).
	%writeln(String)
	%latex_file_stream(S),
	%latex_ttTerm_print_tree(S, 6, (X, np))

% TC to String
tc_to_string(X,_) :- var(X), writeln('Variable accounted'), !, fail.

tc_to_string( (X,_), Str ) :-
	var(X), !,
	term_to_atom(X, StrX),
	atom_chars(StrX, [_, _ | Index_List]),
	X_Index_List = ['X' | Index_List],
	atom_chars(Str, X_Index_List).

tc_to_string( (A @ B, _), Str ) :-
	tc_to_string(A, StrA),
	tc_to_string(B, StrB),
	atomic_list_concat([StrA, ' ', StrB], Str).

tc_to_string( (tlp(A,_,_,_,_),_), A ).

tc_to_string( (A,_), Str ) :-
	tc_to_string(A, Str).

tc_to_string( (abst(A, B),_), Str ) :-
	tc_to_string(A, StrA),
	tc_to_string(B, StrB),
	atomic_list_concat(['(', StrA, '.', StrB, ')'], Str).
