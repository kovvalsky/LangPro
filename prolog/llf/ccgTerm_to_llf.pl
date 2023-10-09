%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module('ccgTerm_to_llf',
	[
		ccgTerm_to_llf/2
	]).

:- use_module('../knowledge/ling', [decompose_everyone/3, lemma_of_poss_pr/2]).
:- use_module('../latex/latex_ttterm', [latex_ttTerm_print_tree/3]).
:- use_module('../printer/reporting', [report/1]).
:- use_module('ttterm_to_term', [ttTerm_to_prettyTerm/2]).
:- use_module('ttterm_preds', [
	add_heads/2, set_type_for_tt/3, apply_ttMods_to_ttArg/3,
	set_type_for_tt_of_type/4,
	right_branch_tt_search/4, is_tlp/1, tlp_pos_in_list/2, rel_clause_ttterm/1,
	tlp_lemma_in_list/2, tlp_pos_with_prefixes/2, red_rel_clause_ttterm/1,
	proper_modttTerm/1
	]).
:- use_module('../lambda/lambda_tt', [op(605, yfx, @), op(605, xfy, ~>), norm_tt/2
	]).
:- use_module('../lambda/type_hierarchy', [cat_eq/2, final_value_of_type/2]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% beginings of ccgTree to LLF convertion
ccgTerm_to_llf(Term, LLF) :-
	%add_heads(Term, Term_H), % binds category features
	once(clean(Term, LLF)).
	%add_heads(LLF, LLF_H).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Cleans CCG_term by applying term fixing procedures
clean(X,_) :-	var(X), writeln('Variable accounted'), !, fail.

clean((X,Ty), (X,Ty)) :-
	var(X), !.

clean(A, B) :-
	once(fix_term(A, C)),
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
% lex_rule (A conj B) -> conj (lex_rule A) (lex_rule B)
% is this necessary for vp->n,n lex rule? results in insertion of several "which"
% takes scope over others
fix_term(
	((((TLP_Conj,A~>A~>A) @ (T1,A), A~>A) @ (T2,A), A), B),
	((((TLP_Conj,B~>B~>B) @ S1, B~>B) @ S2, B), B)
) :- %!!! %+++
	is_tlp(TLP_Conj),
	set_type_for_tt(T1, B, S1),
	set_type_for_tt(T2, B, S2),
	fix_report('!!! Fix: put_lex_rule_under_conj').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% make PP S-modifier an argument of copula
% PP:s~>s @ (is:vp @ np) -> is:pp~>np~>s @ PP:pp @ np
% NL:npn-987p: in NP1 (is NP2) -> is (in NP1) NP2
fix_term(
	( ((PP,np:_~>s:_~>s:_) @ NP1, _) @ ((Be,np:Y~>s:X) @ NP2, _), s:Z ),
	( (((Be,pp~>np:Y~>s:X) @ ((PP,np:_~>pp) @ NP1, pp), np:Y~>s:X) @ NP2, s:Z) )
) :-
	tlp_pos_in_list(PP, ['IN']),
	% FIXME no constraint on BE
	fix_report('!!! Fix: pp_be_to_be_pp (NL)').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% make the determiner ordinary that takes np~>s:adj as an argument
% NL:npn-987h: no:vp[adj]~>np @ adult:vp[adj] -> no:n~>np @ adult:n
fix_term(
	( (Det,(np:_~>s:adj)~>np:Y) @ VP_adj, np:X ),
	( (Det,n:_~>np:Y) @ Noun, np:X )
) :-
	is_tlp(Det),
	set_type_for_tt(VP_adj, n:_, Noun),
	fix_report('!!! Fix: det_pred_adj (NL)').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% pull sinked determiner and put at the top of NP
% NL:Lassy: brown (big (a dog)) -> a (brown (big dog))
fix_term(
	( ModTT @ (NP,np:Y), np:_ ),
	( Det @ Mods_N, np:X )
) :-
	proper_modttTerm(ModTT),
	ModTT = (Mod, np:_~>np:_),
	% ModTT can be lexical, conjunction of TTs, or a TT with a modifier,...
	%once(( is_tlp(Mod); is_cc_ttTerm(ModTT) )),
	nonvar(Mod),
	right_branch_tt_search(Det, (NP,np:Y), Mods, Noun),
	Det = (DT,n:_~>np:X),
	tlp_pos_in_list(DT, ['DT','CD']), % JJ?
	maplist(set_type_for_tt_of_type(np:_~>np:_, n:_~>n:_), [ModTT|Mods], Mods1),
	apply_ttMods_to_ttArg(Mods1, Noun, Mods_N),
	fix_report('!!! Fix: mods_det_noun (NL)').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% introduce lex_rule for tlp(NN:np) and alter its np~>np modifiers accordingly
% SICK_NL-28: (en bolnd wegvliegend) haar:NN:np --> ((en b w) (haar:NN:n)):np
fix_term(
	( ModTT @ (NP,np:Y), np:X ),
	( Mods_N, np:X )
) :-
	proper_modttTerm(ModTT),
	ModTT = (Mod, np:_~>np:_), nonvar(Mod),
	right_branch_tt_search(M, (ModTT@(NP,np:Y),np:X), Ms, Noun),
	Noun = (TLP_NN, np:_),
	tlp_pos_in_list(TLP_NN, ['NN', 'NNS']),
	append(Ms, [M], Mods),
	maplist(set_type_for_tt_of_type(np:_~>np:_, n:_~>n:_), Mods, Mods1),
	apply_ttMods_to_ttArg(Mods1, (TLP_NN,n:_), Mods_N),
	fix_report('!!! Fix: insert n~>np rule for Mods@NN(S):np (NL)').

fix_term(
	( TLP_NN, np:X ),
	( (TLP_NN, n:_), np:X )
) :-
	tlp_pos_in_list(TLP_NN, ['NN', 'NNS']),
	fix_report('!!! Fix: insert n~>np rule for NN(S):np (NL)').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Remove unnecessary type-raising for "Det N and N" with meaning "Det N and Det N"
% (and abst(X,X@adult) abst(X,X@kid)) @ the --> and (the adult)(the kid)
% !!! if type-raising correctly done, dist_arg should do this job
fix_term(
	( (((CC,C~>C~>C) @ (abst(V1,NP1),Ty1),_) @ (abst(V2,NP2),Ty2),_) @ D, np:X ),
	( ((CC,T~>T~>T) @ D_NP1, T~>T) @ D_NP2, T )
) :-
	tlp_pos_in_list(CC, ['CC']),
	C = (n:_~>np:_)~>np:_,
	norm_tt( ((abst(V1,NP1),Ty1) @ D, np:X), D_NP1 ),
	norm_tt( ((abst(V2,NP2),Ty2) @ D, np:X), D_NP2 ),
	T = np:X,
	fix_report('!!! Fix: eta-reduction for Conj (NL)').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% recover [pss] feature in types from [pt] since Lassy has no info for such feature
% SICKNL:1333 (worden,vp[pt]~>vp[dcl]) ((door NP,vp[pt]~>vp[pt]) (gemeten,vp[pt])) ->
%             (worden,vp[pss]~>vp[dcl]) ((door NP,vp[pss]~>vp[pss]) (gemeten,vp[pss]))
fix_term(
	( (Worden,(np:X~>s:pt)~>TyVP) @ VP, TyVP ),
	( (Worden,(np:X~>s:pss)~>TyVP) @ VP_pss, TyVP )
) :-
	tlp_pos_in_list(Worden, ['RB','AUX']),
	tlp_lemma_in_list(Worden, ['worden','is','zijn','be']), % remove NL words?
	set_type_for_tt(VP, np:X~>s:pss, VP_pss),
	fix_report('!!! Fix: recover :pss feature (NL)').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% n arguments of passives or verbs will use lex_rule to become np
% and later will be processed by lex_rule elimination rule
% fix_term(
% 	( ((Worden,(np:X~>s:Y)~>n:_~>S) @ VP, _) @ (Noun,n:A), _ ),
% 	( ((Worden,(np:X~>s:Y)~>np:Z~>S) @ VP, np:Z~>S) @ ((Noun,n:A),np:Z), S )
% ) :-
% 	tlp_pos_in_list(Worden, ['RB','AUX']),
% 	tlp_lemma_in_list(Worden, ['worden','is','zijn','be']). % remove NL words?

fix_term(
	( VP @ (Noun,n:A), VP_Ty ),
	( VP1 @ ((Noun,n:A),np:Z), VP_Ty )
) :-
	final_value_of_type(VP_Ty, s:_),
	add_heads(VP, (_,_,Head)),
	% should there be a constraint that VP has only applications?
	( % SICKNL:3598 doet:n~>vp oefeningen:n -> doet:np~>vp ((oefeningen:n),np)
	  tlp_pos_with_prefixes(Head, ['VB'])
	; % SICKNL:2704 (worden,vp[pt]~>n~>s:dcl) VP_pt n ->
	  %             (worden,vp[pss]~>vp[dcl]) VP_pt ((n),np)
	  tlp_pos_in_list(Head, ['RB','AUX']),
	  tlp_lemma_in_list(Head, ['worden','is','zijn','be']) % remove NL words?
	),
	set_type_for_tt(VP, np:Z~>VP_Ty, VP1),
	fix_report('!!! Fix: insert n~>np rule for n args of VP (NL)').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% n argumnet of prepositions will use lex_rule to become np
% and will be later processed again by lex_rule elimination rule
% SICKNL:2704 ('IN',n~>vp~>vp) n --> ('IN',np~>vp~>vp) ((n),np)

% Note that this rule is applied to larger phrase with Head because, fixing earlier
% is better as other fixing rules (e.g., put pp modifier under det) depend on this
fix_term( % for n~>vp~>vp, n~>np~>np, n~>n~>n cases
	( ((IN,n:_~>ModTy) @ (Noun,n:X), _) @ Head, Ty ),
	( ((IN,np:Y~>ModTy) @ ((Noun,n:X),np:Y), ModTy) @ Head, Ty )
) :-
	tlp_pos_in_list(IN, ['IN']).

fix_term( % for n~>pp case
	( (IN,n:_~>Ty1) @ (Noun,n:X), Ty2 ),
	( (IN,np:Y~>Ty1) @ ((Noun,n:X),np:Y), Ty2 )
) :-
	tlp_pos_in_list(IN, ['IN']),
	fix_report('!!! Fix: insert n~>np rule for n args of PP (NL)').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% attach a VP-modifying particle to a verb
% sick-192: up@stand -> stand_up
% is this necessary after MWE look up in WN is done?
fix_term(
 	((tlp(TP,LP,'RP',_,_),(np:_~>s:_)~>np:_~>s:_) @ VP, _),
	( ((tlp(T,L,POS,F1,F2),V_Ty) @ Rest), VP_Ty )
) :-
	nonvar(TP),
	VP = ((tlp(TV,LV,POS,F1,F2),V_Ty) @ Rest, VP_Ty),
	atom_chars(POS, ['V','B'|_]),
	atomic_list_concat([TV, '_', TP], T),
	atomic_list_concat([LV, '_', LP], L),
	fix_report('!!! Fix: attach_pr_to_verb').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% relative clause should modify noun not np
% e.g. who sleep ((most man, n), np)  ---> ((most (who man sleep, n), n), np)
% fracas-58,74 eccg
fix_term(
	( (W@VP,np:_~>np:_) @ ((M@N,n:F1),np:F2), np:_),
	( (M @ ((W1@VP, n:_~>n:_) @ N, n:_), n:F1), np:F2 )
) :- %+++
	W = (WH_TLP, WTy~>_), % why not any modifier?
	tlp_pos_in_list(WH_TLP, ['WDT', 'WP']),
	VP = (_,np:_~>s:_),
	W1 = (WH_TLP, WTy~>n:_~>n:_),
	fix_report('!!! Fix: put_rel_cl_under det or modN').
	% if M is DEt then put_mod_under_det will fix this issue

% e.g. who sleeps (a woman) ---> a (who sleep woman)
% sick-2722, f %!!! a group of people dancing
fix_term(
	( ((WH_TLP,VpTy~>np:_~>np:_) @ VP, np:_~>np:_) @ (NP,np:X), np:F2),
	( Q @ (((WH_TLP,VpTy~>n:_~>n:_) @ VP, n:_~>n:_) @ N, n:_), np:F2 )
) :- %+++
	% why not any modifier? instead of _~>np~>np
	tlp_pos_in_list(WH_TLP, ['WDT','WP','PRP$','DT']), % NL:die:PRP$,DT
	clean((NP,np:X), (Q@N,np:X)), % sub-cleaning can reveal the quantifier
	Q = (Q_TLP, n:_~>np:_),  % why lexical item only? why not any n~->np?
	tlp_pos_in_list(Q_TLP, ['DT','CD']),
	fix_report('!!! Fix: put_rel_cl_under_det').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% attach the modifier to the head of relative clause or passive clause
% (X, n~>n) @ [(who @ Z, n~>n) @ (Y,n)] ~~~> (who @ Z, n~>n) @ [(X, n~>n) @ (Y,n)]
% (X, n~>n) @ [((VPpass:np~>s), n~>n) @ (Y,n)] ~~~>((VPpass:np~>s), n~>n) @ [(X, n~>n) @ (Y,n)]  %sick-2712, 7649
fix_term(
	( Mod @ (WHC @ TTn, n:X), n:Y ),
	( WHC @ (Mod @ TTn, n:Y), n:X )
) :- %+++
	( rel_clause_ttterm(WHC); red_rel_clause_ttterm(WHC) ),
	\+rel_clause_ttterm(Mod),
	\+red_rel_clause_ttterm(Mod),
	% "posed slept man" will loop in commutation modifiers, sick-964, sick-962
	fix_report('!!! Fix: apply_mod_before_wh_clause').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% put pp modifier under det and attached to noun
% e.g. (of:np,np,np) (s friend) (a group) ---> a ((of:np,n,n) (s friends) group)
% sick-140 eccg
fix_term(
	( ((Of,np:Z~>np:_~>np:_)@NP1,np:_~>np:_) @ NP2, np:_ ),
	( Det @ (((Of,np:Z~>n:X~>n:Y)@NP1, n:X~>n:Y) @ N, n:Y), np:U)
) :- %+++
	clean(NP2, (Det@N, np:U)),
	Det = (_,n:_~>np:_),
	tlp_pos_in_list(Of, ['IN']),
	fix_report('!!! Fix: put_ppMod_under_det').

%%%%%%%%%%%%%%%%%%% lex rule N->NP %%%%%%%%%%%%%%%%%%%%%%%%%
% tlp NNP of cat1=n, cat2=np convert to tlp of cat=np
% e.g. Oracle,NNP,n -> np -----> Oracle,NNP,np
% something, everybody, 'DT'
% Jews, Americans, States, Airlines, 'NNPS'
% it,PRP; then,RB; more,JJR  n -> np --------> X,PRP,np
fix_term(
	( (TLP, n:_), np:X ),
	( TLP, np:X )
) :- % +++
	tlp_pos_in_list(TLP, ['NNP','DT','NNPS','PRP','RB','JJR']),
	fix_report('!!! Fix: proper names as np').

% (south:n~>n @ Europe:NNP:n):np to (the @ (south:n~>n @ Europe:NNP:n)):np
% south Europe ~~> the south Europe, fracas-44
fix_term(
	( (N, n:X), np:_),
	( The @ (N, n:X), np:_)
) :- % +++
	add_heads((N, n:X), (_,_,Head)),
	tlp_pos_in_list(Head, ['NNP']),
	The = (tlp('the','the','DT','I-NP','Ins'), n:_~>np:_),
	fix_report('!!! Fix: modified proper names as np').

%%%%%%%%%%%%%%%%%%% lex rule N->NP for verbs %%%%%%%%%%%%%%%%%%%%%%%%%
% climbing,VBG,n --> a/the climbing, np
% e.g. seasoning,VBG,n, climbing:VBG,n, rule directly for compunds
fix_term(
	( (T,n:Y), np:X ),
	( (D, n:_~>np:X) @ (T,n:Y), np:X )
) :-
	add_heads((T,n:Y), (_,_,Head)),
	tlp_pos_with_prefixes(Head, ['VB']), % often VBG
	%(Cat = n:_; Cat = pp~>n:_), %why constraining category?
	get_det_tlp('a', D),
	fix_report('!!! Fix: insert DT for n:VB* complex term').


%%%%%%%%%%%%%%%%% lex rule N->NP %%%%%%%%%%%%%%%%%%%%%%%%%%%
% change type n~>n to n~>np for DT & JJ(S) words like many, several, most, few, etc
% cat1=n, cat2=np, cat(Quant:JJ)=n~>n to (Quant, n~>np) @ n
% SICKNL-88: ((no@(that...)@biker:n),np) --> (no:n~>np)@((that...)@biker:n)
fix_term(
	( ((Q,n:X~>n:_) @ N, n:_), np:Y ),
	( (tlp(Tk,L,P1,F1,F2),n:X~>np:Y) @ N, np:Y )
) :- %+++
	is_tlp(Q),
	Q = tlp(Tk,L,P,F1,F2),
	( memberchk(L, ['several', 'many', 'few', 'most']) -> P1 = 'DT'
	; memberchk(P, ['CD', 'DT']), P1 = P ),
	%!!! Check that this takes ito account plural cases too: several dogs
	fix_report('!!! Fix: identify modifiers as quantifiers').

% exactly,(n~>n)~>n~>n @ two,n~>n @ N,n : np ~~> exactly,(n~>np)~>n~>np @ two,n~>np @ N,n - fracas-85
fix_term(
	( (((RB,_) @ (CD,n:_~>n:_), n:X~>n:_) @ N, n:_), np:Y ),
	( ((RB, Ty~>Ty) @ (CD, Ty), Ty) @ N, np:Y )
) :- %+++
	tlp_pos_in_list(RB, ['RB']),
	tlp_pos_in_list(CD, ['CD']),
	Ty = n:X~>np:Y,
	fix_report('!!! Fix: change type to correct one').


%%%%%%%%%%%%%%%%% lex rule N->NP %%%%%%%%%%%%%%%%%%%%%%%%%%%
% tlp NN of cat1=n, cat2=np convert to tlp of cat=np
% n with NN heads to np
% e.g. oil,NN,n -> np -----> a@oil,DT,np
% why compunds and constants are seprated? why not to treat them with the same rule?
fix_term(
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
fix_term(
	( (N, n:X), np:Y ),
	( (D,n:_~>np:_) @ (N,n:X), np:Y)
) :-  % +++
	N \= (tlp(_,_,'CD',_,_),_) @ _,
	add_heads((N,n:X), (_,_,Head)),
	nonvar(Head),
	Head = tlp(Cat,_,'NN',_,_),
	(Cat = n:_; Cat = pp~>n:_), %why constraining category?
	get_det_tlp('a', D),
	fix_report('!!! Fix: insert DT for n:NN complex term').

%%%%%%%%%%%%%%%%%%% lex rule N->NP %%%%%%%%%%%%%%%%%%%%%%%%%
% tlp NNS of cat1=n, cat2=np convert to tlp of cat=np
% n with NNS heads to np, NNS is changed in NN by simply/2 predicate
% e.g. dogs,NNS,n -> np -----> s@dogs,PL,np
fix_term(
	( (NNS,n:X), np:Y ),
	( (D,n:_~>np:_) @ (NNS,n:X), np:Y )
) :- % +++
	tlp_pos_in_list(NNS, ['NNS']),
	get_det_tlp('s', D),
	fix_report('!!! Fix: insert DT for n:NNS constant').

% e.g. hungry@dogs,NNS,n -> np -----> s@(hungry@dogs),PL,np
% e.g. apples,NNS,pp~>n for april delivery ----> s@(apples@for_april_delivery)
fix_term(
	( (NNS,n:X), np:Y ),
	( (D,n:_~>np:_) @ (NNS,n:X), np:Y )
) :- % +++
	NNS \= (tlp(_,_,'CD',_,_),_) @ _,
	add_heads((NNS,n:X), (_,_,Head)),
	nonvar(Head),
	Head = tlp(Cat,_,'NNS',_,_),
	( Cat = n:_; Cat = pp~>n:_ ), %why constraining the category?
	get_det_tlp('s', D),
	fix_report('!!! Fix: insert DT for n:NNS complex term').

%%%%%%%%%%%%%%%%%%% lex rule N->NP %%%%%%%%%%%%%%%%%%%%%%%%%
% tt of cat1=n, cat2=np convert to tt of cat=np
% type change from n to np
% e.g. $@37,CD,n:num -> np -----> $@37,CD,np
fix_term(
	( (CD,n:_Num), np:_ ),
	( CD, np:Feat )
) :-
	is_tlp(CD),
	CD = tlp(_,_,'CD',_,F),
	( atom_chars(F, [_,_,'D','A','T']) ->
 	  Feat = 'dat'
	; Feat = 'num' ),
	fix_report('!!! Fix: make CD,n:num of category np').

% a girl in (white, n, np)
fix_term(
	( (JJ,n:X), np:Y ),
	( (D,n:_~>np:_) @ (JJ,n:X), np:Y )
) :-
	tlp_pos_in_list(JJ, ['JJ']),
	get_det_tlp('a', D),
	fix_report('!!! Fix: insert DT for n:JJ constants').

%%%%%%%%%%%%%%%%% lex rule N->NP & VP->N,N %%%%%%%%%%%%%%%%%%%%%%%%%%%
% inserts which:vp,np,np as np modifier (for wrong analyses mainly)
% ((((M,np~>s),n~>n) @ Smith:n:NNP, n), np) --->  (which:(np~>s)~>np~>np @ M:np~>s) @ Smith:np
% Smith see X did Y, wrong analysis mainly, fracas-345
fix_term(
	( (((VP,np:X~>s:Y),n:_~>n:_) @ (N,n:_), n:_), np:_),
	((WH @ (VP,np:X~>s:Y), np:_~>np:_) @ (N,np:_), np:_)
) :- %+++
	is_tlp(N),  % constraint POS = NNP,NNPS,DT,PRP
	WH = (tlp('which','which','WDT','I-NP','Ins'), (np:_~>s:_)~>np:_~>np:_),
	fix_report('!!! Fix: insert Which:vp->np->np for modifying np').

%%%%%%%%%%%%%%%%%%% lex rule VP->N,N %%%%%%%%%%%%%%%%%%%%%%%%%
% X:np->s:pss/ng  -> n->n  ------>  which @ (is @ X)
% e.g. from@Canada@produced,np->s:pss -> n->n -----> which@(is@(from@Canada@produced))
fix_term(
	( (VP,np:X~>s:F), n:_~>n:_ ),
	( WH @ (VP,np:X~>s:F), n:_~>n:_ )
) :- %!!! how do you deal with the verb then? any rule fpr this? %+++
	memberchk(F, [ng, adj, pss, dcl]), % adj: full of X:np~>s:sdj--->n~>n, relax constrain with no checking?
	WH = (tlp('which','which','WDT','I-NP','Ins'), (np:_~>s:_)~>n:_~>n:_),
	fix_report(['!!! Fix: insert Which Is for lex_rule. Feature = ', F]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% explain lex_rule vp --> np~>np
% ((owning X, vp), np~>np) (every man) --> (who,vp~>(np~>np)) (owning X, vp) (every man)
fix_term(
	( ((VP,np:A~>s:B), np:C~>np:D) @ QNP, np:E),
	( (WH @ (VP,np:A~>s:B), np:C~>np:D) @ QNP, np:E )
) :- %+++
	% define NP modifier "who", we dont use "is"
	WH = (tlp('which','which','WDT','I-NP','Ins'), (np:A~>s:B)~>np:C~>np:_),
	fix_report('!!! Fix: insert Which Is for lex_rule: vp->np->np').


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Change plural-some to several
fix_term(
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
fix_term(
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
fix_term(
	( tlp(',', ',', ',',F1,F2), Ty~>Ty~>Ty ),
	( tlp('and','and','CC',F1,F2), Ty~>Ty~>Ty )
) :-
	fix_report('!!! Fix: comma replaced by and').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% fix a weird type of a conjunction that is under a relative pronoun
% SICKNL-372: die:s~>np~>np @ (en:vp~->vp~>s @ VP @ VP) --> die:vp~>np~>np @ (en:vp~->vp~>vp @ VP @ VP) 
fix_term(
	((WH_TLP,s:_~>Ty~>Ty) @ (((CC_TLP,_) @ (C1,Ty1), _) @ (C2,Ty2), _), _),
	((WH_TLP,Ty1~>Ty~>Ty) @ (((CC_TLP,Ty1~>Ty1~>Ty1) @ (C1,Ty1), Ty1~>Ty1) @ (C2,Ty2), Ty1), Ty~>Ty)
) :-
	tlp_pos_with_prefixes(WH_TLP, ['PRP', 'W']),
	tlp_pos_in_list(CC_TLP, ['CC']),
	\+ Ty1 \= Ty2. % unifiable but without binding variables


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% attach remote DT to the head of NP
% e.g. The [people who were at the meeting] [All] laughed
fix_term(
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
fix_term(
	( (Mod @ (tlp(_,L,POS,_,_),n:_), n:_), np:F1 ),
	( (Quant,n:F2~>np:F1) @ (Mod @ (Noun,n:F2), n:F2), np:F1)
) :-
	nonvar(L),
	memberchk(POS, ['DT','PRON','PRP','PRP$']),
	decompose_everyone(L, Q, N),
	Quant = tlp(Q,Q,'DT','Ins','Ins'),
	Noun = tlp(N,N,'NN','Ins','Ins'),
	fix_report('!!! Fix: decompose GQ').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% someone,np -> some:n->np @ person:n
% sick-2405, 6146, 3258
fix_term(
	( tlp(_,L,POS,_Feat1,_),np:F1 ),
	( (Quant,n:F2~>np:F1) @ (Noun,n:F2), np:F1 )
) :-
	nonvar(L),
	memberchk(POS, ['DT','PRON','PRP','PRP$']),
	decompose_everyone(L, Q, N),
	Quant = tlp(Q,Q,'DT','Ins','Ins'),
	Noun = tlp(N,N,'NN','Ins','Ins'),
	fix_report('!!! Fix: decompose GQ').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% no,n~>np (sleeping:n~>n one:n) -> no,n~>np (sleeping:n~>n person:n)
% sick-2404
fix_term(
	( (Q,n:X~>np:Y) @ (Nmod @ (One,n:F), n:X), np:Z ),
	( (Q,n:X~>np:Y) @ (Nmod @ Person, n:X), np:Z )
) :-
	is_tlp(Q), Q = tlp(_,'no',_,_,_),
	is_tlp(One), One = tlp(_,'one','NN',_,_),
	Person = (tlp('person','person','NN','Ins','Ins'), n:F),
	fix_report('!!! Fix: GQ with verb').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% no,n~>np (one:n~>n typing:n) -> no,n~>np (typing:n~>n person:n)
% sick-2937, 3353, 3439
fix_term(
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
% convert possessive pronoun as a possessive marker applied to the pronoun
% [its, n,(np,s),s]  ---> [s, np,n,(np,s),s] @ [it, np]
% sick-5003
fix_term(
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
fix_term(
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
fix_term(
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
% all the dogs ---> all dogs
% All:PDT:np~>np the:n~>np dogs:n ---> All dogs
%!!! should not be "not all", "not every"
% fracas-92
fix_term(
	( (tlp(T,L,'PDT',F1,F2),np:_~>np:_) @ ((DT,n:_~>np:_) @ N, np:_), np:_ ),
	( (tlp(T,L,'DT',F1,F2),n:_~>np:_) @ N, np:_)
) :-
	nonvar(L),
	tlp_pos_in_list(DT, ['DT']),
	fix_report('!!! Fix: attach pre determiner').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% not @ (all @ birds) -> (not @ all) @ birds
fix_term(
	( (NOT,_) @ ((ALL,n:_~>np:_) @ Noun, np:_), np:_ ),
	( ((NOT,Ty) @ (ALL,n:_~>np:_), n:_~>np:_) @ Noun, np:_ )
) :-
	tlp_pos_in_list(ALL, ['DT']), %urgent, fracas-134,
	% fracas-134, atomic list concat why removing this clause causes a problem?
	% expecting negation, but blocking weird order in alpino/npn:"jonge de jongens"
	tlp_pos_in_list(NOT, ['RB']),
	Ty = (n:_~>np:_)~>n:_~>np:_,
	fix_report('!!! Fix: not (all dogs) -> (not all) dogs').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% not @ everybody -> (not @ every) @ person
fix_term(
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
% not/niet @ anymore/veel -> anymore/veel @ not/niet
% MED-NL-3278
fix_term(
	((Not,_) @ (Anymore,_), TyS),
	((Anymore,TyS~>TyS) @ (Not,TyS), TyS)
) :-
	final_value_of_type(TyS, s:_),
	tlp_lemma_in_list(Not, ['not']),
	is_tlp(Anymore),
	fix_report('!!! Fix: not/niet @ anymore/veel -> anymore/veel @ not/niet').




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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
extract_samples(A, _) :-
	A = ((tlp(_,'by',_,_,_), _~>(np:_~>s:pss)~>_,_) @ (B, np:_, _), (np:_~>s:pss)~>_, _),
	ttTerm_to_prettyTerm((B, np:_), Pr),
	report([Pr]),
	fail.

fix_report(Message) :-
	( is_list(Message) -> M = Message; M = [Message] ),
	( debMode('fix') -> report(M); true ).


get_det_tlp(L, D) :-
	( debMode('the') ->
  	  D = tlp('the','the','DT','I-NP','Ins')
	; D = tlp(L,L,'DT','I-NP','Ins') ).
