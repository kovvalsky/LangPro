%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module('../utils/user_preds', [
    sen_input_to_list/2, probIDs_to_senIDs/2, prob_input_to_list/2
    ]).
:- use_module('../printer/reporting', [
    report/1, report/2
    ]).
:- use_module('../rules/rule_hierarchy', [set_rule_eff_order/0]).
:- use_module('../llf/ttterm_to_term', [ndId_to_pretty_atom/2]).
:- use_module('../llf/ttterm_preds', [normalize_lexicon/3]).
:- use_module(library(term_to_json), [term_to_json/2]).
:- use_module(library(http/json), [json_write/2, json_write/3]).


:- dynamic output_file_extension/1.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
all_sen_sem(Filename) :-
    some_sen_sem(Filename, _).

some_sen_sem(Filename, In) :-
    sen_input_to_list(In, List),
    set_rule_eff_order,
    maplist(senId_branch_sem, List, L_BrsTF),
    maplist([E, ['no_align'-E]]>>true, List, No_align_List),
    open(Filename, write, S, [encoding(utf8), close_on_abort(true)]),
    file_name_extension(_, Ext, Filename),
    assertz(output_file_extension(Ext)),
    maplist(write_branch_sem(S), No_align_List, L_BrsTF),
    retractall(output_file_extension(_)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
all_prob_sen_sem(Filename) :-
    some_prob_sen_sem(Filename, _).

% example: parList([aall, allint]), probId_branch_sem(1, P, H).
some_prob_sen_sem(Filename, In) :-
    prob_input_to_list(In, PrIdList),
    set_rule_eff_order,
    maplist(probId_branch_sem, PrIdList, L_PrHyBrs, L_A_PrHyBrs),
    open(Filename, write, S, [encoding(utf8), close_on_abort(true)]),
    file_name_extension(_, Ext, Filename),
    assertz(output_file_extension(Ext)),
    maplist(write_branch_sem(S, 'no_align'), PrIdList, L_PrHyBrs),
    maplist(write_branch_sem(S, 'align'), PrIdList, L_A_PrHyBrs),
    retractall(output_file_extension(_)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
write_branch_sem(S, Align, PrId, (PrBrs, HyBrs)) :-
    maplist(write_branch_sem(S, [PrId,'p',Align]), PrBrs),
    maplist(write_branch_sem(S, [PrId,'h',Align]), HyBrs).


write_branch_sem(S, Info, (BrT, BrF)) :-
    append(Info, ['true'],  InfoT),
    append(Info, ['false'], InfoF),
    output_file_extension(Ext),
    add_branches_to_stream(S, (InfoT, BrT), Ext),
    add_branches_to_stream(S, (InfoF, BrF), Ext).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  IN: problem ID
% OUT: branches modeling semantcis of the (Aligned) premise and hypothesis TTs
% Premise and hypothesis TTterms are also optionally aligned
probId_branch_sem(Id, (PrBrs, HyBrs), (A_PrBrs, A_HyBrs)) :-
    ( problem_to_ttTerms('both', Id, PrTTs, HyTTs, A_PrTTs, A_HyTTs, KB) ->
        append(PrTTs, HyTTs, LLFs),
        % no consistency checking here
        ( ttTerms_same_type(LLFs, _Type) ->
            maplist(ttterm_branch_sem(KB), PrTTs, PrBrs),
            maplist(ttterm_branch_sem(KB), HyTTs, HyBrs),
            maplist(ttterm_branch_sem(KB), A_PrTTs, A_PrBrs),
            maplist(ttterm_branch_sem(KB), A_HyTTs, A_HyBrs)
        ; report(['Inconsistency in node types (probId_branch_sem/3)']),
            maplist(=([]), [PrBrs, HyBrs, A_PrBrs, A_HyBrs])
        )
    ; report(['Failed to get ttTerms (probId_branch_sem/3)']),
        maplist(=([]), [PrBrs, HyBrs, A_PrBrs, A_HyBrs])
    ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  IN: sentence ID
% OUT: A pair of branches modeling semantcis of the TT of the sentence
senId_branch_sem(Sid, (BrsT, BrsF)) :-
    senId_to_ttterm(Sid, TTterm),
    extract_lex_NNPs_ttTerms([TTterm], Lexicon, _, _Names),
    normalize_lexicon(Lexicon, Lex, _), % TOCHECK
    ( debMode('no_wn') -> KB = []; kb_from_wn(Lex, KB) ),
    ttterm_branch_sem(KB, TTterm, (BrsT, BrsF)).

senId_to_ttterm(Sid, TTterm) :-
    ccg(Sid, CCGTree),
    ccgTree_to_correct_ccgTerm(CCGTree, CCGTerm),
    % no lexicon normalization is done, unlike for processing problems
    once_gen_quant_tt(CCGTerm, TTterm).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  IN: knowledge base (KB), TTterm (TT)
% OUT: A pair of branches modeling TT's truth and false semantics
ttterm_branch_sem(KB, TT, (BrsT, BrsF)) :-
    ( generateTableau(KB-_, [TT], [], BrsT, _TreeT, _StatusT) -> true
    ; BrsT = [] ),
    ( generateTableau(KB-_, [], [TT], BrsF, _TreeF, _StatusF) -> true
    ; BrsF = [] ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
add_branches_to_stream(S, (Info, BrList), Ext) :-
	Info = [PrId | Mode],
    ( memberchk('p', Info) -> PH = 'p'; PH = 'h' ), % FIXME: only works for single prem
    once(sen_id(_, PrId, PH, Ans, Sent)),
	( Ext == 'json' ->
        maplist(branch_to_json, BrList, L_JsonBr),
		Dict = j{id:PrId, label:Ans, sentence:Sent, mode:Mode, branches:L_JsonBr},
		term_to_json(Dict, Json),
		json_write(S, Json, [width(80), step(2), tab(4)])
	; Ext == 'txt' ->
		format(S, 'branches: ~w~nsentence: ~w~n', [[Ans|Info], Sent]),
		findall(_, (
				member(br(NdIds,Hist,Sig), BrList),
				maplist(ndId_to_pretty_atom, NdIds, PrettyNdIds),
				format(S, '  [~n    ~w~n', [Sig]),
				format_list(S, '    ~w~n', Hist),
				format_list(S, '    ~w~n', PrettyNdIds)
			),_)
	),
	nl(S),
	flush_output(S).


branch_to_json(br(NdIds,Hist,Sig), Json) :-
    maplist(ndId_to_pretty_atom, NdIds, AtomNdIds),
    maplist(term_to_atom, Hist, AtomHist),
    maplist(term_to_atom, Sig, AtomSig),
    Json = j{nodes:AtomNdIds,rules:AtomHist,sig:AtomSig}.
