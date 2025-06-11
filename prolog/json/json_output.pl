%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: JSON output for LLFs and Proofs
% 	   Author: lasha.abzianidze{at}gmail.com
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module('json_output',
	[
		write_parsed_problem_as_json/3,
		write_json_proof_tree/3,
		tree_structure/1,
		xml_probs_llfs/1,
		xml_probs_llfs/2,
		xml_senIDs_llfs/1,
		xml_senIDs_llfs/2,
		xml_senIDs_llfs/3
	]).


:- use_module('../utils/user_preds', [listInt_to_id_ccgs/2, nth1_projection/3]).
:- use_module('../printer/reporting', [report/1]).
:- use_module('../llf/recognize_MWE', [clean_ccgTerm_once/2]).
:- use_module('../llf/ccg_term', [
	ccgIDTree_to_ccgIDTerm/2, op(601, xfx, (/)), op(601, xfx, (\))
	]).
:- use_module('../llf/correct_term', [correct_ccgTerm/2]).
:- use_module('../llf/ner', [ne_ccg/2]).
:- use_module('../llf/gen_quant', [once_gen_quant_tt/2]).
:- use_module('../llf/ttterm_to_term', [ttTerm_to_prettyTerm/2]).
:- use_module('../llf/ttterm_preds', [pretty_vars_in_ttterm/4]).
:- use_module('../lambda/lambda_tt', [op(605, xfy, ~>),	op(605, yfx, @)]).

:- use_module(library(term_to_json), [term_to_json/2]).
:- use_module(library(http/json), [json_write/2, json_write/3]).

:- dynamic tree_structure/1.
tree_structure(nil).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%    JSON Output of trees, terms and LLFs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
write_json_proof_tree(S, Tree, PID) :-
	retract(tree_structure(_)),
	asserta(tree_structure(Tree)),
	problem_to_dict(PID, ProbDict), !,
	term_to_json(Tree, TreeJson),
    ProbTreeDict = j{problem:ProbDict, proof:TreeJson},
    json_write(S, ProbTreeDict, [width(80), step(2), tab(4)]),
	!.


problem_to_dict(PID, Dict) :-
    sen_id(_, PID, _, Answer, _), !,
    findall(P, sen_id(Id, PID, 'p', Answer, P), PList),
    sen_id(Id, PID, 'h', Answer, H),
    Dict = j{problem_id:PID, gold_label:Answer, premises:PList, hypothesis:H},
    !.



write_parsed_problem_as_json(S, Align, ID) :-
    % dummy
    format(S, 'aligned=~w, ID=~w', [Align, ID]).

