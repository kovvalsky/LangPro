%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: JSON output for LLFs and Proofs
% 	   Author: lasha.abzianidze{at}gmail.com
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module('json_output',
	[
		parsed_problem_to_dict/3
		% write_json_proof_tree/3,
		% tree_structure/1
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
% write_json_proof_tree(S, Tree, PID) :-
% 	retract(tree_structure(_)),
% 	asserta(tree_structure(Tree)),
% 	problem_to_dict(PID, ProbDict), !,
% 	term_to_json(Tree, TreeJson),
%     ProbTreeDict = j{problem:ProbDict, proof:TreeJson},
%     json_write(S, ProbTreeDict, [width(80), step(2), tab(4)]),
% 	!.


% problem_to_dict(PID, Dict) :-
%     sen_id(_, PID, _, Answer, _), !,
%     findall(P, sen_id(Id, PID, 'p', Answer, P), PList),
%     sen_id(Id, PID, 'h', Answer, H),
%     Dict = j{problem_id:PID, gold_label:Answer, premises:PList, hypothesis:H},
%     !.


% strcuture the problem and its terms as a Dict
parsed_problem_to_dict(Align, ProbID, Dict) :-
	findall(X, sen_id(X, ProbID, _, _, _), IDs),
	%free_vars_to_indexed_atoms('x', TTterms, PrettyTTterms),
	findall(ccg(X, CCG), (member(X, IDs), ccg(X, CCG)), CCG_IDs),
	maplist(ccgIDTree_to_ccgIDTerm, CCG_IDs, CCGTerms_IDs),
	maplist(nth1_projection(2), CCGTerms_IDs, CCGTerms),
	maplist(ne_ccg, CCGTerms, CCGTerms_ne),
	maplist(clean_ccgTerm_once, CCGTerms_ne, CCGTerms_clean),
	maplist(correct_ccgTerm, CCGTerms_clean, CCGTerms_corr),
	maplist(once_gen_quant_tt, CCGTerms_corr, _LLFs),
	problem_to_ttTerms(Align, ProbID, PremLLFs, HypLLF, Al_PremLLFs, Al_HypLLF, _KB),
	( Align == 'align' ->
		append(Al_PremLLFs, Al_HypLLF, FinLLFs),
		AlignedBool = true
	; 	append(PremLLFs, HypLLF, FinLLFs),
		AlignedBool = false
	),
	all_terms_per_sentence_as_dict(IDs, CCG_IDs, CCGTerms, CCGTerms_corr, FinLLFs, DictList),
	Dict = j{prob_id:ProbID, prob:DictList, aligned_llfs:AlignedBool}.

% prepresent a sentence and its corresponding structures as a dict
% j{sen_id:ID, role:PH, sen:Sent, 
%   terms:j{ccg_tree:Tree, ccg_term:Term, corr_term:Corr, llf: LLF}}
all_terms_per_sentence_as_dict([ID | Rest], CCG_IDs, CCGTerms, CCGTerms_corr, LLFs, DictList) :-
	!,
	sen_id(ID, _, PH, _, Sent),
	Dict0 = j{sen_id:ID, role:PH, sen:Sent},
	( nth1(I, CCG_IDs, ccg(ID, CCG)) ->
		nth1(I, CCGTerms, CCGTerm),
		nth1(I, CCGTerms_corr, CCGTerm_corr),
		nth1(I, LLFs, LLF),
		maplist(term_to_json, 	[CCG, CCGTerm, CCGTerm_corr, LLF], 
								[CCG_J, CCGTerm_J, CCGTerm_corr_J, LLF_J]), 
		Dict1 = Dict0.put([tree=_{
			ccg_tree:CCG_J, 
			ccg_term:CCGTerm_J, 
			corr_term:CCGTerm_corr_J, 
			llf:LLF_J
			}])
	; Dict1 = Dict0
	),
	DictList = [Dict1 | RestDictList],
	all_terms_per_sentence_as_dict(Rest, CCG_IDs, CCGTerms, CCGTerms_corr, LLFs, RestDictList).

all_terms_per_sentence_as_dict([], _, _, _, _, []).