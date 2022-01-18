%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module('utils/generic_preds', [
	dictList_to_dictPosition/2, read_dict_from_json_file/2, get_cmd/1
    ]).

:- ensure_loaded([
	'task/online_demo',
	'printer/extract',
	'task/sent_sim',
	'task/sentence_semantics',
	'task/bag_of_words',
	'prover/tt_nattableau',
	'task/entail',
	'task/kb_induction',
	'xml/xml_output',
	'printer/reporting',
    'knowledge/wn_preds',
	'latex/latex_ttterm',
	'testing/sick_train_trial_solved'
	]).

:- multifile ccg/2, id/2.
:- discontiguous ccg/2, id/2.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Initially debMode/1 was for bebugging
% now it serves as parameter input
:- dynamic debMode/1.
:- multifile debMode/1.
:- discontiguous debMode/1.
%:- discontiguous assertz_debMode_list/1.

%:- use_module(library(theme/dark)).

debMode( 'nil' ).
debMode( ral(400) ).
%debMode( effCr(['nonProd', 'nonBr', 'equi', 'nonCons']) ). % old one, not effcient
debMode( effCr(['equi', 'nonBr', 'nonProd', 'nonCons']) ). % one of four effcient ones
debMode(wn_sim).
debMode(wn_ant).
debMode(wn_der).
debMode(aall).
debMode(constchk).
debMode(parts(['trial'])).


reset_debMode :-
	retractall( debMode(_) ),
	assertz( debMode('nil') ),
	assertz( debMode(effCr(['equi', 'nonBr', 'nonProd', 'nonCons'])) ),
	set_rule_eff_order,
	assertz( debMode(parts(['trial'])) ),
	assertz( debMode(ral(400)) ).

set_debMode([H | Rest]) :-
	( H = ral(_) ->
		retractall( debMode(ral(_)) ),
		assertz( debMode(H) )
	; H = effCr(_) ->
		retractall( debMode(effCr(_)) ),
		assertz( debMode(H) )
	; H = ss(SS) ->
		retractall( debMode(ss(_)) ),
		( is_list(SS) -> SS1 = SS
		; integer(SS) -> numlist(1,SS,L), SS1 = L
		; float(SS) -> SS1 = SS % in an open interval (0,1)
		; throw_error('Unexpected parameter for wn senses: ~q', [H]) ),
		assertz( debMode(ss(SS1)) )
	; H = parallel(Cores) ->
		% TODO use set_prolog_flag(cpu_count,Cores).
		( var(Cores) -> current_prolog_flag(cpu_count, Cores)
		; set_prolog_flag(cpu_count, Cores) ),
		assertz( debMode(parallel(Cores)) )
	; H = output_branches(Exts, Filename) ->
		findall(_, (
			member(Ext, Exts),
			format(atom(FilenameExt), '~w.~w', [Filename, Ext]),
			open(FilenameExt, write, S, [encoding(utf8), close_on_abort(true)]),
			assertz( debMode(stream(branches, Ext, S)) )
		), _)
	; H = anno_json(JSON) ->
		read_dict_from_json_file(JSON, AnnoDict),
		assertz( debMode(anno_dict(AnnoDict)) ),
		SysOrder = AnnoDict.meta.sys_order,
		dictList_to_dictPosition(SysOrder, AnnoSys2Idx),
		assertz( debMode(anno_sys_idx(AnnoSys2Idx)) ),
		assertz( debMode(anno_json(JSON)) )
	; H = parts(_) ->
		retractall( debMode(parts(_)) ),
		assertz( debMode(H) )
    ; H == wn ->
        assertz_debMode_list([wn_sim, wn_ant, wn_der])
	; H == pr_cmd ->
		get_cmd(CMD), writeln(CMD)
	; assertz( debMode(H) )
	),
	set_debMode(Rest).

set_debMode([]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% a shortcut for asserting several items
assertz_debMode_list([H|R]) :-
    assertz( debMode(H) ),
    assertz_debMode_list(R).

assertz_debMode_list([]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Set parameters from the scratch
parList(Parameters) :- % TODO fix the keywords and error on unknown ones
	is_list(Parameters) ->
		reset_debMode,
		set_debMode(Parameters)
	; throw_error('No list argument given to parList!', []).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
print_param :-
	listing(debMode(_)).

%%%%%%%%%%%%%%%%%%%%%%%%%
% add terms to a stream that usually corresponds to an open file
add_to_stream(DataType, Data) :-
	findall(_, (
		debMode(stream(DataType, Ext, S)),
		( DataType == 'branches' ->
			add_branches_to_stream(S, Data, Ext)
		)
	), _).

%%%%%%%%%%%%%%%%%%%%%%%%
% Patch: switching from /5 to /6 that has data part in it
sen_id(SID, PID, PH, P, H) :-
    debMode(parts(Parts)), % FIXME normally only problem selection should be parts/1-filter sensitive
    member(Part, Parts),
    sen_id(SID, PID, PH, Part, P, H).

sen_id_general(SID, PID, PH, P, H) :- % insensitive to parts/1 filter
	once(sen_id(SID, PID, PH, _Part, P, H)).
%%%%%%%%%%%%%%%%%%%%%%%%
% Patch:
ccg(ID, Tree) :- % FIXME integrate ccg(Parsers) in anno_sys
	debMode(ccg(Parsers)),
    member(P, Parsers),
    ccg(ID, P, Tree).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 				List of Parameters
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  debMode
% data:sick				use sick data
% lang(nl)				activate NL-specific rules, e.g., vp_pr_vs_vp for beklimmen<=>klimmen@op
% 'once_solved:parser'	compare predicted problems to the list of once-solved problems
% 'xml'					write terms or tableaux in XML
% 'html'				write twrms and tableaux in HTML, outomatically creates XML files too
% 'fix' 				prints fixes done on CCG trees
% gtraceProb(Id)		Trigger gtrace for a particular problem
% gtraceSen(Id)		   Trigger gtrace for a particular sentence
% 'proof_tree'   		develope a proof tree
% 'aall'    				allows alignment of any NPs
% cpu_count				the number of threads to use for concurrent run
% complete_tree			Proof stopped when the RAL is reached, not when an open branch is found
% latex_no_corrected    print in latex only original trees, no corrected or type-raised ones
% latex_no_type_raised  don't print in latex type-raised tts
% 'prprb'				prints the problem
%  waif(filename) 		writes answers in file in SICK style
%  waifx				writes extended answers in file
%  output_branches([txt,json], filename)	output branches in a json or txt (human readable) format
% 'ne'					reports MW Named Entity found
% 'mwe'		   	       	multiword expression found
% 'prlim'				prints when rule limit is reached
% 'ProperNames' 		consideres all bare nouns (even plurals) as proper names
% 'the'	    			inserts "the" for bare nouns (even plurals) instead of "a"
%  a2the				replace all a,an with the
%  s2the				replaces all plurals with definites
%  thE					allow Existential import for the in false context
% 'wn_ant'				uses antonym relation of Wordnet
%  prlex				print extracted Lexicon
% '2class'				binary classification
%  ral(N)				rule application limit is N
%  no_gq_llfs			dont obtain LLFs with generalized quantifiers, i.e. use fixed CCG terms
%  gq_report			report how quantifier raising is going on
%  pr_lex_rules			print lexical rules that are not explained
%  pr_sen				print a sentence when running gen_llfs_latex
%  disj					use hand-coded disjoint relation
%  usedRules([rules])	print the rules if they are used
%  parallel(CPUs)		concurrent_maplist for entail
%  pr_cmd				print the executed command
%  pr_kb				print knowledge base
%  hk					use hand crafted lexical knowledge base
%  no_wn				no wn knowledge will be used
%  no_qk				no quantifier knowledge will be used
%  singPrem				takes only single premised problems, for fracas
%  fracFilter			filter Fracas problems that are ill formed
%  noPl					Treat plural morpheme as a
%  constchk				allow consistency check
%  noHOQ				Treating "most", "many", "several", "a_few", "both" as "a"
%  noThe				Treat "the" as "a"
%  shallow				using shallow classifier
%  neg_cont				classifier based on negative vords to identify contradictions
%  sub_ent				classifier based on subset of set of words to identify entailment
%  noAdmissRules		exclude admissible rules
%  single_branch_model	Apply rules in such a way that one gets only single branches
%  EffCr([nonBr, equi, nonProd, nonCons])	defining an effciency criterion
%  eccg				    latex trees are printed in different tex file
%  ss([...])			list of frequent sysnsets to choose
%  allInt				All noun modifeirs are intersective
%  llf_norm				normalize lexicon-wise corrected ccg terms
%  ccg_norm				normalize lexicon-wise uncorrected ccg terms
%  lab_map:mapping_name	Map labels of problems to other ones, e.g., for SICK
% anno_sys(anno_key, list_of_sys)   Use certain system annotations for a specific annotation type. If systems are not specified, all availabel systems are used. anno_keys can be ccg,l,ppos,wn,ner
%%%%%%%%%%%%  Ab|In-duction parameters  %%%%%%%%%%%%%%%%%
% align-(both|no_align|both)	when building tableau for abduction use $align LLFs
% constchk			Use consistency check of sentences to discard induced KB
% fold-N			Defines N-CV for abduction
% constKB			abduced KB should be consistent with initial KB
% compTerms			abduced KB should contain relations over compatible terms
% patterns-[pat]	list of patterns, e.g., _@_, etc
% v(VAR)			verbosity flag for particular procedures
%	indKB_scores	before selecting best KB, print the scores of all
