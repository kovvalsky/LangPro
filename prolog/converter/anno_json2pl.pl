%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Convert token-level annotatiosn
% from json to prolog
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(library(http/json)).

anno_json2pl(JSONFile, PlFile) :-
	read_dict_from_json_file(JSONFile, Dict),
	dict_pairs(Dict, _Tag, Pairs1),
	maplist([K-V,N-V]>>(atom_number(K,I) -> N=I; N=K), Pairs1, Pairs2),
	sort(1, @=<, Pairs2, Pairs3),
	findall(K-V, (member(K-V, Pairs3), number(K)), Pairs),
	open(PlFile, write, S, [encoding(utf8), close_on_abort(true)]),
	with_output_to(S, write_meta(Dict.meta)),
	with_output_to(S, maplist(write_sen_anno, Pairs)),
	flush_output(S).


% read dictionary from json file
read_dict_from_json_file(JSON, Dict) :-
    open(JSON, read, S, [encoding(utf8), close_on_abort(true)]),
    json_read_dict(S, Dict, [value_string_as(atom), default_tag(j)]).

write_meta(Meta) :-
	format('~n~nanno_meta(~q).~n~n', [Meta]),
	dictList_to_dictPosition(Meta.sys_order, Sys2Pos),
	format('anno_sys_position(~q).~n~n', [Sys2Pos]).

write_sen_anno(Key-TokenAnnos) :-
	format('anno_sen(~q, [~n', [Key]),
	write_token_anno_list(TokenAnnos),
	format(']).~n', []).

% write a sentence annotation,
% make sure at the end of the final token there is no comma
write_token_anno_list([TA1,TA2|TokenAnnos]) :- !,
	write_token_anno(TA1, NewTA1),
	format('\t~q,~n', [NewTA1]),
	write_token_anno_list([TA2|TokenAnnos]).

write_token_anno_list([TA]) :- !,
	write_token_anno(TA, NewTA),
	format('\t~q~n', [NewTA]).

% write annotatiosn of a singel token.
% Convert offsets into a list of pairs
write_token_anno(TokenAnnos, NewAnno) :-
	dict_pairs(TokenAnnos, Tag, Pairs),
	offset_as_list(Pairs, Pairs1),
	downcase_lemmas(Pairs1, NewPairs),
	dict_pairs(NewAnno, Tag, NewPairs).

% Convert offsets into a list of pairs: 0-7 ==> [0-7]
offset_as_list(Key_Val, Key_Val1) :-
	once(nth1(Ind, Key_Val, 'o'-Offset, Rest)),
	term_to_atom(Start-End, Offset),
	nth1(Ind, Key_Val1, 'o'-[Start-End], Rest).

% lowercase all lemmas
downcase_lemmas(Key_Val, Key_Val1) :-
	once(nth1(Ind, Key_Val, 'l'-Lemmas, Rest)),
	findall(Dw, (
		member(L, Lemmas),
		( L == 'NULL' -> Dw = L; downcase_atom(L, Dw) )
	), DwLemmas),
	nth1(Ind, Key_Val1, 'l'-DwLemmas, Rest).

% convert key->list structure into key->list_el->position
dictList_to_dictPosition(DictList, DictPos) :-
	dict_pairs(DictList, _, Pairs),
	maplist([K-L, K-D]>>list_to_dict(L,D), Pairs, Pairs1),
	dict_pairs(DictPos, d, Pairs1).

% convert list to a dictionary of elements to their positions
list_to_dict(List, El_Index) :-
	findall(E-I, nth1(I, List, E), E_I_List),
	dict_create(El_Index, d, E_I_List).
