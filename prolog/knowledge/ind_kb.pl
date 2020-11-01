%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module(ind_kb,
    [
        add_ind_kb/2,
        induced_rel/1
    ]).

:- multifile ind_rel/1.

:- dynamic induced_rel/1.

%:- ensure_loaded(['../../ind_train_nokb_yn_al_chk']).
%:- ensure_loaded(['../../ind_train_nokb_yn_al_chk_3t_new']).
%:- ensure_loaded(['../../mine/induced_kb/ind_train_nokb_yn_al_chk_3t_aall_comp_new']).
%:- ensure_loaded(['../../mine/induced_kb/ind_train_nokb_yn_al_chk_3t_aall_comp_easy_new']).



add_ind_kb(KB0, KB) :-
    %findall(Rel, ind_rel(_-Rel), Rels),
    findall(Rel, induced_rel(Rel), Rels),
    append(KB0, Rels, KB).
