:- op(601, xfx, (/)).
:- op(601, xfx, (\)).
:- multifile ccg/2, id/2.
:- discontiguous ccg/2, id/2.

ccg(1,
 ba(s:dcl,
  fa(np,
   t(np/n, 'a', 'a', 'DT', 'I-NP', 'O'),
   t(n, 'bird', 'bird', 'NN', 'I-NP', 'O')),
  rp(s:dcl\np,
   t(s:dcl\np, 'flew', 'fly', 'VBD', 'I-VP', 'O'),
   t(period, '.', '.', '.', 'O', 'O')))).

ccg(2,
 ba(s:dcl,
  fa(np,
   t(np/n, 'a', 'a', 'DT', 'I-NP', 'O'),
   t(n, 'lark', 'lark', 'NN', 'I-NP', 'O')),
  rp(s:dcl\np,
   t(s:dcl\np, 'flew', 'fly', 'VBD', 'I-VP', 'O'),
   t(period, '.', '.', '.', 'O', 'O')))).

