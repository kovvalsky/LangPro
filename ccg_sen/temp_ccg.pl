:- op(601, xfx, (/)).
:- op(601, xfx, (\)).
:- multifile ccg/2, id/2.
:- discontiguous ccg/2, id/2.

sen_id(1, 1, 'p', 'no', 'Mary loves every man owning cars').
sen_id(2, 1, 'p', 'no', 'Mary loves every man owning cars').

ccg(1,
 ba(s:dcl,
  lx(np, n,
   t(n, 'Mary', 'Mary', 'NNP', 'I-NP', 'I-PER')),
  fa(s:dcl\np,
   t((s:dcl\np)/np, 'loves', 'love', 'VBZ', 'I-VP', 'O'),
   fa(np,
    t(np/n, 'every', 'every', 'DT', 'I-NP', 'O'),
    ba(n,
     t(n, 'man', 'man', 'NN', 'I-NP', 'O'),
     lx(n\n, s:ng\np,
      fa(s:ng\np,
       t((s:ng\np)/np, 'owning', 'own', 'VBG', 'I-VP', 'O'),
       lx(np, n,
        t(n, 'cars', 'car', 'NNS', 'I-NP', 'O'))))))))).

ccg(2,
 ba(s:dcl,
  lx(np, n,
   t(n, 'Mary', 'Mary', 'NNP', 'I-NP', 'I-PER')),
  fa(s:dcl\np,
   t((s:dcl\np)/np, 'loves', 'love', 'VBZ', 'I-VP', 'O'),
   ba(np,
    fa(np:nb,
     t(np:nb/n, 'every', 'every', 'DT', 'I-NP', 'O'),
     t(n, 'man', 'man', 'NN', 'I-NP', 'O')),
    lx(np\np, s:ng\np,
     fa(s:ng\np,
      t((s:ng\np)/np, 'owning', 'own', 'VBG', 'I-VP', 'O'),
      lx(np, n,
       t(n, 'cars', 'car', 'NNS', 'I-NP', 'O')))))))).

