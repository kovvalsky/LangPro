### Cross-validation

For cherry-picked problems:
```
parList([aall, allInt, complete_tree, constchk, wn_ant, wn_sim, wn_der, no_kb, ral(100)]).
cv_induce_knowledge([3702,1755,7105], _, [constchk, fold-3, align-both, constKB, compTerms]).
```

For all training data, directly from terminal:
```
swipl -g "parList([allInt, complete_tree, aall, constchk, wn_ant, wn_sim, wn_der, no_kb, ral(10), parallel(8), v1]), load_ccg_sen_probs('ccg_sen_d/SICK_train_ccg.pl', 'ccg_sen_d/SICK_train_sen.pl', _TPIDA), cv_induce_knowledge(_PrIDs, _Answers, [align-both, patterns-([_,_@_,(_@_)@_, _@(_@_)]), constchk, fold-3])" -t halt -f prolog/main.pl
```

### Training with abduction

Training on particular problems with no initial KB
```
Config = [constchk,align-both,constKB,compTerms], train_with_abduction(Config, [3400-no,1294-no], IndKB, Scores, Acc).
```

### Proving
Proving with an initial KB
```
maplist(add_lex_to_id_ans, [3400-no,1294-no], TrainIDAL), predict_with_iKB([constchk,align-both], KB, TrainIDAL, _, _Acc, SolvA0, FailA0).
```


### WordNet

Checking WN relations:
`Lex = [(fallen, 'JJ'), (dead, 'NN')], kb_from_wn(Lex, KB).`

Without specifying POS tags:
`wn_preds:represents_wn_rel((burn,A)-(burning,B), Fact).
`
