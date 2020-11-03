**Replicating results reported in the [Learning as Abduction](https://arxiv.org/abs/2010.15909) paper.**

# Output files

If you are only interested in the files with predictions for the SICK problems,
these files can be found in `results/starSEM_2020/TE/`.
`.log` files contain stdout of abduction and evaluation, while `.ans.T` and `.ans.E` contain predictions for SICK-train&trial and SICK-test, respectively. 

# Required

* [produce](https://github.com/texttheater/produce)
* [LangPro](https://github.com/kovvalsky/LangPro), obviously

# Running experiments

The following command runs Langpro with abductive learning for C&C derivations with 50 rule applications limits for all available threads.
This saves a significant amount of time (compared to `r800`) and sacrifices a little accuracy. 
```
produce -f results/starSEM_2020/produce.ini  results/starSEM_2020/TE/ccg/TD_E/al,ch,w3,-k,r50,c0_ab,ch,cKB,cT,p123.log 
```
The command triggers train-evaluate scenario for C&C derivations (`TE/ccg/`).
First the prover is trained on `TD` (SICK-train & trail) via abduction, and then the prover uses the abduced/induced knowledge from `TD` to prove problems in `E` (SICK-test).

The command creates the following files in `results/starSEM_2020/TE/ccg/TD_E`: `*.log` contains stdout and stderr, `*.ans_KB.pl` lists the learned set of relations, and `*.ans.E` and `.ans.T` contain <problem ID, predicted label> pairs.

To run the abductive learning for derivations produced by other parsers, replace `ccg` with `eccg` or `depccg.trihf.sep` in the above command.
Note that for simplicity CCG derivations of SICK sentences output by C&C, EasyCCG, and DepCCG are already provided in `results/starSEM_2020/ccg_sen/` and `ccg_sen_d/`. 

# Evaluation scores

The scores of training and evaluation can be found in `*.log` and also obtained via running the evaluation script on predicted labels:
```
python3 python/evaluate.py --sys results/starSEM_2020/TE/ccg/TD_E/al,ch,w3,-k,r800,c20_ab,ch,cKB,cT,p123.ans.E  --gld SICK_dataset/SICK_test_annotated.txt
```
Evaluate aggregated predictions from different CCG parser-based LangPro versions as:
```
python3 python/evaluate.py --sys results/starSEM_2020/TE/ccg/TD_E/al,ch,w3,-k,r800,c20_ab,ch,cKB,cT,p123.ans.E results/starSEM_2020/TE/eccg/TD_E/al,ch,w3,-k,r800,c20_ab,ch,cKB,cT,p123.ans.E results/starSEM_2020/TE/depccg.trihf.sep/TD_E/al,ch,w3,-k,r800,c20_ab,ch,cKB,cT,p123.ans.E   --gld SICK_dataset/SICK_test_annotated.txt  --hybrid
```

# References

For more details about the **Learning as Abduction** see [wiki pages](https://github.com/kovvalsky/LangPro/wiki/Learning-as-abduction)
