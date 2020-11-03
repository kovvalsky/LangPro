**Replicating results reported in the [Learning as Abduction](https://arxiv.org/abs/2010.15909) paper.**

# Required

* [produce](https://github.com/texttheater/produce), a Make-like tool with python support
* LangPro
* [DepCCG](https://github.com/masashi-y/depccg), [EasyCCG](https://github.com/mikelewis0/easyccg), and [C&C](https://github.com/chrzyki/candc)
if you don't want to use already parsed and prolog-formatted SICK sentences found in `results/starSEM_2020/ccg_sen/` and `ccg_sen_d/`.

# Naming conventions

* `T`, `D`, and `E` stand for SICK-train (as `T`raining), SICK-trail (as `D`evelopment), and SICK-test (as `E`valuation), respectively.  
* `-k` stands for excluding the hand-crafted lexical relations.  
* `rN` sets rule application limit to `N`.   
* `cN` makes use of `N` threads for concurrent theorem proving. `c0` uses all available threads.  
* `w3` uses WordNet relations: synonymy, hypernymy/hyponymy, similar, derivation, and antonymy.  
* `ccg` denotes CCG derivations obtained from C&C with the rebanked model.  
* `eccg` denotes CCG derivations from EasyCCG with the standard model.  
* `depccg.trihf.sep` denotes CCG derivations from DepCCG with the standard triheadfirst model, where each SICK sentence is parsed separately.
the DepCCG derivations use EasyCCG lemmatizer and the C&C named entity recognizer.
This decision is not the best for performance but makes the settings comparable to [Yanaka et al. (2018)](https://www.aclweb.org/anthology/N18-1069/). 


# Running experiments

The following command runs Langpro with abductive learning for C&C derivations with 50 rule applications limits for all available threads.
This saves a significant amount of time (compared to `r800`) and sacrifices a little accuracy. 
Note that the paper reports results for unseen SICK-test using `r800` and all three parsers.
```
produce -f results/starSEM_2020/produce.ini  results/starSEM_2020/TE/ccg/TD_E/al,ch,w3,-k,r50,c0_ab,ch,cKB,cT,p123.log 
```
The command triggers train-evaluate scenario for C&C derivations (`TE/ccg/`).
First the proveris trained on `TD` (SICK-train & trail) via abduction, and then the prover uses the abduced/induced knowledge from `TD` to prove problems in `E` (SICK-test).
Training on `T+D` and evaluation on `E` is signified by `TD_E/`.


The command creates five files: `*.log` contains stdout and stderr, `*.ans_KB.pl` lists the learned set of relations, and `*.ans.E` and `.ans.T` contain <problem ID, predicted label> pairs.

```
ls results/starSEM_2020/TE/ccg/TD_E/al,ch,w3,-k,r50,c0_ab,ch,cKB,cT,p123*
results/starSEM_2020/TE/ccg/TD_E/al,ch,w3,-k,r50,c0_ab,ch,cKB,cT,p123.ans
results/starSEM_2020/TE/ccg/TD_E/al,ch,w3,-k,r50,c0_ab,ch,cKB,cT,p123.ans.E
results/starSEM_2020/TE/ccg/TD_E/al,ch,w3,-k,r50,c0_ab,ch,cKB,cT,p123.ans_KB.pl
results/starSEM_2020/TE/ccg/TD_E/al,ch,w3,-k,r50,c0_ab,ch,cKB,cT,p123.ans.T
results/starSEM_2020/TE/ccg/TD_E/al,ch,w3,-k,r50,c0_ab,ch,cKB,cT,p123.log
```

The scores of training and evaluation can be found in `*.log` and also obtained via running the evaluation script on predicted labels:
```
python3 python/evaluate.py --sys results/starSEM_2020/TE/ccg/TD_E/al,ch,w3,-k,r50,c0_ab,ch,cKB,cT,p123.ans.E  --gld SICK_dataset/SICK_test_annotated.txt 
```
Evaluate aggregated predictions from different CCG parser-based LangPro versions as:
```
python3 python/evaluate.py --sys results/starSEM_2020/TE/ccg/TD_E/al,ch,w3,-k,r50,c0_ab,ch,cKB,cT,p123.ans.E  results/starSEM_2020/TE/eccg/TD_E/al,ch,w3,-k,r50,c0_ab,ch,cKB,cT,p123.ans.E  results/starSEM_2020/TE/depccg.trihf.sep/TD_E/al,ch,w3,-k,r50,c0_ab,ch,cKB,cT,p123.ans.E  --gld SICK_dataset/SICK_test_annotated.txt --hybrid
```

For more details about the **Learning as Abduction** see [wiki pages](https://github.com/kovvalsky/LangPro/wiki/Learning-as-abduction)




