# Required

* [produce](https://github.com/texttheater/produce), a Make-like tool with python support
* LangPro
* [DepCCG](https://github.com/masashi-y/depccg), [EasyCCG](https://github.com/mikelewis0/easyccg), and [C&C](https://github.com/chrzyki/candc)
if you don't want to use already parsed and prolog-formatted SICK sentences found in `results/starSEM_2020/ccg_sen/`.

# Naming conventions

`T`, `D`, and `E` stand for SICK-train (as `T`raining), SICK-trail (as `D`evelopment), and SICK-test (as `E`valuation), respectively.  
`-k` stands for excluding the hand-crafted lexical relations.  
`rN` sets rule application limit to `N`.   
`cN` makes use of `N` threads for concurrent theorem proving. `c0` uses all available threads.  
`w3` uses WordNet relations: synonymy, hypernymy/hyponymy, similar, derivation, and antonymy.  
`ccg` denotes CCG derivations obtained from C&C with the rebanked model.  
`eccg` denotes CCG derivations from EasyCCG with the standard model.  
`depccg.trihf.sep` denotes CCG derivations from DepCCG with thw standard triheadfirst model, where each SICK sentence is parsed separately.
the DepCCG derivations use EasyCCG lemmatizer and the C&C named entity recognizer.
This decision is not the best for performance but makes the settings comparable to [Yanaka et al. (2018)](https://www.aclweb.org/anthology/N18-1069/). 


# Running experiments

Run abductive learning for C&C derivations with 50 rule applicatios limits for all available threads.
This saves significant amount of time (compared to `r800`) and sacrifices a little accuracy. 
```
produce -f results/starSEM_2020/produce.ini results/starSEM_2020/TE/ccg/TD_E/al,ch,w3,-k,r50,c0_ab,ch,cKB,cT,p123.log 
```


