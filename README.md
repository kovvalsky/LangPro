# LangPro: Natural Language Theorem Prover
LangPro is a tableau-based theorem prover for natural logic and language.

This branch represents a version of LangPro that was descibed in [A Tableau Prover for Natural Logic and Language](http://www.aclweb.org/anthology/D15-1296.pdf) at EMNLP 2015. 

Given a set of premises and a hypothesis in natural language, LangPro tries to find out semantic relation between them: `entailment` (i.e. `yes`), `contradiction` (i.e. `no`) or `neutral` (i.e. `unknown`).  
For this, LangPro needs CCG (Combinatory Categorial Grammar) derivations of the linguistic expressions in order to obtain Lambda Logical Forms (LLFs) from them via the LLFgen (LLF generator) component. The architecture is depicted below: 
```
____________    ________             ___________      ________________________    __________ 
|Premises &|    | CCG  | derivations |   LLF   | LLFs |Tableau Theorem Prover|    |Semantic|
|Hypothesis|--->|Parser|------------>|Generator|----->|  for Natural Logic   |--->|relation|
‾‾‾‾‾‾‾‾‾‾‾‾    ‾‾‾‾‾‾‾‾             ‾‾‾‾‾‾‾‾‾‾‾      ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾    ‾‾‾‾‾‾‾‾‾‾ 
```

## Quick Usage

### Reproducing the Results Reported by [Abzianidze (2015)](http://www.aclweb.org/anthology/D15-1296.pdf)
Assuming that you have [SWI-Prolog](http://www.swi-prolog.org) installed, run the theorem prover for `SICK_test` parsed with the C&C CCG parser (`_ccg`):
```
swipl -f main.pl  -g "ensure_loaded(['ccg_sen/SICK_test_annotated_ccg.pl','ccg_sen/SICK_test_annotated_sen.pl'])" -g "set_debMode([ral(800), aall, wn_ant, waif('sick_test_candc_800.ans')])"   -g "entail_all, halt"
```
The prover is run with a strong alignment `aall`, WordNet antonymy relations `wn_ant`, and rule application limit 800 `ral(800)`. After all the problems are verified, the problemID-answer pairs are written in `sick_test_candc_800.ans` (`waif` = write answers in file). Similarly, run the prover for `SICK_test` parsed with easyCCG (`_eccg`):  
```
swipl -f main.pl  -g "ensure_loaded(['ccg_sen/SICK_test_annotated_eccg.pl','ccg_sen/SICK_test_annotated_sen.pl'])" -g "set_debMode([ral(800), aall, wn_ant, waif('sick_test_easyccg_800.ans')])"   -g "entail_all, halt"
```
Evaluate a simple combination of both answers against the gold labels:
```
./perl/combine_two_classifiers.pl  SICK_dataset/SICK_test_annotated.txt  sick_test_candc_800.ans  sick_test_easyccg_800.ans
```
The script also creates the `HYBRID_ANSWERS` files that lists the problemID-combinedAnswer pairs. Such files, with problemID-answer pairs, can be evaluated against the gold labels via:
```
./perl/evaluate.pl  SICK_dataset/SICK_test_annotated.txt  HYBRID_ANSWERS
```
Ready probleID-answer files are also available in `EMNLP_2015_results/`. 

### Running Natural Language Theorem Prover
You will need only [SWI-Prolog](http://www.swi-prolog.org) to run the prover.
Go to the main directory and run the following command in order to run the prover on the trial portion of the SICK dataset (included in `ccg_sen`):
```
swipl -f main.pl -l ccg_sen/SICK_trial_ccg.pl ccg_sen/SICK_trial_sen.pl
```
`*_ccg.pl` contains CCG derivations by the C&C CCG parser (Clark&Curran,2007) while `*_sen.pl` lists RTE problems. 
Choose `SICK_trial_eccg.pl` for the CCG derivations by EasyCCG (Lewis&Steedman, 2014). 
Now already in the Prolog environment, run 
```
gentail(211).              % gui/graphical entailment check
```
This will trigger a tableau in the XPCE GUI for the SICK-211 problem to verify its gold answer. 

Be aware not all IDs have corresponding problems in SICK-trial as it is just a portion of SICK. 
You can try: 4, 24, 105, 116, 119, 185, 197, ... 
In order to run the prover on several problems without GUI, by listing them or giving an interval, try:
```
entail_some([4, 24, 105, 116, 119, 185, 197]).
```
or equivalently
```
entail_some(1-200).
```
For each RTE problem, these commands will print the problem ID, the [gold answer], the prover's judgment and a tableau status (open/closed, terminated/limited, #rule applications). 
In the end, a confusion matrix with some stats is printed.
Something like this:
```
?- entail_some([4, 24, 105, 116, 119, 185, 197]).

   4:      [no],      no,  closed, Terminated 
  24: [unknown], unknown,    open, Terminated 
 105: [unknown], unknown,    open, Terminated 
 116: [unknown], unknown,    open, Terminated 
 119: [unknown], unknown,    open, Terminated 
 185: [unknown], unknown,    open, Terminated 
 197: [unknown], unknown,    open, Terminated 
------------------------------------------------------ 
 Gold\Prover       YES       NO       UNK       DEF
------------------------------------------------------ 
 ENTAILMENT:        0        0        0 (0)      0 
------------------------------------------------------ 
 CONTRADICTION:     0        1        0 (0)      0 
------------------------------------------------------ 
 NEUTRAL:           0        0        6 (0)      0 
------------------------------------------------------ 
Total #problems:  7
Accuracy (pure):  1.00000    (1.00000)
Precision:        1.00000
Recall (pure):    1.00000    (1.00000)
true.
```

Run the prover on all the problems of SICK-trial by:
```
entail_all.
```
The above predcates `entail_some/1` and `entail_all/0` build tableaux both for aligned and non-aligned LLFs.
If you want to terminate the run, type `Ctrl+C` and then press `a` for abort.


## References

1. R. Muskens (2010): [An Analytic Tableau System for Natural Logic](http://link.springer.com/chapter/10.1007/978-3-642-14287-1_11). LNCS, Vol. 6042, Springer.

   `Proposes to use a tableau system for natural logic`

2. L. Abzianidze (2015): [A Tableau Prover for Natural Logic and Language](http://www.aclweb.org/anthology/D15-1296.pdf). EMNLP.

   `Describe the theprem prover LangPro and reports its performance on the SICK and FraCaS datasets`

3. M. Lewis & M. Steedman (2014): A* CCG Parsing with a Supertag-factored Model. EMNLP.
4. M. Honnibal, J. R. Curran, and J. Bos (2010): Rebanking CCGbank for Improved NP Interpretation. ACL (48).
5. S. Clark and J. R. Curran (2007): Wide-Coverage Efficient Statistical Parsing with CCG and Log-Linear Models. Computational Linguistics, 33(4).

   `Describes EasyCCG and C&C parsers and their statistical models` 
   
6. Ch. Fellbaum eds. (1998): WordNet: an Electronic Lexical Database. MIT press.

   `WordNet which is used as a lexical knowledge database in the prover`

7. Cooper,  R.,  Crouch,  D.,  Eijck,  J.  V.,  Fox,  C.,  Genabith,  J.  V.,  Jaspars,  J.,  Kamp,  H., Milward, D., Pinkal, M., Poesio, M., Pulman, S., Briscoe, T., Maier, H., and Konrad, K. (1996). FraCaS: A Framework for Computational Semantics. Deliverable D16.
8. The FraCaS problems converted in [xml](https://nlp.stanford.edu/~wcmac/downloads/fracas.xml) by B. MacCartney.
9. Marelli,  M.,  Menini,  S.,  Baroni,  M.,  Bentivogli,  L.,  Bernardi,  R.,  and  Zamparelli,  R. (2014b).  A sick cure for the evaluation of compositional distributional semantic models. LREC'14.

   `The FraCaS and SICK textual entailment datasets which are use for evaluating the theorem prover`
