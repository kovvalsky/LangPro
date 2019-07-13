# LangPro: Natural Language Theorem Prover
LangPro is a tableau-based theorem prover for natural logic and language.
See the [online demo](http://h2770688.stratoserver.net/).
<!-- (http://naturallogic.pro/langpro). -->

Given a set of premises and a hypothesis in natural language, LangPro tries to find out semantic relation between them: `entailment` (i.e. `yes`), `contradiction` (i.e. `no`) or `neutral` (i.e. `unknown`).  
For this, LangPro needs CCG (Combinatory Categorial Grammar) derivations of the linguistic expressions in order to obtain Lambda Logical Forms (LLFs) from them via the LLFgen (LLF generator) component. The architecture is depicted below: 
```
____________    ________             ___________      ________________________    __________ 
|Premises &|    | CCG  | derivations |   LLF   | LLFs |Tableau Theorem Prover|    |Semantic|
|Hypothesis|--->|Parser|------------>|Generator|----->|  for Natural Logic   |--->|relation|
‾‾‾‾‾‾‾‾‾‾‾‾    ‾‾‾‾‾‾‾‾             ‾‾‾‾‾‾‾‾‾‾‾      ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾    ‾‾‾‾‾‾‾‾‾‾ 
```
If you use the theorem prover please cite [Abzianidze (2017)](#emnlp_demo_paper)
* For research matters see [References](#references)
* [Quick usage of LangPro](#running-the-prover)
* [Quickly get LLFs](#obtaining-lambda-logical-forms)


## Running the prover

You will need only [SWI-Prolog](http://www.swi-prolog.org) to run the prover.
Go to the main directory and run the following command in order to run the prover on the trial portion of the SICK dataset (included in `ccg_sen_d`):
```
swipl -f main.pl -l ccg_sen_d/SICK_trial_ccg.pl ccg_sen_d/SICK_trial_sen.pl
```
`*_ccg.pl` contains CCG derivations by the C&C CCG parser (Clark&Curran,2007) while `*_sen.pl` lists RTE problems. 
Choose `SICK_trial_eccg.pl` for the CCG derivations by EasyCCG (Lewis&Steedman). 
Now already in the Prolog environment, run 
```
gentail(211).              % gui/graphical entailment check
```
This will trigger a tableau in the XPCE GUI for the SICK-211 problem to verify its gold answer. 
If you prefer an HTML representation of the proof, add the `html` parameter before `gentail/1`:
```
parList([html]), gentail(211).
```
This first creates `xml/tableau-211-yes-no_align.xml` and then `xml/tableau-211-yes-no_align.html` from the latter via `xsltproc`.
The file names stand for "a tableau for problem-211 to verify entailment (i.e. yes) with no alignment techniques used".
To reset the parameter list for the next run use `parList([])`.
If you want to force the alignment of LLFs, run (because SICK-253 shows the effect of alignment well):
```
parList([]), gentail(align, 253).       % gentail(253) is the same as gentail(no_align, 253)
```
In the example, the phrase `is on top of the mountain` shared by the premise and the hypothesis is treated as an atomic term by the alignment technique.  
If you want to get both tableaux for entailment (yes) and contradiction (no) checks, run 
```
gentail_no_answer(211).    % or gentail_no_answer(align, 211) to force alignment of LLFs
```
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
?- entail_some(1-200).
   4:      [no],      no,  closed, 17         
  24: [unknown], unknown,    open, 'Ter',175  
 105: [unknown], unknown,    open, 'Ter',56   
 116: [unknown], unknown,    open, 'Ter',27   
 119: [unknown], unknown,    open, 'Ter',205  
 185: [unknown], unknown,    open, 'Ter',71   
 197: [unknown], unknown,    open, 'Ter',68   
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
------------ STATS -------------
Total #clTabperPrb:            1
Total #ruleApps for clTab:     17
Average #ruleApps for clTab:   17.00000
true.
```
Run the prover on all the problems of SICK-trial by:
```
entail_all.
```
The above predcates `entail_some/1` and `entail_all/0` build tableaux both for aligned and non-aligned LLFs.
If you want to terminate the run, type `Ctrl+C` and then press `a` for abort.
If you have a multi-core CPU, you can use `parallel` in `parList` to prove problems in a concurrent way.
```
parList([parallel]), entail_all.    % similarly: parList([parallel]), entail_some(1-200). 
```
You can make theorem prover faster by building tableaux only for aligned LLFs (use `parList([])` to cancel the `parallel` parameter asserted by the previous command):
```
parList([]), entail_all(align).   % similarly: entail_some(align, 1-200)    
```
or even setting the rule application limit (RAL) in order to stop a tableau after the rule application limit is reached.
The default RAL is 400.  
```
parList([ral(50)]), entail_all(align).   % or combine it with parallel proving
```


### Optimal parameters
The theorem prover has several parameters (see `main.pl`). Part of these parameters control the actual proof procedure, For example:

* *rule application limit* (`ral/1`), 
* *wordnet relations* (`wn_ant/0`, `wn_sim/0`, `wn_der/0`), 
* *treatment of bare, plural and definite NPs* (`the/0`, `a2the/0`, `s2the/0`, `thE/0`, `noPl/0`, `noThe/0`, `noHOQ/0`), 
* *word senses filtering* (`ss/1`), 
* *rule efficiency criterion* (`effCr/1`), 
* intersectivity of unknown noun modifiers (`allInt/0`),
* strong alignment of LLFs (align all, `aall/0`),
* check consistency of each sentence `constchck/0`.

To run the theorem prover with the optimal set of parameters for SICK (according to [Abzianidze (2016b)](#phd_thesis)), run: 
```
parList([aall, wn_ant, wn_sim, wn_der, constchck, allInt, ral(800), waif('file_with_answers_inside.txt')]), entail_all.
```
For FraCaS run the command below. `fracFilter` guarantees that the problems with undefined gold answers are excluded.
```
parList([fracFilter, aall, wn_ant, ral(400), waif('fr_answers_all_sections.txt')]), entail_all.
```
`wn_sim`, `wn_der`, and `constchck` doesn't affect the answers. `ral(800)` is decreased to `ral(400)` as 400 rule applications seem enough for FraCaS problems.
This decrease also makes the pover faster. `allInt` is omitted as it hurts the performace because FraCaS contains many non-intersective adjectives.  
If you want to run the prover on certain sections of FraCas, e.g., 1, 2, 5 and 9, run:
```
parList([fracFilter, aall, wn_ant, ral(400), waif('fr_answers_sec1259.txt')]), findall(X, (sen_id(_,X,'h',_,_), (between(1,80,X); between(81,113,X);  between(197,219,X); between(334,346,X))), List), entail_some(List).
```
The command makes sure that the problem IDs fall in the specific sections, e.g., the Plurals section contains 81,...,113 problems.

### Evaluating or combining answers of prover(s)

After the prover generates all the answers in a file passed by the `waif/1` predicate, the evaluation can be done in the following way, depending on the dataset:
```
./perl/evaluate.pl  SICK_dataset/SICK_test_annotated.txt   file_with_answers_inside.txt  
./perl/evaluate.pl  FraCaS_dataset/FraCaS_gold.txt   file_with_answers_inside.txt  
```

It is also possible two combine two answer sets of the prover obtained based on different LLFs (e.g., resulted from different CCG parsers).
```
./perl/combine_two_classifiers.pl  SICK_dataset/SICK_test_annotated.txt  file_with_answers_inside_1.txt  file_with_answers_inside_2.txt
```
The script also creates the `HYBRID_ANSWERS` files that lists the problemID-combinedAnswer pairs.
Notice that if you have files with the answers for a part of a dataset, e.g., for the FraCaS sections 1 and 2, the evaluation and combining scripts will still work for them.


## Obtaining Lambda Logical Forms

In case you are interested in logical forms used by the prover, you can obtain them from CCG derivations.
After you get into the prolog environment by:
```
swipl -f main.pl -l ccg_sen_d/SICK_trial_ccg.pl ccg_sen_d/SICK_trial_sen.pl
```
You can obtain LLFs in XML and (optional) HTML formats by running:   
```
parList([html]), xml_probs_llfs([4,24,211], 'My_LLFs').    % or xml_probs_llfs([4,24,211]) where 'RTE_LLF' is a default file name 
```
This will create `xml/My_LLFs.xml` which contains a CCG (derivation) tree, a CCG term, a corrected CCG term and the first LLF (1LLF) for each sentence of the RTE problems [4,24,211].
Due to `parList([html])`, you will also get an HTML output for these terms in `xml/My_LLFs.html`.
In order to get HTML files the script uses `xsltproc`.
You can get exactly these quadruples of terms according to the sentence IDs too:  
```
parList([html]), xml_senIDs_llfs(1-6, 'My_LLFs').    % or xml_senIDs_llfs([1,2,3,4,5,6], 'My_LLFs') or even omitting the file name 
```
Because the first six sentences coincide the sentences of the first three RTE problems in the RTE dataset (i.e. two sentences per problem).
To get CCG trees, CCG terms, corrected CCG terms and 1LLFs for all sentences in the dataset, use:
```
parList([]), xml_senIDs_llfs(_, 'All_LLFs').                    % only XML file
parList([html]), xml_senIDs_llfs(_, 'All_LLFs').   % XML and HTML files, XSL transformation will take some time
```



## References

* R. Muskens (2010): [An Analytic Tableau System for Natural Logic](http://link.springer.com/chapter/10.1007/978-3-642-14287-1_11). LNCS, Vol. 6042, Springer.

   `Proposes to use a tableau system for natural logic`

* L. Abzianidze (2017): [LangPro: Natural Language Theorem Prover](https://aclanthology.info/pdf/D/D17/D17-2020.pdf). EMNLP. <a name="emnlp_demo_paper"></a>
* L. Abzianidze (2016a): [Natural Solution to FraCaS Entailment Problems](https://aclweb.org/anthology/S/S16/S16-2007.pdf). &ast;SEM.
* L. Abzianidze (2016b): [A Natural proof System for Natural Language](https://pure.uvt.nl/portal/files/14858339/Abzianidze_Natural_20_01_2017.pdf), PhD thesis, Tilburg University. <a name="phd_thesis"></a>
* L. Abzianidze (2015): [A Tableau Prover for Natural Logic and Language](http://www.aclweb.org/anthology/D15-1296.pdf). EMNLP.

   `Describe the theprem prover LangPro and reports its performance on the SICK and FraCaS datasets`

* M. Lewis & M. Steedman (2014): A* CCG Parsing with a Supertag-factored Model. EMNLP.
* M. Honnibal, J. R. Curran, and J. Bos (2010): Rebanking CCGbank for Improved NP Interpretation. ACL (48).
* S. Clark and J. R. Curran (2007): Wide-Coverage Efficient Statistical Parsing with CCG and Log-Linear Models. Computational Linguistics, 33(4).

   `Describes EasyCCG and C&C parsers and their statistical models` 
   
* Ch. Fellbaum eds. (1998): WordNet: an Electronic Lexical Database. MIT press.

   `WordNet which is used as a lexical knowledge database in the prover`

* Cooper,  R.,  Crouch,  D.,  Eijck,  J.  V.,  Fox,  C.,  Genabith,  J.  V.,  Jaspars,  J.,  Kamp,  H., Milward, D., Pinkal, M., Poesio, M., Pulman, S., Briscoe, T., Maier, H., and Konrad, K. (1996). FraCaS: A Framework for Computational Semantics. Deliverable D16.
* The FraCaS problems converted in [xml](https://nlp.stanford.edu/~wcmac/downloads/fracas.xml) by B. MacCartney.
* Marelli,  M.,  Menini,  S.,  Baroni,  M.,  Bentivogli,  L.,  Bernardi,  R.,  and  Zamparelli,  R. (2014b).  A sick cure for the evaluation of compositional distributional semantic models. LREC'14.

   `The FraCaS and SICK textual entailment datasets which are use for evaluating the theorem prover`

