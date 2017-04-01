# LangPro: Natural Language Theorem Prover
LangPro is a tableau-based theorem prover for natural logic and language.
See the [online demo](http://naturallogic.pro/langpro).

Given a set of premises and a hypothesis in natural language, LangPro tries to find out semantic relation between them: `entailment` (i.e. `yes`), `contradiction` (i.e. `no`) or `neutral` (i.e. `unknown`).  
For this, LangPro needs CCG (Combinatory Categorial Grammar) derivations of the linguistic expressions in order to obtain Lambda Logical Forms (LLFs) from them via the LLFgen (LLF generator) component. The architecture is depicted below: 
```
____________    ________             ___________      ________________________    __________ 
|Premises &|    | CCG  | derivations |   LLF   | LLFs |Tableau Theorem Prover|    |Semantic|
|Hypothesis|--->|Parser|------------>|Generator|----->|  for Natural Logic   |--->|relation|
‾‾‾‾‾‾‾‾‾‾‾‾    ‾‾‾‾‾‾‾‾             ‾‾‾‾‾‾‾‾‾‾‾      ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾    ‾‾‾‾‾‾‾‾‾‾ 
```
* For research matters see [References](#references)
* [Quick usage of LangPro](#running-natural-language-theorem-prover)
* [Quickly get LLFs](#obtaining-lambda-logical-forms)


## Quick Usage

### Running Natural Language Theorem Prover
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
If you have a multicore CPU, you can use `parallel` in `parList` to prove problems in a concurrent way.
```
parList([parallel]), entail_all.    % similalrly: parList([parallel]), entail_some(1-200). 
```
You can make theorem prover faster by building tableaux only for aligned LLFS (use `parList([])` to cancel the `parallel` parameter asserted by the previous command):
```
parList([]), entail_all(align).   % similarly: entail_some(align, 1-200)    
```
or even setting the rule application limit (RAL) in order to stop a tableau after the rule application limit is reached.
The default RAL is 400.  
```
parList([ral(50)]), entail_all(align).   % or combine it with parallel proving
```
This command takes ca. 30 seconds to judge 500 SICK problems for a 2.7GHz CPU.


### Obtaining Lambda Logical Forms

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


## Detailed Usage


### More instructions comming soon

## References

1. R. Muskens (2010): [An Analytic Tableau System for Natural Logic](http://link.springer.com/chapter/10.1007/978-3-642-14287-1_11). LNCS, Vol. 6042, Springer.

   `Proposes to use a tableau system for natural logic`

1. L. Abzianidze (2016): [Natural Solution to FraCaS Entailment Problems](https://aclweb.org/anthology/S/S16/S16-2007.pdf). *SEM.
2. L. Abzianidze (2015): [A Tableau Prover for Natural Logic and Language](http://www.aclweb.org/anthology/D15-1296.pdf). EMNLP.

   `Describes the theprem prover LangPro and reports its performance on the SICK and FraCaS datasets`

4. M. Lewis & M. Steedman (2014): A* CCG Parsing with a Supertag-factored Model. EMNLP.
6. M. Honnibal, J. R. Curran, and J. Bos (2010): Rebanking CCGbank for Improved NP Interpretation. ACL (48).
7. S. Clark and J. R. Curran (2007): Wide-Coverage Efficient Statistical Parsing with CCG and Log-Linear Models. Computational Linguistics, 33(4).

   `Describes EasyCCG and C&C parsers and their statistical models` 
   
8. Ch. Fellbaum eds. (1998): WordNet: an Electronic Lexical Database. MIT press.

   `WordNet which is used as a lexical knowledge database in the prover`

9. Cooper,  R.,  Crouch,  D.,  Eijck,  J.  V.,  Fox,  C.,  Genabith,  J.  V.,  Jaspars,  J.,  Kamp,  H., Milward, D., Pinkal, M., Poesio, M., Pulman, S., Briscoe, T., Maier, H., and Konrad, K. (1996). FraCaS: A Framework for Computational Semantics. Deliverable D16.
9. The FraCaS problems converted in [xml](https://nlp.stanford.edu/~wcmac/downloads/fracas.xml) by B. MacCartney.
9. Marelli,  M.,  Menini,  S.,  Baroni,  M.,  Bentivogli,  L.,  Bernardi,  R.,  and  Zamparelli,  R. (2014b).  A sick cure for the evaluation of compositional distributional semantic models. LREC'14.

   `The FraCaS and SICK textual entailment datasets which are use for evaluating the theorem prover`

