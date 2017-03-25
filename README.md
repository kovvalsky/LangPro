# LangPro: Natural Language Theorem Prover
LangPro is a tableau-based theorem prover for natural logic and language.
See the [online demo](http://naturallogic.pro/langpro).

Given a set of premises and a hypothesis in natural language, LangPro tries to find out semantic relation between them: `entailment`, `contradiction` or `neutral`.  
For this, LangPro needs CCG (Combinatory Categorial Grammar) derivations of the linguistic expressions in order to obtain Lambda Logical Forms (LLFs) from them via the LLFgen (LLF generator) component. The architecture is depicted below: 
```
____________    ________             ___________      ________________________    __________ 
|Premises &|    | CCG  | derivations |   LLF   | LLFs |Tableau Theorem Prover|    |Semantic|
|Hypothesis|--->|Parser|------------>|Generator|----->|  for Natural Logic   |--->|relation|
‾‾‾‾‾‾‾‾‾‾‾‾    ‾‾‾‾‾‾‾‾             ‾‾‾‾‾‾‾‾‾‾‾      ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾    ‾‾‾‾‾‾‾‾‾‾ 
```


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
If you prefer an HTML or XML representation of the proof, add the `xml` parameter before `gentail/1`:
```
parList('xml'), gentail(211).
```
This creates `xml/tableau-211-yes-no_align.xml` (and `xml/tableau-211-yes-no_align.html` from the latter via `xsltproc`) where the name stands for a tableau for problem-211 to verify entailment (i.e. yes) with no alignment techniques used.
If you want to force the alignment of LLFs, run:
```
gentail(align, 211).       % gentail(211) is the same as gentail(no_align, 211)
```
If you want to get both tableaux for entailment (yes) and contradiction (no) checks, run 
```
gentail_no_answer(211).    % or gentail_no_answer(align, 211) to force alignment of LLFs
```
Be aware not all IDs have corresponding problems in SICK-trial as it is just a portion of SICK. 
You can try: 4, 24, 105, 116, 119, 185, 197, ... 
In order to run the prover on several problems without GUI, by listing them or giving an interval, try:
```
entail_some([4, 24, 105, 116, 119, 185, 197, 211]).
```
or
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
It will take some time. If you want to terminate the run, type `Ctrl+C` and then press `a` for abort.


### Obtaining Lambda Logical Forms

In case you are interested in logical forms used by the prover, you can obtain them from CCG derivations.
After you get into the prolog environment by:
```
swipl -f main.pl -l ccg_sen_d/SICK_trial_ccg.pl ccg_sen_d/SICK_trial_sen.pl
```
You can obtain LLFs in XML and HTML formats by running:   
```
xml_probs_llfs([4,24,211], 'My_LLFs').    % or xml_probs_llfs([4,24,211]) that sets 'RTE_LLF' as a file name 
```
This will create `xml/My_LLFs.xml` and `xml/My_LLFs.html` files which contain a CCG (derivation) tree, a CCG term, a corrected CCG term and the first LLF (1LLF) for each sentence of the RTE problems [4,24,211].
You can get these quadruples of terms according to the sentence IDs too:  
```
xml_senIDs_llfs(1-6, 'My_LLFs').    % or xml_senIDs_llfs([1,2,3,4,5,6], 'My_LLFs') or even omitting the file name 
```
Because the first six sentences coincide the sentences of the first three RTE problems in the RTE dataset (i.e. two sentences per problem).
To get CCG trees, CCG terms, corrected CCG terms and 1LLFs for all sentences in the dataset, use:
```
xml_senIDs_llfs(_, 'All_LLFs').
```


## Detailed Usage


### More instructions comming soon
