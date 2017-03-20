# LangPro: Natural Language Theorem Prover
LangPro is a tableau-based theorem prover for natural logic and language.
See the [online demo](http://naturallogic.pro/langpro).

Given a set of premises and a hypothesis in natural languge, LangPro tries to find out semantic relation between them: `entailment`, `contradiction` or `neutral`.  
For this, LangPro needs CCG (Combinatory Categorial Grammar) derivations of the linguistic expressions in order to obtain Lambda Logical Forms (LLFs) from them via the LLFgen (LLF generator) component. The architecture is depicetd below: 
```
____________    ________             ___________      ________________________    __________ 
|Premises &|    | CCG  | derivations |   LLF   | LLFs |Tableau Theorem Prover|    |Semantic|
|Hypothesis|--->|Parser|------------>|Generator|----->|  for Natural Logic   |--->|relation|
‾‾‾‾‾‾‾‾‾‾‾‾    ‾‾‾‾‾‾‾‾             ‾‾‾‾‾‾‾‾‾‾‾      ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾    ‾‾‾‾‾‾‾‾‾‾ 
```


## Quick Usage
You will need only [SWI-Prolog](http://www.swi-prolog.org) to run the prover.
Go to the main directory and run the following command in order to run the prover on the trial portion of the SICK dataset:
```
swipl -f main.pl -l ccg_sen_d/SICK_trial_ccg.pl ccg_sen_d/SICK_trial_sen.pl
```
`FILE_ccg.pl` contains CCG derivations by the C&C CCG parser while `FILE_sen.pl` lists RTE problems. 
Now already in the Prolog environment, run 
```
gentail(211).
```
This will trigger a tableau proof for the SICK-211 problem. Be aware not all IDs have corresponding problems in SICK-trial as it is just a portion of SICK. You can try: 4, 24, 105, 116, 119, 185, 197, ... 

In order to run the prover on several problems, by listing them or giving an interval, try:
```
entail_some([4, 24, 105, 116, 119, 185, 197]).
```
or
```
entail_some(1-200).
```
These commands will print the problem ID, the [gold answer], the prover's judgment and tableau status (open/closed, terminated/limited, #rule applications). Something like this:
```
   4:      [no],      no,  closed, 17         
  24: [unknown], unknown,    open, 'Ter',175  
 105: [unknown], unknown,    open, 'Ter',56   
 116: [unknown], unknown,    open, 'Ter',27   
 119: [unknown], unknown,    open, 'Ter',205  
 185: [unknown], unknown,    open, 'Ter',71   
 197: [unknown], unknown,    open, 'Ter',68 
```
Run the prover on all the problems of SICK-trial by:
```
entail_all.
```
It will take some time. If you want to terminate the run, type `Ctrl+C` and then press `a` for abort.

## Detailed Usage


### More instructions comming soon
