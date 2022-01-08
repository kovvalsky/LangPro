# [LangPro](https://github.com/kovvalsky/LangPro): Natural [Lang](https://github.com/kovvalsky/LangPro)uage Theorem [Pro](https://github.com/kovvalsky/LangPro)ver
LangPro is a tableau-based theorem prover for natural logic and language.
See the [online demo](https://naturallogic.pro/LangPro/) (not the latest version).
<!-- (http://naturallogic.pro/langpro). -->

Given a set of premises and a hypothesis in natural language, LangPro tries to find out semantic relation between them: `entailment` (i.e. `yes`), `contradiction` (i.e. `no`) or `neutral` (i.e. `unknown`).  
For this, LangPro needs CCG (Combinatory Categorial Grammar) derivations of the linguistic expressions in order to obtain Lambda Logical Forms (LLFs) from them via the LLFgen (LLF generator) component. The architecture is depicted below:
```
____________    ________             ___________      ________________________    __________
|Premises &|    | CCG  | derivations |   LLF   | LLFs |Tableau Theorem Prover|    |Semantic|
|Hypothesis|--->|Parser|------------>|Generator|----->|  for Natural Logic   |--->|relation|
‾‾‾‾‾‾‾‾‾‾‾‾    ‾‾‾‾‾‾‾‾             ‾‾‾‾‾‾‾‾‾‾‾      ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾    ‾‾‾‾‾‾‾‾‾‾
```
If you use the theorem prover, please cite [Abzianidze (2017)](https://www.aclweb.org/anthology/D17-2020):
```
@inproceedings{abzianidze-2017-langpro,
    title = "{L}ang{P}ro: Natural Language Theorem Prover",
    author = "Abzianidze, Lasha",
    booktitle = "Proceedings of the 2017 Conference on Empirical Methods in Natural Language Processing: System Demonstrations",
    month = sep,
    year = "2017",
    address = "Copenhagen, Denmark",
    publisher = "Association for Computational Linguistics",
    url = "https://www.aclweb.org/anthology/D17-2020",
    doi = "10.18653/v1/D17-2020",
    pages = "115--120"
}
```

For the manual on how to use the prover or how to obtain reported results, consult the [wiki](https://github.com/kovvalsky/LangPro/wiki).

# Quick links to the [wiki pages](https://github.com/kovvalsky/LangPro/wiki):

* [Using the prover](https://github.com/kovvalsky/LangPro/wiki/Using-the-prover)
* [Producing LLFs](https://github.com/kovvalsky/LangPro/wiki/Producing-LLFs)
* [Learning as abduction](https://github.com/kovvalsky/LangPro/wiki/Learning-as-abduction)
* [References](https://github.com/kovvalsky/LangPro/wiki/References)
