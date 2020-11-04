The directory should contain three files corresponding to the train, trial, and test parts of SICK.
```
$ wc -l SICK_dataset/SICK_t*
   4928 SICK_dataset/SICK_test_annotated.txt
   4501 SICK_dataset/SICK_train.txt
    501 SICK_dataset/SICK_trial.txt
   9930 total

```

These files can be obtained from the [SemEval-14 task 1](https://alt.qcri.org/semeval2014/task1/index.php?id=data-and-tools):
* [TRIAL DATA](http://alt.qcri.org/semeval2014/task1/data/uploads/sick_trial.zip),
* [TRAINING DATA](http://alt.qcri.org/semeval2014/task1/data/uploads/sick_train.zip),
* [TEST DATA (including gold scores)](http://alt.qcri.org/semeval2014/task1/data/uploads/sick_test_annotated.zip)

Note that files obtained from the original SICK [page](http://marcobaroni.org/composes/sick.html) contain fewer problems than the one distributed via the SemEval task
