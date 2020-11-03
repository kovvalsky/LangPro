The directory contains predictions on SICK-test reported by [Abzianidze (2015)](https://www.aclweb.org/anthology/D15-1296/).  
Predictions are based on LangPro that uses max 800 rule applications and two CCG parsers (C&C and EasyCCG) separately.  
The hybrid predictions are aggregations of the predictions based on the C&C and EasyCCG parsers.

`Tested for 0054975c88a5ae1aa07c1d12800ee55108aec015`
```
python3 python/evaluate.py --sys results/EMNLP_2015/sick_test_candc_800.ans  results/EMNLP_2015/sick_test_easyccg_800.ans --gld SICK_dataset/SICK_test_annotated.txt 
2 systems' output read
results/EMNLP_2015/sick_test_candc_800.ans
---------------------------------------------------------------
                     ENTAILMENT   CONTRADICTION         NEUTRAL
---------------------------------------------------------------
     ENTAILMENT             713               0             701 
  CONTRADICTION               1             455             264 
        NEUTRAL              18               5            2770 
---------------------------------------------------------------
accuracy    : 79.93%
precision   : 97.99%
recall      : 54.73%
results/EMNLP_2015/sick_test_easyccg_800.ans
---------------------------------------------------------------
                     ENTAILMENT   CONTRADICTION         NEUTRAL
---------------------------------------------------------------
     ENTAILMENT             666               0             748 
  CONTRADICTION               1             458             261 
        NEUTRAL              17               5            2771 
---------------------------------------------------------------
accuracy    : 79.05%
precision   : 97.99%
recall      : 52.67%

python3 python/evaluate.py --sys results/EMNLP_2015/sick_test_candc_800.ans  results/EMNLP_2015/sick_test_easyccg_800.ans --gld SICK_dataset/SICK_test_annotated.txt  --hybrid
2 systems' output read
**********************Hybrid**********************
---------------------------------------------------------------
                     ENTAILMENT   CONTRADICTION         NEUTRAL
---------------------------------------------------------------
     ENTAILMENT             760               0             654 
  CONTRADICTION               1             480             239 
        NEUTRAL              20               5            2768 
---------------------------------------------------------------
accuracy    : 81.35%
precision   : 97.95%
recall      : 58.11%
```
