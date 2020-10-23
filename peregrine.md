Peregrine commands

*Cross-validation*
```
r=50; c=20; name=rEFF_r${r}_c${c}; sbatch --partition=short --time=30:00 --cpus-per-task=$c --job-name=$name  --output=peregrine/$name.out  peregrine/produce.sh "-d -b"  "results/starSEM_2020/CV-3/ccg/train_trial/al,ch,r$r,w3,-k,c$c_ab,ch,cKB,cT,p123.log"
```

```
results/starSEM_2020/CV-3/ccg/train_trial/al,ch,r800,w3,-k,c20_ab,ch,cKB,cT,p123.log
results/starSEM_2020/CV-3/ccg/train_trial/al,ch,r50,w3,-k,c20_ab,ch,cKB,cT,p123.log
```


*Ablation*
```
results/starSEM_2020/CV-3/ccg/train_trial/al,ch,r50,w3,-k,c20_ab,cKB,cT,p123.log
results/starSEM_2020/CV-3/ccg/train_trial/al,ch,r50,w3,-k,c20_ab,ch,cKB,p123.log
results/starSEM_2020/CV-3/ccg/train_trial/al,ch,r50,w3,-k,c20_ab,ch,cT,p123.log
results/starSEM_2020/CV-3/ccg/train_trial/al,ch,r50,-k,-w,c20_ab,ch,cKB,cT,p123.log
results/starSEM_2020/CV-3/ccg/train_trial/al,ch,r50,w3,c20_ab,ch,cKB,cT,p123.log
results/starSEM_2020/CV-3/ccg/train_trial/al,ch,r50,w3,-k,c20_ab,ch,cKB,cT,p12.log
results/starSEM_2020/CV-3/ccg/train_trial/al,ch,r50,w3,-k,c20_ab,ch,cKB,cT,p1.log
```

*Train & evaluate*
```
results/starSEM_2020/TE/ccg/TD_E/al,ch,r800,w3,-k,c20_ab,ch,cKB,cT,p123.log
results/starSEM_2020/TE/eccg/TD_E/al,ch,r800,w3,-k,c20_ab,ch,cKB,cT,p123.log
# results/starSEM_2020/ccg_sen/SICK_train_trial_sen.pl
# results/starSEM_2020/ccg_sen/SICK_train_trial_depccg.trihf.sep.pl
results/starSEM_2020/TE/depccg.trihf.sep/TD_E/al,ch,r800,w3,-k,c20_ab,ch,cKB,cT,p123.log

results/starSEM_2020/TE/ccg/TD_E/al,ch,r50,w3,-k,c20_ab,ch,cKB,cT,p123.log
results/starSEM_2020/TE/eccg/TD_E/al,ch,r50,w3,-k,c20_ab,ch,cKB,cT,p123.log
results/starSEM_2020/TE/depccg.trihf.sep/TD_E/al,ch,r50,w3,-k,c20_ab,ch,cKB,cT,p123.log
```

