Peregrine commands

```
r=50; c=20; name=rEFF_r${r}_c${c}; sbatch --partition=short --time=30:00 --cpus-per-task=$c --job-name=$name  --output=peregrine/$name.out  peregrine/produce.sh "-d -b"  "results/starSEM_2020/CV-3/ccg/train_trial/al,ch,r$r,w3,-k,c$c_ab,ch,cKB,cT,p123.log"
```
