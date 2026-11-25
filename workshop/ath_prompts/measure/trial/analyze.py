"""Exact sign test / McNemar on paired task outcomes. Usage: analyze.py results.json"""
import json,sys
from math import comb
from statistics import mean,median
R=json.load(open(sys.argv[1])); rows=R["rows"]
def binom2(b,c):
    n=b+c
    if n==0: return 1.0
    k=min(b,c); return min(1.0,2*sum(comb(n,i) for i in range(k+1))/2**n)
def get(run):
    d={}
    for r in rows:
        if r["run"]==run: d.setdefault(r["task"],{})[r["register"]]=r
    return d
print("model",R["model"],"seconds",R["seconds"])
for run in ["greedy","s0","s1","s2"]:
    d=get(run); I=sum(v["informal"]["ok"] for v in d.values()); F=sum(v["formal"]["ok"] for v in d.values())
    b=sum(v["informal"]["ok"] and not v["formal"]["ok"] for v in d.values()); c=sum(v["formal"]["ok"] and not v["informal"]["ok"] for v in d.values())
    li=[v["informal"]["out_tokens"] for v in d.values()]; lf=[v["formal"]["out_tokens"] for v in d.values()]
    print(f"{run}: informal {I}/30 formal {F}/30 | informal-only {b} formal-only {c} exact McNemar p={binom2(b,c):.4f} | out tokens mean inf {mean(li):.1f} form {mean(lf):.1f}, median {median(li)} {median(lf)}; pairs inf shorter {sum(x<y for x,y in zip(li,lf))}, longer {sum(x>y for x,y in zip(li,lf))}")
# pooled over 3 sampled runs: per-task success count 0..3 each register, sign test on task-level differences
d=[get(s) for s in ["s0","s1","s2"]]
tasks=sorted(d[0]); pos=neg=0
for t in tasks:
    di=sum(x[t]["informal"]["ok"] for x in d)-sum(x[t]["formal"]["ok"] for x in d)
    pos+=di>0; neg+=di<0
print(f"sampled pooled per task: informal better {pos}, formal better {neg}, ties {30-pos-neg}, exact sign p={binom2(pos,neg):.4f}")
rs=[sum(x[t][r]["ok"] for t in tasks) for x in d for r in ("informal",)]; fs=[sum(x[t]["formal"]["ok"] for t in tasks) for x in d]
print("sampled run totals informal",rs,"formal",fs)
ai=[v["ask_tokens"] for v in get("greedy").values() for k,v in [("i",v["informal"])]]
af=[v["formal"]["ask_tokens"] for v in get("greedy").values()]
print(f"ask tokens mean informal {mean(ai):.1f} formal {mean(af):.1f}")
print("\nper-task (greedy I/F, sampled I/F counts of 3):")
g=get("greedy")
for t in tasks:
    print(f"| {t} | {int(g[t]['informal']['ok'])} | {int(g[t]['formal']['ok'])} | {sum(x[t]['informal']['ok'] for x in d)} | {sum(x[t]['formal']['ok'] for x in d)} | {g[t]['informal']['out_tokens']} | {g[t]['formal']['out_tokens']} |")
