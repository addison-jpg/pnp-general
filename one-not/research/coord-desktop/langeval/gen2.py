import random, sys
random.seed(1)
n=9; G=60; K=int(sys.argv[1])
full=(1<<(1<<n))-1
def var(i):
    v=0
    for r in range(1<<n):
        if (r>>i)&1: v|=1<<r
    return v
out=[]
for _ in range(K):
    w=[var(i) for i in range(n)]; c=0
    for g in range(G):
        op=random.randrange(4); a=random.randrange(len(w)); b=random.randrange(len(w))
        x,y=w[a],w[b]
        w.append([x&y,x|y,full^x,x^y][op]); c|=((op<<14)|(a<<7)|b)<<(16*g)
    out.append((c,w[-1]))
print("import Packed\nnamespace LE")
print("def corpus : List (Nat × Nat) := [")
print(",\n".join(f"  ({c}, {t})" for c,t in out))
print("]")
print("theorem corpus_ok : checkAll 9 60 corpus = true := by decide +kernel")
print("#print axioms corpus_ok\nend LE")
