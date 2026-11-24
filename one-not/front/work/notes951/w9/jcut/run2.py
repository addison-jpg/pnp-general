from cls import *
A=allcirc()
short=0; inter=0; interN=0; tot=0; ex=[]
kinds={}
for nm,c in A:
    T=TT(c); sets=c['sets']; dem=[len(S)-1 for S in sets]
    C={b:classes(T,b) for b in ('real',0,1)}
    U=[set().union(*[C[b][k][i] for b in C for k in (0,1)]) for i in range(len(sets))]
    for i in range(len(sets)):
        tot+=1
        if len(U[i])<dem[i]: short+=1
    for i in range(len(sets)):
        for j in range(i+1,len(sets)):
            I=U[i]&U[j]
            if I:
                inter+=1
                for g in I:
                    key=tuple(sorted([ (str(b),k) for b in C for k in (0,1) if g in C[b][k][i]]))+('|',)+tuple(sorted([ (str(b),k) for b in C for k in (0,1) if g in C[b][k][j]]))
                    kinds[key]=kinds.get(key,0)+1
                    if g==T.Ni: interN+=1
                if len(ex)<5: ex.append((nm,i,j,sorted(I)))
print('sets',tot,'short',short,'intersecting pairs',inter,'N in inter',interN)
for k,v in sorted(kinds.items(),key=lambda t:-t[1])[:30]: print(v,k)
print(ex)
