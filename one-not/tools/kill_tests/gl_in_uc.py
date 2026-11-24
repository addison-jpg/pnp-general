# Menu-decision check (13:30 UTC, 2026-11-24): are the gates of front A2's graph-heavy constructions G1 and GL
# (one-not/SYNTHESIS-one-not.md section 6) members of the one-face count set UC(emptyset, Q) of mu_light.py?
# Graph system = every set a pair. Q = points fixed to 1, v alive and heavy (h(Q+e_v) = 1), N = alive neighbours of v.
# Lifted wire value at (x, y) = table of C_y at x (the NOT wire is y). For a pair the class of a lifted test system
# (zero point, two atoms) is ONE gate: the first wire that is 0 at the zero point and 1 at both atoms (an OR gate).
#  GL, edge {v,a}: zero (Q + N - a, y_a), atoms (Q+e_v, 0), (Q+e_a, t_a), t_a = NOT h(Q+e_a);
#      y_a = 1 if C_1(o_va)(Q + N - a) = 0 (valid), else y_a = 0 (always valid). Both valid y are also reported.
#      "GL applies" at (Q, v): at most one LIGHT neighbour a is forced to y_a = 0 (SYNTHESIS 6.1).
#  G1, edge {v,a}: world 0, zero top_va, atoms Q+e_v and (a heavy: Q+e_a; a light: X+e_a, X = V - v - light nbrs);
#      applies if h(X+e_a) = 1 for every light neighbour a.
# Run: python3 -I one-not/tools/kill_tests/gl_in_uc.py one-not 9
import sys, os, itertools, collections, functools, random
ROOT=sys.argv[1] if len(sys.argv)>1 else 'one-not'; NMAX=int(sys.argv[2]) if len(sys.argv)>2 else 9
sys.argv=['x',ROOT,str(NMAX)]
here=os.path.dirname(os.path.abspath(__file__))
src=open(os.path.join(here,'canon.py')).read(); exec(src[:src.index("st=collections.Counter()")])
src=open(os.path.join(here,'mu_light.py')).read(); exec(src[src.index("def mk("):src.index("random.seed(1)")])
def first(c,W1,zero,atoms):
    # wires as (table index); point = (x, y); value = table_y >> x
    T=(c['W0'],W1); n=c['n']
    for i in range(n,len(W1)):
        if not (T[zero[1]][i]>>zero[0])&1 and all((T[y][i]>>x)&1 for x,y in atoms): return i
    return None
st=collections.Counter(); ex={}
def note(k,item):
    if k not in ex or item<ex[k]: ex[k]=item
for name,n,S,G,outs in circuits():
    if n>NMAX or sum(1 for g in G if g[0]=='not')!=1 or len(S)<2: continue
    if any(len(R)!=2 for R in S) or len({frozenset(R) for R in S})!=len(S): continue
    c=mk(name,n,S,G,outs)
    if not c: continue
    W1=tables(n,G,1); W0=c['W0']; h=c['h']; hb=lambda x:(h>>x)&1; st['graph circuits']+=1
    out={frozenset(R):o for R,o in zip(S,outs)}; ALL=(1<<n)-1
    for Q in range(1<<n):
        al=[R for R in S if not any(Q>>u&1 for u in R)]
        if not al: continue
        U=None
        for v in sorted({u for R in al for u in R}):
            if not hb(Q|1<<v): continue
            N=[u for R in al if v in R for u in R if u!=v]; Nm=sum(1<<u for u in N)
            if U is None: U=UC(c,0,Q)
            st['heavy (Q,v) instances']+=1; size=(n,len(G),bin(Q).count('1'))
            light=[a for a in N if not hb(Q|1<<a)]
            ucgain=len(U-UC(c,0,Q|1<<v))>=len(N); st['heavy (Q,v): UC gain >= deg(v)']+=ucgain; miss=False
            # ---- GL
            rows=[]; forced0=0
            for a in N:
                Z=Q|(Nm&~(1<<a)); o=out[frozenset((v,a))]; t=0 if hb(Q|1<<a) else 1
                assert not (W0[o]>>Z)&1
                y1ok=not (W1[o]>>Z)&1; ya=1 if y1ok else 0
                if not y1ok and t: forced0+=1
                gs={y:first(c,W1,(Z,y),[(Q|1<<v,0),(Q|1<<a,t)]) for y in ((0,1) if y1ok else (0,))}
                rows.append((a,t,ya,gs))
            applies=forced0<=1; st['GL applies']+=applies; st['GL does not apply']+=(not applies)
            pre='GL' if applies else 'GL(n/a)'
            chosen=[gs[ya] for a,t,ya,gs in rows]
            if applies and len(set(chosen))<len(chosen): st['GL applies but gates NOT distinct']+=1; note('GL not distinct',(size,name,Q,v))
            for a,t,ya,gs in rows:
                g=gs[ya]; assert g is not None and G[g-n][0]=='or'
                kind='%s gate, a %s, y_a=%d'%(pre,'light' if t else 'heavy',ya)
                st[kind+': checked']+=1; st[kind+': in UC']+=(g in U)
                if g not in U: note(kind+' NOT in UC',(size,name,Q,v,a,g)); miss=True
                if applies:
                    st['GL gates checked']+=1; st['GL gates in UC']+=(g in U)
                    for y,gg in gs.items():
                        if y!=ya: st['GL alt y=%d gate: checked'%y]+=1; st['GL alt y=%d gate: in UC'%y]+=(gg in U)
            if miss: st['instances with a GL gate outside UC']+=1; st['  of these: UC gain >= deg(v) still holds']+=ucgain
            # ---- G1
            X=ALL&~(1<<v)&~sum(1<<a for a in light)
            if all(hb(X|1<<a) for a in light):
                st['G1 applies']+=1; gl=[]
                for a in N:
                    top=ALL&~(1<<v)&~(1<<a); ma=(X if a in light else Q)|1<<a
                    g=first(c,W1,(top,0),[(Q|1<<v,0),(ma,0)]); assert g is not None
                    gl.append(g); st['G1 gates checked']+=1; st['G1 gates in UC']+=(g in U)
                    if g not in U: note('G1 gate NOT in UC',(size,name,Q,v,a,g))
                if len(set(gl))<len(gl): st['G1 applies but gates NOT distinct']+=1
            else: st['G1 does not apply']+=1; st['  G1 does not apply and a GL gate is outside UC']+=miss
            if miss and all(hb(X|1<<a) for a in light): st['  GL gate outside UC but G1 applies (all G1 gates in UC)']+=1
            st['neither G1 nor GL applies']+=(not applies and not all(hb(X|1<<a) for a in light))
for k,v in sorted(st.items()): print('%-52s %d'%(k,v))
for k,v in sorted(ex.items()): print('SMALLEST',k,v)
# ---------------- Part 2: exact liftMenu_Q on graph systems (pairs), light-case gain test ----------------
# For a pair R the lifted test systems are (zeta, q, q') in the lifted cube with o(zeta)=0, o(q)=o(q')=1, q AND q' <= zeta
# (Lean LTSValid), all x-parts ⊇ Q; the class is the first wire that is 0 at zeta and 1 at q and q'. Listed exhaustively,
# so F(Q) = union over alive edges is EXACT. (Sets of size k >= 3 need (2^(n+1-|Q|))^(k+1) systems each: not listed.)
def lifted(c,W1):
    n=c['n']; P=1<<n; return [W0i|(W1i<<P) for W0i,W1i in zip(c['W0'],W1)]   # point index = x | y<<n
def menuF(c,T,Q,al,out,cache):
    if Q in cache: return cache[Q]
    n=c['n']; NP=1<<(n+1); pts=[p for p in range(NP) if (p&Q)==Q]; sup=sum(1<<p for p in pts); F=set()
    yw=[i for i,g in enumerate(c['G']) if g[0]=='not'][0]+n
    for R in al:
        To=T[out[frozenset(R)]]
        for z in pts:
            if (To>>z)&1: continue
            zw=[(i,T[i]) for i in range(n,len(T)) if not (T[i]>>z)&1]
            for q in pts:
                if not (To>>q)&1: continue
                d=q&~z; cand=To&sup&dis[n][d]; blocked=0
                for i,Ti in zw:
                    if not (Ti>>q)&1: continue
                    if cand&Ti&~blocked: F.add(i)
                    blocked|=Ti
                    if not cand&~blocked: break
    F.discard(yw); cache[Q]=F; return F
dis={}
def mkdis(n):
    NP=1<<(n+1); dis[n]=[sum(1<<p for p in range(NP) if not p&d) for d in range(NP)]
st=collections.Counter(); ex={}
for name,n,S,G,outs in circuits():
    if n>7 or sum(1 for g in G if g[0]=='not')!=1 or len(S)<2: continue
    if any(len(R)!=2 for R in S) or len({frozenset(R) for R in S})!=len(S): continue
    c=mk(name,n,S,G,outs)
    if not c: continue
    if n not in dis: mkdis(n)
    W1=tables(n,G,1); T=lifted(c,W1); h=c['h']; out={frozenset(R):o for R,o in zip(S,outs)}; cache={}; st['graph circuits']+=1
    # the y wire (NOT gate) is a lifted INPUT, never a class member; T[yw] must be the y coordinate
    aliveQ=lambda Q:[R for R in S if not any(Q>>u&1 for u in R)]
    for Q in range(1<<n):
        al=aliveQ(Q)
        if not al: continue
        P=sorted({u for R in al for u in R}); F=menuF(c,T,Q,al,out,cache); U=UC(c,0,Q)
        st['(C,Q) instances']+=1; st['MUL_Q holds (|F(Q)| >= base)']+=(len(F)>=len(al)); st['UC(Q) inside F(Q)']+=(U<=F)
        if any((h>>(Q|1<<v))&1 for v in P): continue
        st['light instances']+=1
        okF={}; okU={}
        for v in P:
            deg=sum(1 for R in al if v in R); Q2=Q|1<<v
            okF[v]=len(F-menuF(c,T,Q2,aliveQ(Q2),out,cache))>=deg; okU[v]=len(U-UC(c,0,Q2))>=deg
        st['light: liftMenu gain at SOME v']+=any(okF.values()); st['light: liftMenu gain at EVERY v']+=all(okF.values())
        st['light: UC gain at SOME v']+=any(okU.values()); st['light: UC gain at EVERY v']+=all(okU.values())
        if not any(okF.values()): note('light liftMenu gain FAILS',((n,len(G),bin(Q).count('1')),name,Q))
        if not any(okU.values()): note('light UC gain FAILS',((n,len(G),bin(Q).count('1')),name,Q))
print('--- part 2: exact liftMenu_Q, graph systems, n <= 7')
for k,v in sorted(st.items()): print('%-52s %d'%(k,v))
for k,v in sorted(ex.items()): print('SMALLEST',k,v)
