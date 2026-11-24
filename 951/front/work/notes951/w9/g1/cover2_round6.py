# cover2: coverage checker.  Sound over-approximation of "a minimal-counterexample scenario exists"; covered(system)=True means
# s>=base is PROVED for the system (given small3, R0, and the lemmas of g1_fable.md / pairrule_log.md).
#
# A scenario = (sigma, B, peeling order of V1 = points - B), checked by DFS over orders with capacities.
# Rule letters (string `rules`):
#   (i),(ii)  always on: every set S through a V1 point v meets A_j = placed points (G1.3 (i)); a singleton T={u} needs
#             d(u) >= 3+sigma (u in B) / 2+sigma (u in V1)                                  (G1.3 (ii))
#   '2'  capacity (ii'), G1.6: #singleton users of u <= d(u)-sigma-2 (u in B) / d(u)-sigma-1 (u in V1)
#   '4'  tight-pair lemma G1.7 steps 1,2 (sigma=1, v of degree 2): a tight pair T={a,b} must consist of B-points; not both sets of v
#   '5'  G1.7 step 3: a known-tight B-point is in at most one tight pair
#   'p'  [ROUND 4, pair lemma G1.9 in counting form = PAIR-N2, see pairrule_log.md section 1]
#        For every point u with l(u) lines (|S|>=3) and p(u) pair-sets {u,w}:
#            nonpair(u) + kL(u) <= l(u) - sigma,     nonpair(u) >= 1,
#        nonpair(u) = #readers of x_u other than the gates x_u|x_w (w a pair-partner of u), kL(u) = #V1 points that use u as
#        singleton through a LINE.  Proof: under x_u:=0, besides the readers of x_u, for every pair-partner w the LOWEST gate
#        whose restriction is x_w dies; it is a reader of x_u iff it is the gate x_u|x_w (G1.9 argument); the r_v of the
#        line-singleton users die and are non-readers (G1.3 (ii)); all these are distinct; N2 gives dead0(u) <= d(u)-sigma.
#        nonpair(u) >= 1: if all readers of x_u were pair-gates x_u|x_w, put x_w=1 for those w, all else 0: toggling x_u changes
#        no wire but OR(L) for a line L through u.  Pair-gates x_u|x_w cannot exist if u or w is in V1 (P2).  Encoded as:
#          sigma <= min_u l(u) - 1;  B needs l >= 1+sigma;
#          capL(u) = l(u)-sigma-1 (u in V1),  l(u)-sigma-2+min(1,pB(u)) (u in B; pB = #pair-partners in B; readers>=2);
#          singleton uses through PAIR-sets are free (the dying gate is already the one counted for that pair).
#        Equality case = G1.9: a tight point has all its pair-gates and exactly l-sigma non-pair readers.
#   'q'  [ROUND 4, G1.7 step 1 + G1.9, pairrule_log.md section 2] sigma=1, v tight (degree 2), T_i = {a,b} tight pair, a in B tight
#        (d(a)=3) with ONE pair-set {a,w}: readers(a) = {x_a|x_w (G1.9), g1 = x_a|x_b (G1.7)}, g1 read only by c_v <= OR(T_o)
#        (T_o = the other T of v).  At z = e_w vs z+e_a only g1 changes among the readers of x_a, and c_v = 0 at both unless
#        w in T_o; but OR(S_i)(z)=0 != 1 = OR(S_i)(z+e_a).  So w must lie in T_o, else the scenario is impossible.
#   'r'  [ROUND 4, c-death + relative AL, pairrule_log.md section 2b; needs 'p'] Let U(u) = V1 points v using u as singleton
#        (through a line OR a pair-set S0(v)); k(u)=|U(u)|.  Under x_u:=0 also c_v dies (it becomes constant); it is either a
#        reader of x_u or one MORE death (distinct from all counted ones: it restricts to a constant).
#        (R2) u in V1: c_v is never the reader r_u of x_u [r_u = x_u&c_u has r_u(e_u)=c_u(0)=1 > c_v(e_u)=0; x_u|c_u is not
#             <= x_u; AND-type r_v needs c_v=1 on x_u=0, impossible for r_u].  So k(u)>=1 => 1+kL(u)+1 <= l(u)-sigma.
#        (R3) u in B, all c_v readers of x_u, nonpair(u)=1: then every c_v IS the unique non-pair reader h_u = x_u&y (h_u=N is
#             impossible by monotonicity on Q={x_W=1}, W = partners with pair-gate); at z=1_W toggling x_u must move h_u, so
#             y(z)=1, so c_v(z+e_u)=1 <= OR(T_S'(v))(z+e_u): every other set S' of v has T_S'(v) meeting W (subset of P(u)&B).
#        Encoded: if k(u)>=1:  u in V1: kL(u) <= l-sigma-2;
#                              u in B : kL(u) <= l-sigma-2  or  [pB(u)>=1, kL(u) <= l-sigma-1, every user v satisfies (R3)].
#   'a'  [ROUND 5, P-TIGHT PAIR LEMMA, frontier15_log.md section 1/1b; needs 'p'; sigma=1] u is p-tight iff nonpair(u)=l(u)-sigma
#        (then dead0(u) = readers + lowest pair-gates EXACTLY); capL(u)=0 => p-tight.  v in V1 p-tight (l(v)=2; OR-type reader),
#        T_S(v)={a,b} both p-tight, P(a)&P(b)=empty:  (A0) x_a|x_b exists, read only by c_v;  (A1) a,b in B;  (A2) at most one
#        such pair per v;  (A3') a p-tight B-point a is in at most l(a)-2 such pairs (z = 1_W + sum e_{b_i}: all readers of x_a
#        are 1, a free line through a remains).  Generalises rules 4, 5 and subsumes q.
#   's'  [ROUND 5, absorption at the singleton user, section 2; needs 'r'] any point u used as singleton needs
#        kL(u) <= l(u)-sigma-2: the (R3) mode of rule r is impossible (z = 1 on P(u) and on the line-users: every reader of
#        h_u = x_u&y is 1, but a line through u without users vanishes).
#   'b'  [ROUND 5, BOTTOM LEMMA with pair-gates, section 3; needs 'p'] U-type = B-point with l = sigma+1 (unique non-pair
#        reader h_t = x_t|c_t, relative AL on Q={x_W=1}).  g* = lowest gate among V1-readers and the h_t: its other input is a
#        function of (variables of B\U, pair-gates touching U).  If that forces c == const (V1) resp. c|_Q == 0 and the restriction
#        x_W := 1 kills more than loss(W)-sigma gates (c, h_t, outputs through W, h_w) for every candidate, the scenario dies.
#        Works for V1 = empty.  bottom_rule() below; applied to scenarios surviving the DFS.
#   'n'  [ROUND 6, refined scenarios, frontier15_log.md sections 6-7; needs a, s, b] every B-point gets a class: U (l=sigma+1),
#        T (nonpair = l-sigma, p-tight), M (2 <= nonpair < l-sigma), S (nonpair = 1 with slack); a scenario dies iff every class
#        vector dies.  bottom_rule(cls=...) then uses U' = U+S, Lemma N-O, the equality case (E) (two-sided x_w:=1 / x_w:=0),
#        Lemma-A feeders as pseudo pair-gates (P) and bottom + cascade (K).
# NOTE: with a/s/b/n use greedy='none' (default); the exchange argument for greedy modes was only checked for rules <= 245pqr.
# Peeling DFS: greedy "free moves" are sound (exchange argument, pairrule_log.md section 3): placing a free V1 point v early only
# enlarges other points' T's; the only conceivable harm (a line-singleton T={u} of a later y becoming a forbidden tight pair {u,v})
# needs u tight, and singleton uses of tight u are rejected anyway.  greedy='old' = round-2 code, 'safe' = greedy except in that
# configuration, 'none' = pure DFS with memo (DEFAULT; fast for n<=10).  All three agree on every data set.
import itertools, sys
from cover import norm, degs, delete
RULES_NEW='245pqrasbn'
RULES_OLD='245'
def info(sets):
    d=degs(sets); pts=sorted(d)
    Sv={v:[S for S in sets if v in S] for v in pts}
    l={v:sum(1 for S in Sv[v] if len(S)>=3) for v in pts}
    P={v:frozenset(w for S in Sv[v] if len(S)==2 for w in S if w!=v) for v in pts}
    return d,pts,Sv,l,P
def feasible(sets,verbose=False,rules=RULES_NEW,greedy='none'):
    d,pts,Sv,l,P=info(sets); out=[]
    R2='2' in rules; R4='4' in rules; R5='5' in rules; RP='p' in rules; RQ='q' in rules; RR='r' in rules and RP
    RA='a' in rules and RP
    RS='s' in rules and RR
    RB='b' in rules and RP
    RN='n' in rules and RB and RS and RA
    smax=min(d.values())-1
    if RP: smax=min(smax,min(l.values())-1)          # PAIR-N2: 1 <= nonpair(u) <= l(u)-sigma for every point
    for sigma in range(1,smax+1):
        cand=[v for v in pts if d[v]>=2+sigma and (not RP or l[v]>=1+sigma)]
        for r in range(2,len(cand)+1):               # (B2): |B| >= 2
            for B in itertools.combinations(cand,r):
                Bs=frozenset(B)
                tight=lambda u: (u in Bs and d[u]==2+sigma) or (u not in Bs and d[u]==1+sigma)
                def cap1(u): return (d[u]-sigma-2) if u in Bs else (d[u]-sigma-1)   # (ii') all singleton users
                pB={u:len(P[u]&Bs) for u in pts}
                cls={}                                   # rule n: class of each B-point (U,S,T,M); empty = unrefined
                def capL(u):                             # PAIR-N2, line users
                    if u not in Bs: return l[u]-sigma-1
                    c=cls.get(u)
                    if c is None: return l[u]-sigma-2+min(1,pB[u])
                    return {'U':0,'T':0,'M':l[u]-sigma-2,'S':l[u]-sigma-1}[c]
                if RP and any(capL(u)<0 for u in pts): continue
                seen=set()
                def status(v,placed):
                    """None if not placeable; else dict of consumption"""
                    use={}
                    Ts=[(S&placed)-{v} for S in Sv[v]]
                    for i,(S,T) in enumerate(zip(Sv[v],Ts)):
                        if not T: return None                                     # (i)
                        if len(T)==1:
                            u=next(iter(T))
                            if RP:
                                if len(S)>=3: use[('sL',u)]=use.get(('sL',u),0)+1  # pair-set singleton uses are free under 'p'
                            else: use[('s',u)]=use.get(('s',u),0)+1
                            if RR:                                                  # rule r: record user and (R3) condition
                                use[('k',u)]=use.get(('k',u),0)+1
                                PBu=P[u]&Bs
                                if not all(PBu&Ts[j] for j in range(len(Ts)) if j!=i): use[('wbad',u)]=1
                    if sigma==1 and d[v]==2:
                        tp=[len(T)==2 and all(tight(u) for u in T) for T in Ts]
                        if R4:
                            if all(tp): return None
                            if any(t and any(u not in Bs for u in T) for t,T in zip(tp,Ts)): return None
                        if RQ:
                            for i,(t,T) in enumerate(zip(tp,Ts)):
                                if not t: continue
                                To=Ts[1-i]
                                for a in T:
                                    if a in Bs and len(P[a])==1 and not (P[a]&To): return None
                        if R5:
                            for t,T in zip(tp,Ts):
                                if t:
                                    for u in T: use[('p',u)]=use.get(('p',u),0)+1
                    if RA and sigma==1 and l[v]==2:                                 # rule a (frontier15_log.md section 1)
                        na=0
                        for i,T in enumerate(Ts):
                            if len(T)!=2: continue
                            a,b=tuple(T)
                            if capL(a)==0 and capL(b)==0 and not (P[a]&P[b]):
                                if a not in Bs or b not in Bs: return None             # (A1)
                                na+=1
                                for x in (a,b): use[('a',x)]=use.get(('a',x),0)+1
                        if na>=2: return None                                          # (A2)
                    return use
                def okuse(use,used):
                    for (k,u),c in use.items():
                        tot=used.get((k,u),0)+c
                        if k=='s' and tot>(cap1(u) if R2 else (99 if cap1(u)>=1 else 0)): return False
                        if k=='sL' and tot>capL(u): return False
                        if k=='p' and tot>1: return False
                        if k=='a' and tot>l[u]-sigma-1: return False                 # (A3)
                        if k=='k':                                                  # rule r
                            kL=used.get(('sL',u),0)+use.get(('sL',u),0)
                            wb=used.get(('wbad',u),0)+use.get(('wbad',u),0)
                            if u not in Bs:
                                if kL>l[u]-sigma-2: return False
                            elif not (kL<=l[u]-sigma-2 or (not RS and pB[u]>=1 and kL<=l[u]-sigma-1 and wb==0)): return False
                    return True
                def unsafe(v,placed):
                    # placing free v now could turn some later y's singleton into a forbidden tight pair {u,v}
                    if not (R4 and sigma==1 and d[v]==2): return False
                    for S in Sv[v]:
                        if len(S)<3: continue
                        for y in S:
                            if y!=v and y not in placed and d[y]==2 and len((S&placed)-{y})<=1: return True
                    return False
                def dfs(placed,used):
                    if greedy!='none':
                        ch=True
                        while ch:
                            ch=False
                            for v in pts:
                                if v in placed: continue
                                u=status(v,placed)
                                if u is not None and not u and (greedy=='old' or not unsafe(v,placed)):
                                    placed=placed|{v}; ch=True
                    if len(placed)==len(pts): return True
                    key=(placed,tuple(sorted(used.items())))
                    if key in seen: return False
                    seen.add(key)
                    for v in pts:
                        if v in placed: continue
                        u=status(v,placed)
                        if u is None or not okuse(u,used): continue
                        nu=dict(used)
                        for k,c in u.items(): nu[k]=(1 if k[0]=='wbad' else nu.get(k,0)+c)
                        if dfs(placed|{v},nu): return True
                    return False
                if RN:
                    opts=[]
                    for u in B:
                        m=l[u]-sigma                                   # nonpair(u) in [1,m]
                        if m==1: o=['U']
                        else: o=(['S'] if pB[u]>=1 else [])+(['M'] if m>=3 else [])+['T']
                        opts.append(o)
                    found=False
                    for combo in itertools.product(*opts):
                        cls.clear(); cls.update(zip(B,combo)); seen.clear()
                        if any(capL(u)<0 for u in pts): continue
                        if dfs(Bs,{}) and not bottom_rule(sets,d,pts,Sv,l,P,sigma,Bs,cls=dict(cls)): found=True; break
                    cls.clear()
                    if not found: continue
                    out.append((sigma,B))
                    if not verbose: return out
                elif dfs(Bs,{}):
                    if RB and bottom_rule(sets,d,pts,Sv,l,P,sigma,Bs): continue
                    out.append((sigma,B))
                    if not verbose: return out
    return out
def bottom_rule(sets,d,pts,Sv,l,P,sigma,Bs,explain=None,cls=None):
    """rule b (frontier15_log.md section 3; with cls: refined version of section 6): True iff the scenario is IMPOSSIBLE."""
    if cls is None: cls={t:('U' if l[t]==sigma+1 else 'X') for t in Bs}; refined=False
    else: refined=True
    Ut=set(t for t in Bs if cls[t]=='U'); Sc=set(t for t in Bs if cls[t]=='S')
    U=sorted(Ut|Sc)                                         # U' = points with a unique non-pair reader h_t
    V1=[v for v in pts if v not in Bs]
    if not U and not V1: return False
    Us=set(U); Bl=sorted(Bs); idx={u:i for i,u in enumerate(Bl)}
    pairs0=[tuple(sorted(S)) for S in sets if len(S)==2 and S<=Bs and (S&Us)]
    pp={}                                                   # pseudo pair-gates x_a|x_b from Lemma A (section 7), refined mode only
    if refined and sigma==1:
        V1s=set(V1)
        for v in V1:
            if l[v]!=2: continue
            for S in Sv[v]:
                T=S&Bs
                if len(S)>=3 and (S&V1s)=={v} and len(T)==2:
                    a,b=sorted(T)
                    if cls[a]=='T' and cls[b]=='T' and l[a]==3 and l[b]==3 and not P[a] and not P[b] and a not in pp and b not in pp:
                        pp[a]=b; pp[b]=a; pairs0.append((a,b))
    Np=sorted(Bs-Us-set(pp))
    def keyf(x,prs): return (tuple(x[idx[u]] for u in Np),tuple(x[idx[a]]|x[idx[b]] for a,b in prs))
    X=list(itertools.product((0,1),repeat=len(Bl)))
    wantbad=False
    def realizable(t,W,prs,zsets):
        # every x with x_W=1 is equivalent (same key) to some x'' with x''_W=1 vanishing on one of zsets
        Q=[x for x in X if all(x[idx[w]] for w in W)]
        good=set()
        for x in Q:
            if any(all(x[idx[u]]==0 for u in Z) for Z in zsets): good.add(keyf(x,prs))
        bad=[x for x in Q if keyf(x,prs) not in good]
        return (not bad) if not wantbad else bad
    wantbad=True
    for v in V1:
        bad=realizable(v,(),pairs0,[(S&Bs)-{v} for S in Sv[v]])
        ok=not bad
        if not ok and refined and l[v]==sigma+1:            # bottom + cascade (K): c_v <= x_u, u p-tight, kills c_v and r_v
            pt=[u for u in Bl if cls[u] in 'UT' and v not in P[u]]              # p-tight points, v no pair-partner
            ok=any(all(x[idx[u]] for x in bad) for u in pt)                      # (K): c_v <= x_u
            if not ok and sigma==1:                                             # (K2): c_v <= x_u|x_w, {u,w} a pair-set
                ok=any(u<w and w in P[u] and (d[u]==3 or d[w]==3) and not (P[u]&P[w]) and all(x[idx[u]]|x[idx[w]] for x in bad) for u in pt for w in pt)
        if not ok:
            if explain is not None: explain.append(('V1',v))
            return False
    wantbad=False
    for a in sorted(pp):                                    # g* = second reader g_a = x_a|c_a of a pseudo-pair point
        b=pp[a]
        ok=realizable(a,(b,),pairs0,[(S&Bs)-{a} for S in Sv[a] if b not in S])
        if ok:
            meet=[S for S in sets if b in S]
            ok=4+len(meet)>sum(len(S)-1 for S in meet)-sigma
        if not ok:
            if explain is not None: explain.append(('PP',a))
            return False
    for t in U:
        PB=sorted(P[t]&Bs)
        forced=[w for w in PB if d[w]==2+sigma]             # tight partner => pair-gate exists (G1.9)
        opt=[w for w in PB if w not in forced]
        for r in range(len(opt)+1):
            for extra in itertools.combinations(opt,r):
                W=tuple(forced)+extra
                if not W: continue                          # readers >= 2 and nonpair = 1 => some pair-gate
                ok=True
                if t in Sc and not all(cls[w]=='U' or d[w]==2+sigma for w in W): ok=False   # h_t = x_t & x_w not excluded
                if ok:
                    prs=[p for p in pairs0 if not (t in p and (p[0] if p[1]==t else p[1]) not in W)]
                    zsets=[(S&Bs)-{t} for S in Sv[t] if not (S&set(W))]
                    ok=realizable(t,W,prs,zsets)
                if ok:
                    Ws=set(W); meet=[S for S in sets if S&Ws]
                    loss=sum(len(S)-1 for S in meet)
                    # c is counted unless (t of class S, AND-type) it could coincide with an output through W
                    cg=1 if (t in Ut or all((P[w]&Bs)<={t} and (w in Us or not any(len(S)>=3 and w in S and S<=set(Np) for S in sets)) for w in W)) else 0
                    dead=1+cg+len(meet)+len(Ws&Ut)
                    if refined:
                        bS=min(1,len(Ws&Sc))                                       # h_w, w of class S
                        bN=min(1,sum(1 for w in W if w not in Us and cls[w]=='T')) if t in Ut else 0   # Lemma N-O, w p-tight
                        dead+=max(bS,bN)
                    ok=dead>loss-sigma
                    if not ok and refined and dead==loss-sigma and len(W)==1 and W[0] in Ut and P[W[0]]&Bs=={t}: ok=True  # (E)
                if not ok:
                    if explain is not None: explain.append(('U',t,W))
                    return False
    return True
memo={}
def covered(sets,rules=RULES_NEW,greedy='none'):
    sets=norm(sets); key=(sets,rules,greedy)
    if key in memo: return memo[key]
    if all(len(S)<=3 for S in sets): memo[key]=True; return True          # small3 (proved)
    d=degs(sets)
    for v in d:
        if sum(1 for S in sets if v in S and len(S)>=3)<=1:                # R0 (proved)
            r=covered(delete(sets,v),rules,greedy); memo[key]=r; return r
    r=all(covered(delete(sets,v),rules,greedy) for v in d) and not feasible(sets,False,rules,greedy)
    memo[key]=r; return r
if __name__=='__main__':
    # usage: python3 cover2.py GREEDY RULES1,RULES2,... n1 n2 ...   (RULES '-' = (i),(ii) only)
    import pickle
    gr=sys.argv[1]; RS=[('' if x=='-' else x) for x in sys.argv[2].split(',')]
    for n in sys.argv[3:]:
        R=pickle.load(open(f'cores{n}.pkl','rb'))
        for rules in RS:
            cv=[covered(s,rules,gr) for s in R]
            print('n',n,'skeleton cores',len(R),'greedy',gr,'rules',rules or '(i),(ii)','covered',sum(cv),flush=True)
