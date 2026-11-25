#!/usr/bin/env python3
"""Granovetter's strong triadic closure, by exhaustion on every labelled graph on 1..5 vertices and every strong/weak labelling.
Granovetter, The Strength of Weak Ties (1973); Easley and Kleinberg, Networks, Crowds, and Markets (2010) (cited from memory, not read).
Definitions. Strong triadic closure at v: any two strong neighbours of v are adjacent (by any tie). Local bridge: an edge whose
endpoints share no neighbour. Easley-Kleinberg claim: if v satisfies it and has at least two strong edges, a local bridge at v is weak.
Two forms are checked: STC at every vertex, and STC only at the endpoint v with two strong edges (EK as stated). A control without STC at v
shows the claim is not vacuous. Finding: the bare claim "STC everywhere implies every local bridge is weak" is FALSE (one strong edge between two vertices); the
hypothesis "an endpoint has two strong edges" is needed. Both are counted.
Run: python3 -I culture/social/weakties.py   (last line is JSON)
"""
import itertools, json, time

def main():
    t0 = time.time(); graphs = lab = stc = with_lb = bare_fail = ek_cases = nostc = 0; first = nostc_first = None
    for n in range(1, 6):
        pairs = list(itertools.combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            E = [p for k, p in enumerate(pairs) if mask >> k & 1]; graphs += 1
            nb = [set() for _ in range(n)]
            for a, b in E: nb[a].add(b); nb[b].add(a)
            lb = [e for e in E if not (nb[e[0]] & nb[e[1]])]; with_lb += bool(lb)
            for lm in range(1 << len(E)):
                strong = {e for k, e in enumerate(E) if lm >> k & 1}; lab += 1
                sn = [{b if a == v else a for a, b in strong if v in (a, b)} for v in range(n)]
                ok = [all(y in nb[x] for x, y in itertools.combinations(sorted(sn[v]), 2)) for v in range(n)]
                for e in lb:
                    if e not in strong: continue
                    for v in e:
                        if len(sn[v]) < 2: continue
                        if ok[v]: ek_cases += 1; assert False, (n, E, strong)   # EK, STC at v only: must never happen
                        nostc += 1
                        if nostc_first is None: nostc_first = (n, E, sorted(strong))
                if not all(ok): continue
                stc += 1
                for e in lb:
                    if e in strong:
                        if first is None: first = (n, E, sorted(strong))
                        bare_fail += 1
                        assert not any(len(sn[v]) >= 2 for v in e), (n, E, strong)   # global STC form of EK
    assert first == (2, [(0, 1)], [(0, 1)]) and bare_fail > 0
    assert ek_cases == 0 and nostc > 0 and nostc_first == (3, [(0, 1), (0, 2)], [(0, 1), (0, 2)])   # control: without STC at v it fails
    print("graphs:", graphs, "; labellings:", lab, "; graphs with a local bridge:", with_lb)
    print("labellings with STC everywhere:", stc, "; strong local bridges among them:", bare_fail, "; smallest:", first)
    print("EK as stated (STC only at the endpoint v with two strong edges): strong local bridges at such v:", ek_cases, "(none)")
    print("Control, no STC at v: strong local bridge with an endpoint of two strong edges occurs", nostc, "times; smallest:", nostc_first)
    print("PASS"); print(json.dumps({"states": lab, "seconds": round(time.time() - t0, 2), "graphs": graphs, "with_local_bridge": with_lb, "stc_labellings": stc, "bare_counterexamples": bare_fail, "ek_violations": ek_cases, "no_stc_control": nostc}))

if __name__ == "__main__": main()
