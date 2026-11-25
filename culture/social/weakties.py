#!/usr/bin/env python3
"""Granovetter's strong triadic closure, by exhaustion on every labelled graph on 1..5 vertices and every strong/weak labelling.
Granovetter, The Strength of Weak Ties (1973); Easley and Kleinberg, Networks, Crowds, and Markets (2010) (cited from memory, not read).
Definitions. Strong triadic closure at v: any two strong neighbours of v are adjacent (by any tie). Local bridge: an edge whose
endpoints share no neighbour. Easley-Kleinberg claim: if v satisfies it and has at least two strong edges, a local bridge at v is weak.
Finding: the bare claim "STC everywhere implies every local bridge is weak" is FALSE (one strong edge between two vertices); the
hypothesis "an endpoint has two strong edges" is needed. Both are counted.
Run: python3 -I culture/social/weakties.py   (last line is JSON)
"""
import itertools, json, time

def main():
    t0 = time.time(); graphs = lab = stc = with_lb = bare_fail = 0; first = None
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
                if not all(y in nb[x] for v in range(n) for x, y in itertools.combinations(sorted(sn[v]), 2)): continue
                stc += 1
                for e in lb:
                    if e in strong:
                        if first is None: first = (n, E, sorted(strong))
                        bare_fail += 1
                        assert any(len(sn[v]) >= 2 for v in e) is False, (n, E, strong)   # EK: no endpoint has two strong edges
    assert first == (2, [(0, 1)], [(0, 1)]) and bare_fail > 0
    print("graphs:", graphs, "; labellings:", lab, "(3^10 = 59049 on 5 vertices alone is part of it); graphs with a local bridge:", with_lb)
    print("labellings satisfying STC everywhere:", stc, "; strong local bridges among them:", bare_fail, "; smallest:", first)
    print("Easley-Kleinberg form holds: every strong local bridge under STC has no endpoint with two strong edges")
    print("PASS"); print(json.dumps({"states": lab, "seconds": round(time.time() - t0, 2), "graphs": graphs, "with_local_bridge": with_lb, "stc_labellings": stc, "bare_counterexamples": bare_fail}))

if __name__ == "__main__": main()
