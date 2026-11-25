"""w951: one shared toolkit for the L-meta-951 experiments (Boolean sums, one-NOT circuits).

    circuit   Circuit (JSON I/O, truth tables, C0/C1, cones, readers, checks, restrict / delete_outputs)
    systems   test systems, counted sets, menus (canon, R*, full menu, Gap-G, hard N-sets)
    matching  capacitated bipartite matching (Dinic), copied from research/tools/matching
    lp        min max load LP, fixed-weight LP, dual prices
    rules     private / sandwich classes, relative-sandwich rule, X-rule, coin rule
    sat       SAT encodings that generate circuits (needs python-sat)
See README.md for the old-script -> new-function map.
"""
from .circuit import Circuit, Reduced, as_circuit, load, save, point, bits, z_of, CONST0, CONST1
from . import circuit, systems, matching

__all__ = ['Circuit', 'Reduced', 'as_circuit', 'load', 'save', 'point', 'bits', 'z_of', 'CONST0', 'CONST1',
           'circuit', 'systems', 'matching', 'lp', 'rules', 'sat']


def __getattr__(name):          # lp / rules need scipy, sat needs python-sat: import them on first use
    if name in ('lp', 'rules', 'sat'):
        import importlib
        return importlib.import_module('.' + name, __name__)
    raise AttributeError(name)
