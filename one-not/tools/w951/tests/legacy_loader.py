"""Loads the ORIGINAL implementations (verbatim copies under tests/legacy/<branch>/<original path>).

Importable scripts are imported as they are; scripts that do work at import time are cut at the
same marker the scripts themselves use (e.g. ov951 at 'random.seed(') and only their defs are run.
Module-name clashes between directories (`lib`, `relrule`) are handled by aliasing during import.
"""
import contextlib
import importlib.util
import io
import os
import sys
import types

HERE = os.path.dirname(os.path.abspath(__file__))
LEG = os.path.join(HERE, 'legacy')
FRONT = os.path.join(LEG, 'front-match')
SCAF = os.path.join(LEG, 'scaffold-951')
TRACT = os.path.join(LEG, 'tractability')
FN = os.path.join(FRONT, 'work', 'notes951')
SN = os.path.join(SCAF, 'work', 'notes951', 'scripts')
DUALS = os.path.join(TRACT, 'work', 'duals')

_PATHS = [os.path.join(FN, 'scripts'), os.path.join(FN, 'scripts', 'w8'), os.path.join(FN, 'scripts', 'w8b'),
          os.path.join(FN, 'w9'), os.path.join(FN, 'w9', 'tw'), os.path.join(FN, 'w9', 'fb'), DUALS,
          os.path.join(SN, 'payment')]


@contextlib.contextmanager
def _quiet(**alias):
    argv, cwd, path = sys.argv, os.getcwd(), list(sys.path)
    saved = {k: sys.modules.get(k) for k in alias}
    sys.argv = ['x']
    sys.path[:0] = _PATHS
    sys.modules.update(alias)
    os.chdir(FRONT)                      # live951 / clean951_scaffold open 'tools/l951_charging/ov951.py'
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            yield
    finally:
        sys.argv = argv
        os.chdir(cwd)
        sys.path[:] = path
        for k, m in saved.items():
            if m is None:
                sys.modules.pop(k, None)
            else:
                sys.modules[k] = m


def _file(unique, path, **alias):
    with _quiet(**alias):
        spec = importlib.util.spec_from_file_location(unique, path)
        m = importlib.util.module_from_spec(spec)
        sys.modules[unique] = m
        spec.loader.exec_module(m)
    return m


def _plain(name):
    with _quiet():
        m = importlib.import_module(name)
    return m


def _slice(unique, path, start, end, glob=None, **alias):
    src = open(path).read()
    i = src.index(start)
    j = src.index(end, i) if end else len(src)
    m = types.ModuleType(unique)
    m.__dict__.update(glob or {})
    with _quiet(**alias):
        exec(compile(src[i:j], path, 'exec'), m.__dict__)
    return m


L = types.SimpleNamespace()
# front-match scripts (plain names, importable)
for _n in ('verify', 'chargeok_check', 'conedbl', 'nsets', 'hallcheck', 'gapg_check', 'allsys', 'rstar',
           'mixrule', 'fraclp', 'tw', 'clean', 'dual', 'irr', 'top2'):
    setattr(L, _n, _plain(_n))
L.fa_lib = _file('legacy_fa_lib', os.path.join(FN, 'w9', 'fa', 'lib.py'))
L.sig = _file('legacy_fa_sig', os.path.join(FN, 'w9', 'fa', 'sig.py'), lib=L.fa_lib)
L.sand = _file('legacy_fa_sand', os.path.join(FN, 'w9', 'fa', 'sand.py'), lib=L.fa_lib, sig=L.sig)
L.kill = _file('legacy_fe_kill', os.path.join(FN, 'w9', 'fe', 'kill.py'), lib=L.fa_lib)
L.rel = _file('legacy_fe_rel', os.path.join(FN, 'w9', 'fe', 'rel.py'), lib=L.fa_lib)
L.fc_lib = _file('legacy_fc_lib', os.path.join(FN, 'w9', 'fc', 'lib.py'))
L.priv = _file('legacy_fc_priv', os.path.join(FN, 'w9', 'fc', 'priv.py'), lib=L.fc_lib)
L.fc_relrule = _file('legacy_fc_relrule', os.path.join(FN, 'w9', 'fc', 'relrule.py'), lib=L.fc_lib)
import itertools as _it, json as _json, time as _time, collections as _col
L.gen_clean = _slice('legacy_gen_clean', os.path.join(FN, 'scripts', 'gen_clean.py'), 'def ev(', 'name, extra, cap',
                     dict(itertools=_it))
L.cfgI = _slice('legacy_cfgI', os.path.join(FN, 'w9', 'fb', 'cfgI.py'), 'def prune(', 'c2=prune(c2)')
L.restr951 = _slice('legacy_restr951', os.path.join(FRONT, 'tools', 'l951_charging', 'agents', 'restr951.py'),
                    'def restrict_count(', 't0=time.time()')
# tractability duals
for _n in ('dualp', 'resid', 'relrule', 'xrule'):
    setattr(L, _n, _plain(_n))
L.climbr = _slice('legacy_climbr', os.path.join(DUALS, 'climbr.py'), 'def tt_ok(', 'def mutate(')
# scaffold
L.ana = _plain('ana')
L.gen = _slice('legacy_gen', os.path.join(SN, 'scaffold_opus', 'gen.py'), 'def cone(', 'def analyse(')
def chan_sat(n, sets):
    """scaffold_runs/chan_sat.py (verbatim), cut to its `build(p)` (which reads globals n, s, sets, R):
    returns build(s, p) -> (clauses, A, B, OP, O) for the instance."""
    from pysat.card import CardEnc, EncType
    path = os.path.join(SN, 'scaffold_runs', 'chan_sat.py')
    def build(s, p):
        m = _slice('legacy_chan_sat', path, 'def build(p):', 'for p in range(plo',
                   dict(CardEnc=CardEnc, EncType=EncType, n=n, sets=sets, s=s, R=1 << n))
        return m.build(p)
    return build


L.chan_sat = chan_sat
L.climbrel = _slice('legacy_climbrel', os.path.join(SN, 'scaffold_runs', 'climbrel.py'), 'def ev(', 'def score(')
L.needsB = _slice('legacy_needsB', os.path.join(SN, 'scaffold_runs', 'needsB.py'), 'def choice(', 'tot = withA',
                  dict(GC=L.gapg_check, os=os))
# SAT builders (need python-sat)
try:
    L.ov951 = _slice('legacy_ov951', os.path.join(FRONT, 'tools', 'l951_charging', 'ov951.py'), 'import itertools',
                     'random.seed(')
    L.live951 = _file('legacy_live951', os.path.join(FRONT, 'tools', 'l951_charging', 'live951.py'))
    L.clean951 = _file('legacy_clean951', os.path.join(FRONT, 'tools', 'l951_charging', 'clean951_scaffold.py'))
    L.have_sat = True
except ImportError:
    L.have_sat = False
