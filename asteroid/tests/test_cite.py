"""Test of the citation resolver and gate (tools/cite/cite.py, tools/cite/gate.py). Run: python3 -I asteroid/tests/test_cite.py"""
import os, sys
ROOT = os.path.realpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "tools", "cite"))
import cite as C, gate as G

def alive(k): C.reset(); return C.resolve(*C.parse_keys(k)[0])[0]
assert alive('file:README.md') and not alive('file:../../etc/passwd') and not alive('file:no/such/file')
assert alive('original')
assert not alive('lit:"zz no such source zz"') and not alive('doi:10.0000/zz-not-indexed')
assert not alive('lean:zz_no_such_declaration') and not alive('commit:deadbee') and not alive('commit:xyz')
assert C.tokens('[PROVED] x cite:lit:"A B" and cite:original') == [("lit", "A B"), ("original", "")]

def problems(path, text):
    C.reset(); r = []; G.check_file(path, text, None, r); return [w for _, _, w in r]
assert problems("a.ath", "claim correct(x)\ncite original\n") == []
assert problems("a.ath", "claim correct(x)\nclaim correct(y)\ncite original\n") == ["claim with no cite line below it"]
assert any("dead" in w for w in problems("a.ath", "claim correct(x)\ncite file:no/such\n"))
assert problems("a.md", "- [PROVED] x\n") == ["result tag with no cite:KEY on the line"]
assert problems("a.md", "- [PROVED] x cite:original\n- plain line\n") == []
assert problems("a.lean", "theorem t : True := trivial\n") != []
assert problems("a.lean", "/-! cite:original -/\ntheorem t : True := trivial\n") == []
print("PASS")
