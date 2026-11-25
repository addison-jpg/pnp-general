"""Tests for the poetry track's repairs. Run: python3 -I -m unittest discover -s culture/poetry -p test_poetry.py (under 1 s)."""
import importlib.util, itertools, json, math, os, re, subprocess, unittest
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
spec = importlib.util.spec_from_file_location("poetry_check", os.path.join(HERE, "check.py"))
check = importlib.util.module_from_spec(spec); spec.loader.exec_module(check)

def read(path):
    with open(path, encoding="utf-8") as fh: return fh.read()
def text(name): return read(os.path.join(HERE, name))
def tags(): return {t["tag"]: t for t in json.loads(text("tags.json"))["tags"]}

class Provenance(unittest.TestCase):
    def test_readme_states_which_commit_holds_what(self):
        r = text("README.md")
        self.assertIn("cace727 holds only this README and `tags.json`", r)
        self.assertIn("f5cd385", r)

    def test_cace727_really_holds_only_two_files(self):
        try:
            out = subprocess.run(["git", "-C", ROOT, "show", "--stat", "--format=", "cace727"],
                                 capture_output=True, text=True, timeout=30)
        except OSError: self.skipTest("git not available")
        if out.returncode: self.skipTest("not a git checkout with cace727")
        files = sorted(l.split("|")[0].strip() for l in out.stdout.splitlines() if "|" in l)
        self.assertEqual(files, ["culture/poetry/README.md", "culture/poetry/tags.json"])

class Sources(unittest.TestCase):
    def test_no_untraceable_governance_source(self):
        for f in ("README.md", "tags.json", "check.py"):
            t = text(f).lower()
            self.assertNotIn("governance", t, f); self.assertNotIn("scratchpad", t, f)
        self.assertNotIn("governance", read(os.path.join(ROOT, "poetry.ath")).lower())

    def test_anchor_is_our_own_definition(self):
        r = text("README.md")
        self.assertRegex(r, r"\*\*P6\. The anchor\.\*\*.*our own construction.*Freud and Lacan did not define it")
        self.assertIn("not Freud's or Lacan's", tags()["anchor"]["reading"])

    def test_no_forbidden_word(self):
        for f in ("README.md", "tags.json", "check.py", "findings.jsonl", "fingerprints.json", "test_poetry.py"):
            self.assertNotIn("s" + "orry", text(f).lower(), f)

class Condensation(unittest.TestCase):
    def test_readme_says_given_kernel(self):
        self.assertIn("Maps with a given kernel of b blocks", text("README.md"))
        self.assertIn("S(k,b) · m(m−1)…(m−b+1)", text("README.md"))

    def test_total_over_kernels_is_stirling_times_falling(self):
        for k, m in ((4, 3), (5, 4), (3, 5)):
            by_b = Counter(len(set(f)) for f in itertools.product(range(m), repeat=k))
            for b in range(1, k + 1):
                self.assertEqual(by_b[b], check.stirling2(k, b) * check.falling(m, b))
        self.assertEqual([check.stirling2(5, b) for b in range(6)], [0, 1, 15, 25, 10, 1])

class Capiton(unittest.TestCase):
    code = ["0", "01", "11"]

    def test_delay_unbounded_without_known_length(self):
        for k in range(16):
            firsts = set()
            for tail in ("", "1"):                         # one more bit flips which parse exists
                ps = check.parses("0" + "1" * k + tail, self.code)
                if ps: firsts.add(ps[0][0])
            self.assertEqual(firsts, {"0", "01"}, k)

    def test_readme_says_length_is_known_and_drops_end_only_reading(self):
        r = text("README.md")
        self.assertIn("the reader is assumed to know the chain's length", r)
        self.assertIn("unbounded", r)
        self.assertNotIn("a chain can be read only from its end", r)
        self.assertIn("unbounded", tags()["point-de-capiton"]["means"])
        self.assertIn("length known", read(os.path.join(ROOT, "poetry.ath")))

class Queneau(unittest.TestCase):
    def test_book_rhyme_claim_not_checked_finite(self):
        t = tags()
        self.assertNotIn("rhyme", t["combinatorial-poem"]["means"])
        self.assertEqual(t["combinatorial-poem-rhyme"]["label"], "open")

    def test_toy_is_not_a_tautology(self):
        src = text("check.py")
        self.assertIn("some poem leaves the scheme", src)
        check.queneau()                                     # asserts both directions

class Petrarch(unittest.TestCase):
    def test_enumerator_matches_formula_on_small_profiles(self):
        for n in range(1, 8):
            for prof in {check.profile(s) for s in check.rgs(n)}:
                parts = list(check.by_profile(n, prof))
                self.assertEqual(len(parts), len(set(parts)))
                self.assertEqual(len(parts), check.profile_formula(n, prof), (n, prof))

    def test_petrarch_label_matches_evidence(self):
        src = text("check.py")
        self.assertIn("by_profile(14, (4, 4, 2, 2, 2))", src)
        self.assertEqual(tags()["sonnet-petrarchan"]["label"], "checked-finite")
        self.assertIn("enumerated at n = 14", tags()["sonnet-petrarchan"]["means"])
        self.assertEqual(math.comb(14, 4) * math.comb(10, 4) // 2 * 15, 1576575)

class Records(unittest.TestCase):
    def test_findings_match_poetry_ath_records(self):
        ath = read(os.path.join(ROOT, "poetry.ath"))
        stmts = re.findall(r'^record \S+ \S+ \S+ "(.*)"$', ath, re.M)
        rows = [json.loads(l) for l in text("findings.jsonl").splitlines() if l.strip()]
        self.assertEqual(sorted(r["statement"] for r in rows), sorted(stmts))

if __name__ == "__main__":
    unittest.main()
