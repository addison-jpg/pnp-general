"""frames_meta.ath: a checked-finite frame states only the checked fact; any interpretation is marked analogy (reading)."""
import os, re, unittest
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PAT = re.compile(r'frame "([^"]+)" reading "([^"]+)" -> (\S+) label ([\w-]+)')

class FramesMeta(unittest.TestCase):
    def test_checked_readings_are_facts_only(self):
        rows = [PAT.match(l) for l in open(os.path.join(ROOT, "frames_meta.ath"), encoding="utf-8")]
        rows = [m for m in rows if m]
        self.assertEqual(len(rows), 6)
        for src, reading, ref, label in (m.groups() for m in rows):
            if label != "checked-finite" or not any(k in src for k in ("Lewis", "Lyotard", "Homestuck")): continue
            self.assertTrue(reading.startswith("Kripke fact only:"), reading)
            self.assertIn("analogy (reading)", src)

if __name__ == "__main__": unittest.main()
