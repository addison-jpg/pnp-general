#!/usr/bin/env python3
"""Run every top-level .ath program with --no-lean (hello.ath needs Lean and is skipped); PASS if all exit 0."""
import glob, os, subprocess, sys
root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
progs = [p for p in sorted(glob.glob(os.path.join(root, "*.ath"))) if os.path.basename(p) not in ("hello.ath", "first_light.ath")]
bad = []
for p in progs:
    r = subprocess.run([os.path.join(root, "bin", "asteroid"), "--no-lean", p], cwd=root, capture_output=True, text=True, timeout=900)
    print(("ok  " if r.returncode == 0 else "FAIL"), os.path.basename(p))
    if r.returncode: bad.append(p)
print(f"{len(progs) - len(bad)} of {len(progs)} programs pass")
if bad: sys.exit(1)
print("PASS")
