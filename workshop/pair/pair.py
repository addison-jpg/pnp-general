# Run baby.py and big.py in turn. Print both last lines, then JSON exit codes. Exit 0 only if both are 0.
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
TIMEOUT = 110


def run(script):
    try:
        proc = subprocess.run([sys.executable, os.path.join(HERE, script)],
                              capture_output=True, text=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return 124, f"timeout after {TIMEOUT} s: {script}"
    lines = proc.stdout.splitlines()
    return proc.returncode, (lines[-1] if lines else "")


baby_code, baby_last = run("baby.py")
big_code, big_last = run("big.py")
print(baby_last)
print(big_last)
print(json.dumps({"baby": baby_code, "big": big_code}))
sys.exit(0 if baby_code == 0 and big_code == 0 else 1)
