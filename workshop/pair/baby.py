# Run hello.ath through bin/asteroid. Print the last output line. Exit with asteroid's exit code.
import os
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
FRAMES = "/tmp/claude-0/-home-user/c7c2895f-eb04-517d-b538-6d0d59d567a9/scratchpad/pair_frames.jsonl"
PROGRAM = "hello.ath"
TIMEOUT = 110


def main():
    env = dict(os.environ, ASTEROID_FRAMES=FRAMES)
    cmd = [os.path.join(REPO, "bin", "asteroid"), "--no-lean", PROGRAM]
    try:
        proc = subprocess.run(cmd, cwd=REPO, env=env, capture_output=True,
                              text=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        print(f"timeout after {TIMEOUT} s: {PROGRAM}")
        return 124
    lines = (proc.stdout + proc.stderr).splitlines()
    print(lines[-1] if lines else "")
    return proc.returncode


if __name__ == "__main__":
    sys.exit(main())
