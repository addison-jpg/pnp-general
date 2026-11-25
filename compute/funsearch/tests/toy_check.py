#!/usr/bin/env python3
"""Independent check of the toy claim (exit 1 = the claim fails on the instance, the convention of a finding's runner)."""
import sys, json
xs = json.load(sys.stdin)['xs']
sys.exit(1 if len(set(xs)) == 3 and all(0 <= x <= 9 for x in xs) and xs[0] + xs[1] + xs[2] > 23 else 0)
