#!/usr/bin/env python3
"""Invisible work in the recorded seat tables: how many tokens leave no checked line? Standard library only.

Data, and nothing else: the seat table under "Data so far" in ath_prompt_method.md (11 seats, tool-reported tokens).
Measured (exact on that table): the share of all tokens spent by seats whose result is not "checked"
(an obstacle, or tested only). Those tokens left no checked line, though an obstacle is still written work.
Proxy (an assumption, not measured): the cheapest seat's total stands in for the fixed read of rules and files.
For each seat, min(floor, tokens) / tokens is then the share of its tokens that was reading, not output.
Not measured at all: tokens per committed line, or coordination tokens. The table has no such column.
Star and Strauss (1999) on visible and invisible work: cited from memory; the link is analogy.
Run: python3 -I workshop/ath_prompts/invisible/invisible.py      (last line is JSON)
"""
import json, os, re
root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
text = open(os.path.join(root, "ath_prompt_method.md"), encoding="utf-8").read().split("### Data so far")[1].split("###")[0]
rows = [[c.strip() for c in l.strip("|").split("|")] for l in text.splitlines() if re.match(r"\| \w+ \| \w+ \|.*\| [\d,]+ \|", l)]
seats = [(r[0], r[1], int(r[3].replace(",", "")), r[5]) for r in rows]
assert len(seats) == 11, len(seats)
total = sum(t for _, _, t, _ in seats)
unchecked = sum(t for _, _, t, res in seats if "checked" not in res)
floor = min(t for _, _, t, _ in seats)
for name, model, t, res in seats:
    print(f"{name:10} {model:6} {t:>8,} tokens  result: {res:30} reading share (proxy) {min(floor, t) / t:.2f}")
print(f"seats {len(seats)}, tokens {total:,}; tokens in seats with no checked line: {unchecked:,} ({unchecked / total:.1%})")
print(f"floor (cheapest seat) {floor:,}; it is {floor * len(seats) / total:.1%} of all tokens if every seat paid it (proxy)")
print("PASS")
print(json.dumps({"states": len(seats), "tokens": total, "no_checked_line": unchecked, "share_no_checked_line": round(unchecked / total, 4),
                  "floor": floor, "floor_share_proxy": round(floor * len(seats) / total, 4)}))
