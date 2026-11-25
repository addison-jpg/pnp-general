#!/usr/bin/env python3
"""Attack (c): is ~78k tokens per checked lemma mostly the fixed cost of starting a seat? Standard library only.
Inputs are numbers copied from files this seat read (paths below); nothing is measured anew except file sizes.
Run: python3 -I workshop/ath_prompts/attack/seat_floor.py"""
import os
R = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..")
# workshop/ath_prompts/measure/cost_per_result.md: plain one-lemma Sonnet lines
SEATS, LEMMAS, TOKENS = 13, 15, 1_165_505
MIN_SEAT = 76_792  # C1, 32 s, the cheapest plain seat
# ath_prompt_method.md table: (tokens, lemmas) for the six Sonnet seats listed there
LISTED = {"A6": (99_716, 1), "A8": (84_399, 1), "A9": (91_567, 2), "A11": (92_533, 1), "A12": (89_475, 2), "B8": (86_424, 1)}
# workshop/ath_prompts/measure/trial/CLAUDE_HAIKU.md: 84 Haiku agents, no tools, one short answer each, about 5.5M tokens
HAIKU_FLOOR = 5_500_000 / 84

print(f"per checked lemma: {TOKENS / LEMMAS:,.0f}; per seat: {TOKENS / SEATS:,.0f}")
for name, floor in (("Haiku no-tool agent (other model; analogy)", HAIKU_FLOOR), ("cheapest plain Sonnet seat (upper bound on the floor)", MIN_SEAT)):
    fixed = floor * SEATS; marg = (TOKENS - fixed) / LEMMAS
    print(f"floor {floor:,.0f} = {name}: fixed share of all tokens {fixed / TOKENS:.0%}; marginal tokens per lemma {marg:,.0f}")
one = [t for t, l in LISTED.values() if l == 1]; two = [t for t, l in LISTED.values() if l == 2]
print(f"listed seats: one-lemma mean {sum(one) / len(one):,.0f} (n={len(one)}), two-lemma mean {sum(two) / len(two):,.0f} (n={len(two)})")
print(f"  -> a second lemma adds {sum(two) / len(two) - sum(one) / len(one):+,.0f} tokens: no sign of a per-lemma cost at this n")
spread = max(t for t, _ in LISTED.values()) - min(min(t for t, _ in LISTED.values()), MIN_SEAT)
print(f"spread of plain seats: {spread:,} tokens; a doubling of the marginal part would add about {(TOKENS - HAIKU_FLOOR * SEATS) / SEATS:,.0f} per seat")
# rule files every seat is told to read, in characters; tokens shown at 4 chars/token (an approximation, no tokenizer)
for f in ("BOARD.md", "AGENTS.md"):
    p = os.path.join(R, f)
    if os.path.exists(p):
        n = os.path.getsize(p); print(f"{f}: {n:,} bytes today, about {n / 4:,.0f} tokens at 4 chars/token")
print("PASS")
