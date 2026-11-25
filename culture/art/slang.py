#!/usr/bin/env python3
"""Gay and ballroom slang mapped onto the repository's structures. Checks only the mapping itself.

Each term maps to ONE structure, a file that exists in this repository. Checked:
  1. every term has exactly one structure (the mapping is a function, not a relation);
  2. every target file exists;
  3. every term has a source note (no term without a provenance line).
These are readings: the mapping says where a term's meaning would sit in the repo's structures, not what
the word means to the people who use it. Those meanings come from the communities, not from this file.
Run: python3 -I culture/art/slang.py   (last line is JSON)
"""
import json, os, time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
MAP = {
    "camp":    ("culture/art/camp.ath", "a broadcast of exaggerated, knowing artifice: the star of cone.py, read as style"),
    "read":    ("core/ontology/qualquant.py", "a witty takedown with a counterexample: a refuted row, kept on the record"),
    "shade":   ("culture/homestuck/quadrants/check.py", "an indirect hostility: a negative edge, as in the kismesis quadrant"),
    "clocked": ("culture/art/reference.py", "being recognised as something: supplied by the listener, not by the message"),
    "house":   ("culture/love/family.py", "a chosen family in which no one is alone: the household check"),
    "tea":     ("culture/art/reference.py", "gossip that travels laterally: a lateral link, not news from the hub"),
    "come for": ("core/ontology/asymmetry.py", "a one-way challenge: a non-symmetric relation"),
}
SOURCE = {
    "camp": "queer slang; Sontag 1964 took it into wider culture (cited from memory)",
    "read": "ballroom and Black and Latino queer usage (cited from memory; documented in Paris Is Burning, 1990, dir. Jennie Livingston)",
    "shade": "queer and Black vernacular usage (cited from memory)",
    "clocked": "ballroom and queer vernacular usage (cited from memory)",
    "house": "New York ballroom culture, commonly dated to Harlem in the 1920s and 30s (cited from memory)",
    "tea": "Black vernacular usage (cited from memory)",
    "come for": "Black and queer vernacular usage (cited from memory)",
}

def main():
    t0 = time.time(); states = 0
    for term, (target, meaning) in MAP.items():
        states += 1
        assert list(MAP).count(term) == 1, f"{term}: one structure only"
        assert os.path.exists(os.path.join(ROOT, target)), f"{term}: missing target {target}"
        assert term in SOURCE and SOURCE[term].strip(), f"{term}: no source note"
    assert len(MAP) == len(SOURCE) == 7
    print(f"{len(MAP)} terms, each mapped to one existing structure, each with a source note")
    for term, (target, meaning) in MAP.items():
        print(f"  {term}: {target}  ({meaning})")
    print("PASS")
    print(json.dumps({"states": states, "seconds": round(time.time() - t0, 3), "terms": len(MAP)}))

if __name__ == "__main__":
    main()
