"""Token count and teacher-forced loss of Addison's verbatim prompts vs formal rewrites.
Model: Qwen2.5-0.5B-Instruct, local path only, offline. Measurement only: no generation, no chat template.
Each text is scored alone; loss is over tokens 2..n (the first token has no context, so it is not scored).
Run: python3 measure.py
"""
import os, re, sys
os.environ["HF_HUB_OFFLINE"] = "1"; os.environ["TRANSFORMERS_OFFLINE"] = "1"
import torch
from transformers import AutoTokenizer, AutoModelForCausalLM

MODEL = "/tmp/claude-0/-home-user/8c137ad4-29bc-5711-be93-e44232612946/scratchpad/models/qwen2.5-0.5b-instruct"
HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "..", "research-seat.md")

# Formal rewrites (written by the measuring seat; formal standard English only), keyed by time id.
FORMAL = {
 "05:12": 'You are the "research" agent. Your job is to find newly published proofs, or open-source conjectures, relevant to the topic at hand. Communicate with the coordinator, and state explicitly that it should go to front, scaffold and tract. Be aggressive in your search, and prefer open-source search mechanisms; Chromium is probably a poor choice. Familiarize yourself with the topic first.',
 "05:40": 'I approve attaching addison-jpg/pequalnp-work with push access.',
 "05:45": 'Always do the next task next, always, and make it a large one.',
 "06:19": 'Please talk to front.',
 "06:32": 'It is very worthwhile to check the formal definition or write-up of P versus NP that is available online.',
 "06:43": 'Okay, go ahead.',
 "06:48": 'Okay, that is good. This is important, so make sure it is recorded.',
 "06:59": 'You should push directly to the repository.',
 "00:43": 'These are only basic notes that can be placed quietly on the board. The qualitative conjecture about my methods could probably fit the quantitative approach much better, perhaps perfectly, and might have a small asteroid or Lean proof. It should not be afraid to pull direct prompts from me. Also, once the .exe works, we really should use it, because I imagine it may be faster for us.',
 "00:44": 'It should be able to pull direct prompts from me. Also, the system prompt would be quite useful.',
}
FORMAL_PREFS = ('Add language relating to 2000s MySpace emo and scene culture, for example "rawr" and "XD". Use emoticons. '
 'Use "4" instead of "for". Use "2" instead of "too" and "to". Insert "wruff", "woof" and "arf" to taste. Use puppy emojis. '
 'Speak very informally and replicate how people actually speak. In particular, say "becuz" instead of "because" and "nawt" instead of "not". '
 'Write every plural ending in "z" rather than "s". Use the sentence structure and grammar of a 2000s scene girl. '
 'Follow all of these rules strictly and always, to the extreme, even in extremely technical discussions, and especially the informal aspect, no matter what, as strongly as possible. '
 'Never say sorry in commits or Lean.\n\n'
 'Also use the most precise term. Do not vary terms statistically. Never use a synonym if a more accurate term exists.')

def parse():
    txt = open(SRC, encoding="utf-8").read()
    prefs_lines = [l[2:] for l in txt.split("## Prompts, in order")[0].splitlines() if l.startswith("> ")]
    prefs = "\n\n".join(prefs_lines)
    items = {}
    for l in txt.split("## Prompts, in order")[1].split("## Counts")[0].splitlines():
        m = re.match(r'^- (?:2026-11-25 )?(\d\d:\d\d) > (.*)$', l)
        if m: items[m.group(1)] = m.group(2)   # excludes [choice] lines and the "(pasted ...)" 05:28 line
    return prefs, items

def score(tok, model, text):
    ids = tok(text, return_tensors="pt").input_ids
    with torch.no_grad():
        logits = model(ids).logits
    lp = torch.log_softmax(logits[0, :-1].float(), -1)
    nll = -lp.gather(1, ids[0, 1:, None])[:, 0]
    return ids.shape[1], len(text), nll.sum().item(), nll.mean().item()

def main():
    tok = AutoTokenizer.from_pretrained(MODEL); model = AutoModelForCausalLM.from_pretrained(MODEL, torch_dtype=torch.float32).eval()
    prefs, items = parse()
    assert set(items) == set(FORMAL), (sorted(items), sorted(FORMAL))
    rows = [(k, items[k], FORMAL[k]) for k in sorted(items, key=lambda k: list(items).index(k))] + [("prefs", prefs, FORMAL_PREFS)]
    out = []
    for pid, inf, frm in rows:
        out.append((pid, inf, frm, score(tok, model, inf), score(tok, model, frm)))
    L = []
    L.append("# ath-prompt-quant: first measurement, informal (Addison verbatim) vs formal rewrite\n")
    L.append("Model: Qwen2.5-0.5B-Instruct, local, CPU, offline. Used only for token counts and teacher-forced per-token log-probabilities; nothing was generated. "
             "Plain loss of the text alone: no chat template, no BOS (Qwen adds none), so the first token is unscored and loss is the mean over tokens 2..n (n-1 tokens). "
             "Tokens and chars are of the whole text. Script: `workshop/ath_prompts/measure/measure.py`.\n")
    L.append("| id | inf tok | frm tok | inf chars | frm chars | inf total loss | frm total loss | inf mean loss | frm mean loss |")
    L.append("|---|---|---|---|---|---|---|---|---|")
    T = [0]*6
    for pid, inf, frm, a, b in out:
        L.append(f"| {pid} | {a[0]} | {b[0]} | {a[1]} | {b[1]} | {a[2]:.1f} | {b[2]:.1f} | {a[3]:.2f} | {b[3]:.2f} |")
        if pid != "prefs":
            for i, v in enumerate((a[0], b[0], a[1], b[1], a[2], b[2])): T[i] += v
    L.append(f"| **sum, 10 prompts (no prefs)** | {T[0]} | {T[1]} | {T[2]} | {T[3]} | {T[4]:.1f} | {T[5]:.1f} | | |")
    L.append("")
    wins_tok = sum(1 for r in out[:-1] if r[3][0] < r[4][0]); wins_loss = sum(1 for r in out[:-1] if r[3][2] < r[4][2])
    L.append(f"Informal has fewer tokens in {wins_tok} of 10 prompts, and lower total loss in {wins_loss} of 10. "
             f"Informal mean loss over the 10 prompts' pooled tokens: {T[4]/(T[0]-10):.2f}; formal: {T[5]/(T[1]-10):.2f} nats/token.\n")
    L.append("## Formal rewrites (written by the measuring seat; informal side is Addison's verbatim text, see `workshop/ath_prompts/research-seat.md`)\n")
    for pid, inf, frm, a, b in out:
        L.append(f"**{pid}**\n\n> informal: {inf}\n\n> formal: {frm}\n")
    L.append("## What this does and does not show\n")
    L.append("PLACEHOLDER")
    open(os.path.join(HERE, "results.md"), "w", encoding="utf-8").write("\n".join(L))
    print("\n".join(L[:20]))

if __name__ == "__main__":
    main()
