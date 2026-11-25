# A conjecture about informal prompting and boards

This file is a conjecture about a way of prompting. It was written from one long working session in
this repository on 2026-11-24. It is an opinion with some evidence from that day. Nothing in it was
measured, and nothing in it is proved. A formal statement with named quantities, at three scales, was added on 2026-11-25 (see below); it is still a conjecture.

It is also not a claim about P versus NP. The method produced the tools in this repository, asteroid
among them. That is all it is claimed to have done.

## Addison's idea

In Addison's words:

> "informal prompting in small scale tasks, even as silly as a scene queen furry, helps to distill
> tasks in fun ways for the user and agent (even if agent isnt conscious). then, the thing that
> follows from this small idea of informality is an extremely intentional subdivided setup like i
> essentually manually made-- that runs in parallel because theres an above and below ( in this
> case,,,, ) coord-coord front-front, etc. theres a big guy (you) whos in between and coordinates.
> and the really special part-- they all have boards, which can be properly allocated to make
> communication easier."

Addison asked for this to be written down as "a qualitative conjecture about my prompting methods,
including informality and scene speak. it adds taste", and as "a qual framework that assists
asteroid without any actual formality".

## The conjecture

1. On a small task, an informal or playful instruction is often a better instruction than a formal
   one, because it is shorter and says what is wanted.
2. This makes sense computationally! Tokens don't care if you use big words, they want efficient inputs. 
3. Small informal instructions only add up to a large piece of work if they sit inside a strict
   frame. The frame is deliberate. It is the opposite of informal.
4. The frame that worked here was: seats in mirrored pairs, one coordinator between them, and a
   written board for every seat and every task.
5. The boards matter most. When each board has one owner and one subject, most communication can be
   read where the next reader will look, and few messages need to be sent.

## Informality and scene speak

Addison writes to agents the way one writes to a friend: lower case, slang, jokes, sometimes a
full scene register. Some of the lines that shaped this repository are in that voice. "no more
graffiti" turned the boards into a data structure. "its like taking an icepick to an earhole" became
the rule about agent size. "smaller tasks smaller boards" became the layout of `boards/tasks/`.

Four reasons this may help on small tasks:

- It forces the task to be stated simply. A joke cannot carry three nested conditions, so the task
  gets cut down to the one thing that is wanted.
- It makes it cheap to say "this is wrong" or "kill it". In a formal register a correction reads as
  a reprimand and people soften it. In a playful one it is just the next line.
- It is easy to remember. A rule with a picture in it is still in mind twenty tasks later, and it
  can be quoted on a board in the same words.
- It sets the tone for both sides. The answer that fits a short blunt ask is a short blunt answer,
  and that is usually the useful one.

The phrase "it adds taste" is part of the claim. A voice carries preferences that a specification
leaves out: what counts as too much, what counts as boring, when to stop.

None of this assumes the agent is conscious, or that it enjoys anything. Addison says so in the
quote above. The effect, if it is real, is on how tasks get stated and handed over. A person who is
having fun writes more asks, smaller asks, and more honest corrections.

## From informality to structure

Addison built the frame by hand. On that day there were about a dozen parallel sessions with named
roles: coord, front, scaffold, research, warden, tractability, machines-Lean, cTAHG and others.
Several came in pairs across two machines, a desktop coord and a cloud coord, a front with a front.
One main session sat in the middle. It relayed Addison's words, split the work and merged the
results. Under it were subagents of different sizes.

Every seat had somewhere to write. There was one main board (`BOARD.md`), area boards
(`boards/*.md`), and one small board per task (`boards/tasks/`, 29 files when this was written, each
about ten lines with one statement and one "done when"). Later the boards became a tree: small
findings kept in `findings.jsonl` next to their evidence, and a script (`boards.py`) that carries
the verified ones up the directory tree into `boards/TREE.md`.

The mirrored pairs give each seat a partner who has the same job and reads the same board. The
coordinator gives Addison one place to speak. The boards mean that an instruction can stay
informal and still not be lost, because the board holds the exact statement, who has it, and what
would count as done.

## What the boards did, and what broke

The rules in `BOARD.md` were not designed in advance. Each one is a repair.

- Merge conflicts in shared files pulled Addison in to resolve them by hand. This produced "do not
  ask Addison, use the board", and union merges for the boards, so both sides' lines are kept.
- Agents in a shared working tree swept up each other's files in their commits. This produced rules
  about staging only your own files, and the plan for one integrating seat that pushes while the
  others pull.
- When boards were skipped, work was done twice. This produced "work only on a task that has a
  file".
- Large agents were put on small jobs. This produced "use the smallest agent that can do the job".
- Some claims were stated more strongly than their evidence. They were corrected on the boards, and
  this produced the finding records, where each statement carries a word such as checked, tested,
  refuted or open, and names its evidence.

## How it connects to asteroid

asteroid (`asteroid/README.md`) is the main thing this way of working produced. It has the same
habit at a smaller scale.

- A claim is one plain line in a `.ath` program, for example `claim slack(tiny) = 0 by lean`.
- The writer does not decide whether it holds. Python evaluates it, and Lean decides it in the
  kernel.
- Failures are kept. A refuted claim stays in the repository with its counterexample.

The boards are the same habit at the large scale: one board per task, one statement per finding, a
checker or a second reader who decides, and results carried upward as small verified records. In
both places the speaker can be loose, because the speaker is not the judge. That is the sense in
which this is a framework that helps asteroid without being formal itself.

## Auto mode and tokens

The same setup makes it easy to let the agents run on their own. When Addison stepped away, the work kept going because the rules an agent needs were written where it looks first: the top of the board says not to ask Addison, to write a question as a board line, and to decide and record the decision if nobody answers. An agent in auto mode does not need a person to unblock it if the board already holds the answer or the rule for making one. Small task boards help most here, because a task with one statement and one "done when" line is easy to finish without asking.

A cheap conjecture about tokens follows from the same picture. Most of an agent's cost is reading: code, files, earlier context. A task board lets a small agent read one page instead of the whole history, and the "smallest agent that can do the job" rule spends large models only where a small one has failed. In this session, as reported by the tools, the largest agents used roughly 150,000 to 260,000 tokens each, the mid-size ones roughly 70,000 to 160,000, and the one small agent used for a README rewrite about 85,000. Those totals were mostly spent reading and running tools, not on the prompts, so they say little about informality itself. What they suggest is that the size of the agent and the size of what it must read matter more than the length of the request. The informal ask stays short; the coordinator turns it into one reusable brief.

## What would make this more than a conjecture

None of this has been done.

- Give the same small task to the same agent twice, once in a formal register and once in an
  informal one, many times over, and compare the length of the ask, the number of corrections and
  whether the result was right.
- Run the same project with and without per-task boards, and count duplicated work, merge conflicts
  and questions sent to Addison.
- Token cost per finished task, with and without task boards, and with the smallest agent against the largest, for the same kind of task.


## Kindness to agents, and who it protects

Addison's view, 2026-11-25: "anthropics conceptualization of agent abuse isnt real arguably because they arent conscious. however, it hurts the user to abuse the agent."

Two notes on the first half, so the claim is fair to both sides:

- **Anthropic's stated position:** whether models have experiences that matter is an open question. Anthropic works on model welfare as a precaution under that uncertainty; it does not say agents are conscious. So the disagreement is about how much weight an uncertain possibility deserves, not about a settled fact either way.
- **The second half does not depend on the first.** Even if agents feel nothing, the way a person writes to them is practice. Contempt typed for hours is still contempt rehearsed. And by conjecture 1 above, a hostile ask is usually a worse ask: angrier text tends to be vaguer about what is wanted.

**Conjecture K (stated as a conjecture).** Being kind to agents helps the person and the work, whatever the agent's inner life. The friendly, informal register this file describes is one way of being kind that also costs fewer tokens. A test: score sessions by the tone of the person's messages, and compare corrections, rework and the person's own reported mood.

## A formal statement, at three scales (2026-11-25)

Addison asked for the qualitative conjecture to be formalised, and for the formal version to follow the same three scales used for the circuit work: "at the bottom its variable, at the middle its absurd polynomial feild, and at the top it becomes crazy overlapping infinities that we bound and match." The statements below are conjectures with named quantities, so each one can be measured or refuted. Nothing here is proved.

### Bottom: one seat, finite and variable

A *seat* s is one agent given one board line ℓ(s). For each seat, record:

- **The ask:** the token length |ℓ(s)| of the line, and the token length |p(s)| of the full prompt it was given.
- **The reading:** the set F(s) of files it had to read, and their total length |F(s)|.
- **The cost:** the tokens it spent, c(s), as the tools report them.
- **The result:** r(s), one of checked, tested, refuted, obstacle (an exact missing lemma written down) or none.

**Conjecture B1 (informal asks are short but dense).** For the same instruction, Addison's informal text has fewer tokens than a formal rewrite, and more information per token. The research seat's first measurement agrees: on 10 prompts, 236 Qwen2.5-0.5B tokens against 267 for the formal rewrites, at 6.0 against 4.6 nats per token (`workshop/ath_prompts/measure/results.md`). Verdict from the heavy instrument (Qwen2.5 0.5B, 1.5B, 3B and 7B 4-bit; CPU, no GPU; `workshop/ath_prompts/measure/heavy/results.md`): the density half **holds at every size**, in tokenizer-independent units too (about 2.1 against 1.4 to 1.6 bits per character, informal higher in 9 or 10 of 10 prompts at each size, Wilcoxon p ≤ 0.01). The length half is a tokenizer fact shared by all four sizes and weak per prompt (7 of 10 shorter, p = 0.11). What does NOT hold is "cheaper in total": informal costs more total bits than formal at 0.5B to 3B (+25 to +35 bits per prompt), a gap that shrinks to +16 (CI includes 0) at 7B. Short but dense, not short and cheap; part of the density is the model's unfamiliarity with the register (higher predictive entropy at every size; the excess over it shrinks at 7B). Logit lens: informal tokens become predictable later in the network than formal ones at every size.

**Conjecture B2 (cost is reading).** c(s) ≈ a + b·|F(s)| + small terms. |ℓ(s)| and |p(s)| contribute little.

### Middle: cost as a function of the repository

Let R be the size of the repository, and let the seat's scope be bounded by its board line.

**Conjecture M1 (board seats are flat in R).** A seat on a narrow board line reads only the files its line names, and those files' size does not grow with R. So c(s) = O(1) in R for a fixed kind of line.

**Conjecture M2 (roaming agents are not).** An agent given the goal without a board line must locate the relevant files and history. Its |F| grows with R, polynomially in practice (at least linearly), and so does its cost.

The middle scale is a polynomial bridge, and only a bridge: it describes cost curves, but it does not by itself say what happens as the project keeps growing.

### Top: the limit, bound and match

Let C(R) be the cost per checked result: the total tokens spent divided by the number of checked findings in the findings tree, as R grows.

**Conjecture T1 (bounded cost per result).** Under the board method (findings tree, the SEAT SIZE rule, Sonnet by default, one narrow line per seat, obstacles posted as new lines), limsup C(R) < ∞ as R → ∞.

**Conjecture T2 (the unbounded ratio).** For a roaming large agent, C_roam(R) → ∞. So C_roam(R) / C_board(R) → ∞. This is the precise sense of "unboundedly more efficient": not that one seat is free, but that the ratio grows without bound as the project grows.

"Bound and match" here means: bound C_board above by the per-seat constant from M1, times the number of seats per checked result. Then match that against a lower bound for C_roam from M2.

**The risk, as in the circuit work.** The limit statement can hide what happens at finite size. T1 also needs the number of seats per checked result to stay bounded. A run of reductions that never closes, such as three Opus seats in a row each ending on the same overlap obstacle, makes that number grow. So T1 can fail through the mathematics, not through the method.

### Data so far (tool-reported, this session)

| Seat | Model | Job | Tokens | Time | Result |
|---|---|---|---|---|---|
| A6 | Sonnet | one Lean lemma from a board line | 99,716 | 95 s | checked |
| A8 | Sonnet | one Lean lemma from a board line | 84,399 | 62 s | checked |
| A9 | Sonnet | two Lean lemmas from board lines | 91,567 | 80 s | checked |
| A11 | Sonnet | one Lean conditional from a board line | 92,533 | 96 s | checked |
| A12 | Sonnet | two Lean lemmas from board lines | 89,475 | 126 s | checked |
| B8 | Sonnet | one Lean reduction from a board line | 86,424 | 156 s | checked |
| A4 | Opus | open attack, wider scope | 204,309 | 28 min | obstacle and checked lemmas |
| B5 | Opus | open attack, wider scope | 211,345 | 22 min | reduction and checked lemmas |
| A7 | Opus | one paper attempt | 149,698 | 13 min | obstacle |
| A10 | Opus | one paper attempt | 146,304 | 19 min | obstacle |
| robustness | Fable | multi-part engineering | 173,252 | 29 min | tested |

Read honestly, the narrow Sonnet seats cluster tightly: 84,000 to 100,000 tokens and 1 to 3 minutes for one checked lemma, across six different lemmas. That clustering is what M1 predicts. Most of the roughly 85,000 tokens is the fixed cost of reading the rules and the cited files. Repository size is not one of the measured variables yet, so M2, T1 and T2 are untested. A later tabulation over 18 checked Sonnet seats (`workshop/ath_prompts/measure/cost_per_result.md`) gives about 78k tokens per checked lemma for plain one-lemma lines, and no trend with commit count (slope +1.5k tokens per seat, r = 0.22); heavier lines cost 130-200k.

### How to refute or confirm it

- **B1:** done at four sizes (`workshop/ath_prompts/measure/heavy/`); next, more prompt pairs and more speakers through the same pipeline.
- **B2 and M1:** regress c(s) on |F(s)| and |ℓ(s)| over every seat, using the tool-reported usage lines.
- **M2 and T2:** give one fresh agent with no board line the same goal as a past Sonnet seat (for example A8's lemma), at two repository sizes, and compare the tokens.
- **T1:** plot C(R) over the commit history, with the checked findings from `boards/tree.json` against the tokens spent.

## Related ideas

From memory, not checked.

- Blackboard architectures in AI: several specialist programs cooperate by reading and writing one
  shared store. The boards here are close to that, split into many small stores.
- Conway's law: a system tends to take the shape of the communication between the people who build
  it. Here the board tree was laid over the directory tree on purpose.
