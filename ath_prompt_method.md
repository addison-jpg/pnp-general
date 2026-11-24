# A conjecture about informal prompting and boards

This file is a conjecture about a way of prompting. It was written from one long working session in
this repository on 2026-11-24. It is an opinion with some evidence from that day. Nothing in it was
measured, and nothing in it is proved.

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


## Related ideas

From memory, not checked.

- Blackboard architectures in AI: several specialist programs cooperate by reading and writing one
  shared store. The boards here are close to that, split into many small stores.
- Conway's law: a system tends to take the shape of the communication between the people who build
  it. Here the board tree was laid over the directory tree on purpose.
