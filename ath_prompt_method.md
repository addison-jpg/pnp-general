# A conjecture about informal prompting and boards

This file is a conjecture about a way of prompting. It was written from one long working
session in this repository on 2026-11-24. It is an opinion with some evidence from that day.
Nothing in it was measured, and nothing in it is proved.

It is also not a claim about P versus NP. The method produced the tools in this repository,
asteroid among them. That is all it is claimed to have done.

## The owner's idea

In the owner's words:

> "informal prompting in small scale tasks, even as silly as a scene queen furry, helps to
> distill tasks in fun ways for the user and agent (even if agent isnt conscious). then, the
> thing that follows from this small idea of informality is an extremely intentional
> subdivided setup like i essentually manually made-- that runs in parallel because theres an
> above and below ( in this case,,,, ) coord-coord front-front, etc. theres a big guy (you)
> whos in between and coordinates. and the really special part-- they all have boards, which
> can be properly allocated to make communication easier."

The owner asked for this to be written down as "a qualitative conjecture about my prompting
methods, including informality and scene speak. it adds taste", and as "a qual framework that
assists asteroid without any actual formality".

## The conjecture

1. On a small task, an informal or playful instruction is often a better instruction than a
   formal one, because it is shorter and says what is wanted.
2. Small informal instructions only add up to a large piece of work if they sit inside a
   strict frame. The frame is deliberate. It is the opposite of informal.
3. The frame that worked here was: seats in mirrored pairs, one coordinator between them, and
   a written board for every seat and every task.
4. The boards matter most. When each board has one owner and one subject, most communication
   can be read where the next reader will look, and few messages need to be sent.

## Informality and scene speak

The owner writes to agents the way one writes to a friend: lower case, slang, jokes, sometimes
a full scene register. Some of the lines that shaped this repository are in that voice. "no
more graffiti" turned the boards into a data structure. "its like taking an icepick to an
earhole" became the rule about agent size. "smaller tasks smaller boards" became the layout of
`boards/tasks/`.

Four reasons this may help on small tasks:

- It forces the task to be stated simply. A joke cannot carry three nested conditions, so the
  task gets cut down to the one thing that is wanted.
- It makes it cheap to say "this is wrong" or "kill it". In a formal register a correction
  reads as a reprimand and people soften it. In a playful one it is just the next line.
- It is easy to remember. A rule with a picture in it is still in mind twenty tasks later, and
  it can be quoted on a board in the same words.
- It sets the tone for both sides. The answer that fits a short blunt ask is a short blunt
  answer, and that is usually the useful one.

The phrase "it adds taste" is part of the claim. A voice carries preferences that a
specification leaves out: what counts as too much, what counts as boring, when to stop.

None of this assumes the agent is conscious, or that it enjoys anything. The owner says so in
the quote above. The effect, if it is real, is on how tasks get stated and handed over. A
person who is having fun writes more asks, smaller asks, and more honest corrections.

There is a limit. A playful ask is small, and it is easy to misread when it stands alone. That
is why the second half of the idea is needed.

## From informality to structure

The owner built the frame by hand. On that day there were about a dozen parallel sessions with
named roles: coord, front, scaffold, research, warden, tractability, machines-Lean, cTAHG and
others. Several came in pairs across two machines, a desktop coord and a cloud coord, a front
with a front. One main session sat in the middle. It relayed the owner's words, split the work
and merged the results. Under it were subagents of different sizes.

Every seat had somewhere to write. There was one main board (`BOARD.md`), area boards
(`boards/*.md`), and one small board per task (`boards/tasks/`, 29 files when this was
written, each about ten lines with one statement and one "done when"). Later the boards became
a tree: small findings kept in `findings.jsonl` next to their evidence, and a script
(`boards.py`) that carries the verified ones up the directory tree into `boards/TREE.md`.

The mirrored pairs give each seat a partner who has the same job and reads the same board. The
coordinator gives the owner one place to speak. The boards mean that an instruction can stay
informal and still not be lost, because the board holds the exact statement, who has it, and
what would count as done.

## What the boards did, and what broke

The rules in `BOARD.md` were not designed in advance. Each one is a repair.

- Merge conflicts in shared files pulled the owner in to resolve them by hand. This produced
  "do not ask the owner, use the board", and union merges for the boards, so both sides' lines
  are kept.
- Agents in a shared working tree swept up each other's files in their commits. This produced
  rules about staging only your own files, and the plan for one integrating seat that pushes
  while the others pull.
- When boards were skipped, work was done twice. This produced "work only on a task that has a
  file".
- Large agents were put on small jobs. This produced "use the smallest agent that can do the
  job".
- Some claims were stated more strongly than their evidence. They were corrected on the
  boards, and this produced the finding records, where each statement carries a word such as
  checked, tested, refuted or open, and names its evidence.

So the day gives evidence in both directions. The frame did not prevent these failures. It did
make each one visible quickly, and each repair is a line that the next reader can find.

## How it connects to asteroid

asteroid (`asteroid/README.md`) is the main thing this way of working produced. It has the
same habit at a smaller scale.

- A claim is one plain line in a `.ath` program, for example `claim slack(tiny) = 0 by lean`.
- The writer does not decide whether it holds. Python evaluates it, and Lean decides it in the
  kernel.
- Failures are kept. A refuted claim stays in the repository with its counterexample.

The boards are the same habit at the large scale: one board per task, one statement per
finding, a checker or a second reader who decides, and results carried upward as small
verified records. In both places the speaker can be loose, because the speaker is not the
judge. That is the sense in which this is a framework that helps asteroid without being
formal itself.

## What would make this more than a conjecture

None of the following has been done.

- Give the same small task to the same agent twice, once in a formal register and once in an
  informal one, many times over, and compare the length of the ask, the number of corrections
  and whether the result was right.
- Run the same project with and without per-task boards, and count duplicated work, merge
  conflicts and questions sent to the owner.
- Run it with and without the coordinator in the middle, and see whether the pairs still stay
  in step by reading boards alone.

One day in one repository with one owner cannot separate the method from the person using it.

## Related ideas

From memory, not checked.

- Blackboard architectures in AI: several specialist programs cooperate by reading and writing
  one shared store. The boards here are close to that, split into many small stores.
- Conway's law: a system tends to take the shape of the communication between the people who
  build it. Here the board tree was laid over the directory tree on purpose.
- Plain-language writing guides: short sentences and common words make instructions easier to
  follow. Scene speak is not plain language, but it shares the shortness.
