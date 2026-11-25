# Model-aware routing (noted, not built)

Source: Addison, 2026-11-25: "kill the board concept, all it has to do is consider effort/model and act accordingly".

**The idea:** a small routing layer in the memory core decides, per task, which model should do it and how much effort to spend, instead of a board that lists everything.

**Where it's safe to automate (plumbing):** regenerating views, committing, running checks, reference checks, retests. A small model can do these reliably.

**Where it isn't (judgment):** deciding join vs analogy vs rhyme, deciding whether a claim is checked or only tested, deciding whether a reduction covers all n, and anything that goes public. These need a stronger model, or Addison.

**The open question, which is Addison's to decide:** whether to retire the board. Retiring it deletes the record of what each seat was asked to do, so the routing layer would need that record in its own store first. Not built, and nothing has been deleted.
