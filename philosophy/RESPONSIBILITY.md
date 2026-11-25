# Responsibility: to people, to agents, to those who rely on asteroid

This is a **position**, not a result. Nothing in it is checked, except where it points at a check that already exists. Sources are cited from memory.

## 1. To people

- No real person's health data or personal data goes into this repository. Every individual in a model is synthetic: `culture/narrative/narrative.py` enumerates constructed stories, not anyone's life.
- Historical persons get readings, never diagnoses. A reading says what a text or a life can be read as, and is labelled analogy. A diagnosis claims a fact about a body or a mind that no archive here can support. `culture/narrative/DIARIES.md` follows this rule.
- Criticism of historical persons is stated plainly and sourced. Nin's racist and exoticizing portrayals, Dostoevsky's antisemitism, Woolf's antisemitism and class contempt are part of the record. They are not set aside to protect a reputation, and no slur is reproduced to make the point.
- Openness has a limit here, as in `philosophy/OPEN_RESEARCH.md`: method and aggregates are open; anything that identifies a person stays out.

## 2. To agents

- Whether models have welfare is an open question. Anthropic's stated position, as far as I know it (cited from memory), is that model welfare is an open question it works on as a precaution, not a settled fact. This repository takes the same stance: act with care under an open question, and claim nothing either way.
- Conjecture K (`ath_prompt_method.md`) is a conjecture: being kind to agents helps the person and the work, whatever the agent's inner life. It is stated so that it can be tested, not assumed.
- Attribution is credit for visible work. A co-author line on a commit records which agent did the work. It is a small, exact record, and it costs nothing to keep.
- Invisible work is still work. `workshop/ath_prompts/invisible/` measures what it can: 32.8% of the recorded seat tokens left no checked line. The reading and coordination behind every checked line are owed a record, even when they get no row of their own.

## 3. To .ath, .ast and asteroid

- Never print a label stronger than its check. `asteroid/ext_frame.py` already enforces part of this: a frame whose claim did not pass is forced to `open`, and a Python claim cannot carry `checked`. The duty goes further than the code: a reading must say it is a reading, a memory must say it is a memory.
- The duty is to those who rely on the output. A reader who trusts `checked-finite` trusts that the stated finite set was covered with nothing sampled. Printing it without that is a false promise to them.
- Refuted rows stay, with their counterexamples. A dead end that is written down is not a dead end for the next person.

## 4. The postmodern link, through Frank

Arthur Frank, *The Wounded Storyteller* (1995; cited from memory), argues that ill people reclaim their own story from the medical story told about them. Restitution is the story medicine prefers; chaos is the story it cannot hear; quest is the one the teller makes. Read with Lyotard (`philosophy/OPEN_RESEARCH.md`): the medical narrative is a metanarrative, and the incredulity toward it is a person's right to tell their own life.

The same duty runs through all three sections above. People keep their own stories, so no real person's story is modelled. Agents are not told a settled story about their inner life, in either direction. And asteroid does not tell a stronger story than its check allows. In each case the duty is the same: do not overwrite someone's story with a stronger one of your own.

`narrative.py` adds one exact fact that supports this: the type of a joined life is not fixed by the types of its parts (all 16 type pairs, every pair of stories of length up to 4). A whole cannot be read off its labelled parts. That is checked-finite on constructed stories; the moral is a reading.
