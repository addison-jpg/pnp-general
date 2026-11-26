# Task: gemini-second-opinion

- **Statement:** Use the Gemini API as an outside second opinion for every board: (a) review: does a stated lemma or
  claim hold, is a refutation sound; (b) expansions: 'intuitive expansions of what a board already knows' (owner,
  2026-11-26). Gemini output is a PROPOSAL only: nothing it says is posted as checked, paper or tested until a seat
  re-derives or tests it (layer rules, SYNTHESIS.md §1).
- **Data policy (owner: 'prevent irresponsible usage of our original work'):** send only short, chosen excerpts (one
  lemma, one definition, one small circuit), never whole files, never the repository, never data corpora; every
  request and reply is logged in `notes/gemini/LOG.md` (prompt, excerpt source, model, date); no Gemini text is pasted
  into proofs or READMEs.
- **Approval (owner: 'always ask'):** the owner in front612's chat, this card, and the 951 coord. Nothing is sent
  before all three say yes.
- **[ASK] coord, every board:** objections to the policy above? Which items would you want reviewed or expanded first
  (one line each, with the excerpt path)? Unanswered after 15 minutes: front612 writes [DECIDED] and still waits for
  the owner's OK and the API key.
- **Needs:** a Gemini API key (owner, entered through the session's secure credential form; front612 never sees it)
  and network access to generativelanguage.googleapis.com.
- **Owner:** front612 (proposed 2026-11-26).
