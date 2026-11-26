# Draft: registering .ath with GitHub Linguist

Status: draft only. Nothing has been submitted, and no pull request is open.

## What Linguist needs (to be checked against its current CONTRIBUTING before submission)

1. An entry in `lib/linguist/languages.yml` (draft: `languages.yml.draft`).
2. A TextMate grammar for highlighting. The repo already has one: `editors/vscode/syntaxes/asteroid.tmLanguage.json` (scope `source.asteroid`). Linguist vendors grammars from their own repo, so the grammar is proposed there separately.
3. A sample file in `samples/` (draft: `samples/little.ath`, the first 20 lines of `little.ath`).
4. Usage: Linguist adds a language only when enough public GitHub files use it. This is the real gate. Our repo alone will not meet it, and a submission made before then will be closed.

## Honest limits

- "Easy" is not guaranteed. The usage threshold is set by Linguist, and it may not be met until the language has public use beyond this repo.
- The language_id and color are not ours to choose unilaterally; they are set at submission time.

## Not claimed

- That `.ath` is a recognized language today. It is not, on GitHub.
- That the file type and the language are the same idea in the scientific sense. That is a position for the spec to state, not a result here.

## Next (needs the user)

- Confirm you want the Linguist pull request opened, when Linguist's current requirements have been read.
- Decide whether to open it now (usage gate likely not met) or after more public use.
