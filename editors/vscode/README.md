# asteroid (.ath) for VS Code

Syntax highlighting for [asteroid](../../asteroid/SPEC.md) programs (`.ath` files): circuits, `claim … by lean`, `corpus`, `hunt`, `theorem … from … in …`, `#` comments, strings, paths, numbers and `->`.

## Install from the VSIX

Search **asteroid** in the Extensions view, or [open it on the Marketplace](https://marketplace.visualstudio.com/items?itemName=asteroid.asteroid). Offline: download `asteroid-0.1.0.vsix` from this folder, then
   Extensions view → `…` menu → **Install from VSIX…** → pick the file.
   Or: `code --install-extension asteroid-0.1.0.vsix`

## What it does

- Language id `asteroid`, extension `.ath`.
- TextMate grammar built from `asteroid/SPEC.md` and every `.ath` file in the repository.
- `#` toggles line comments; brackets auto-close; `circuit … end` indents.

## Build and test

```
cd editors/vscode
npm install
npm test                       # tokenizes every .ath in the repo, fails on unscoped or illegal tokens
npx @vscode/vsce package       # writes asteroid-0.1.0.vsix
```

Published on the VS Code Marketplace (`asteroid.asteroid`). Not on Open VSX yet.

MIT licensed. Icon: the 4STeroid logo (`site/LOGO.md` for credits).
