# asteroid (.ath) for VS Code

Syntax highlighting for [asteroid](../../asteroid/SPEC.md) programs (`.ath` files): circuits, `claim … by lean`, `corpus`, `hunt`, `theorem … from … in …`, `#` comments, strings, paths, numbers and `->`.

## Install from the VSIX

1. Download `asteroid-0.1.0.vsix` from this folder.
2. In VS Code: Extensions view → `…` menu → **Install from VSIX…** → pick the file.
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

Not published to the Marketplace or Open VSX.

MIT licensed. Icon: the 4STeroid logo (`site/LOGO.md` for credits).
