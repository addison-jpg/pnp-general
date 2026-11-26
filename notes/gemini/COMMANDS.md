# Copy-paste commands

Run these from the repository folder (`pnp-general`).

Install asteroid (once):

```bash
pip install -e .
```

Run the starter program:

```bash
asteroid hello.ast
```

Run every program:

```bash
asteroid test
```

Gemini dry run (sends nothing; shows exactly what would be sent):

```bash
python3 -m asteroid.ext_gemini notes/gemini/EXCERPT.txt "Is this lemma true?"
```

Gemini send (only after the owner approves; key only from the environment, never a file):

```bash
GEMINI_API_KEY=PASTE_KEY_HERE python3 -m asteroid.ext_gemini notes/gemini/EXCERPT.txt "Is this lemma true?" --send
```
