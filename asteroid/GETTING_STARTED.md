# Getting started with asteroid in Git Bash

This page takes you from nothing installed to your own circuit checked by asteroid. It assumes Windows and
Git Bash, and that you have not used asteroid before. Every command is run from inside the project folder
unless it says otherwise.

## 1. What you need

- Git for Windows, which gives you Git Bash. Get it from git-scm.com and accept the defaults.
- Python 3.9 or newer, from python.org. In the installer, tick "Add python.exe to PATH". The `python3`
  shortcut that Windows offers from the Microsoft Store does not count: it is a stub, and asteroid
  cannot use it.
- Optional: Lean, installed through elan. Without it asteroid still evaluates every claim. With it,
  claims marked `by lean` are proved by the Lean kernel, not only evaluated. You can add it later (section 5).

Open Git Bash and check Python:

```bash
python --version
```

In cmd or PowerShell the same check is `py -3 --version`. Any 3.9 or newer is fine.

## 2. Get the code and set it up

```bash
git clone https://github.com/addison-jpg/pnp-general.git
```

```bash
cd pnp-general
```

```bash
bin/setup
```

`bin/setup` makes a private `.venv` folder inside `pnp-general` and installs numpy and matplotlib into it.
Nothing goes into AppData or into your user Python. To undo it, delete the `.venv` folder. In cmd or
PowerShell, run `bin\setup.cmd` instead.

## 3. Run the first program

```bash
bin/asteroid hello.ath
```

In cmd or PowerShell: `bin\asteroid.cmd hello.ath`. You should see something like this:

```
4: hello loaded (4 inputs, 3 gates)
5: hello: gates 3, nots 0, base 3, witness 3, orwitness 3, correct True
6: claim correct(hello): python TRUE (correct = True)
7: claim gates(hello) = base(hello): python TRUE (3 = 3)
...
wrote asteroid/out/hello.png
```

What the lines mean:

- `hello loaded` says the circuit file was read: 4 inputs, 3 gates. The number at the start of each line
  is the line of the `.ath` program that produced it.
- The `hello: gates 3, nots 0, base 3 ...` line is what `show` prints. It counts the gates and the NOT
  gates, gives `base` (the fewest gates the theory says are needed without NOT), and says whether the
  circuit is `correct` on every input.
- Each `claim` line reports one claim. `TRUE` or `FALSE` is the Python evaluation, with the numbers it
  compared in brackets.
- `wrote asteroid/out/hello.png` is the plot. Open that file to look at it.
- The last lines depend on Lean. With Lean installed they say `proved: ...` for the claims marked
  `by lean`. Without it you get `not proved: 3 claims were only evaluated`, and that is fine for now.

## 3b. Interactive

Addison asked for "basically Python IDLE", so asteroid has two interactive faces, both built on pieces that already ship with Python:

```bash
bin/asteroid          # the prompt: type asteroid lines, state stays between lines
bin/asteroid idle     # the window: editor, Run (F5), output, plot preview
```

The prompt is built on the standard library's `cmd` module (`cmd.Cmd`, with `readline` history where the platform has it). Each line goes through the same line evaluator a file uses. Meta commands: `:help`, `:load FILE.ath`, `:lean on|off` (off by default, so it is fast), `:save FILE.ath`, `:quit` (Ctrl-D too). Colours show only on a terminal and not when `NO_COLOR` is set; `--no-color` turns them off. The window is built on `tkinter` and Python's own IDLE code (`idlelib`: its colorizer and percolator); on Windows `tkinter` ships with python.org Python.

## 4. Write your own

A circuit is a `.bench` file. Save this as `demo.bench` in the `pnp-general` folder. It has four
inputs, two outputs and five gates, one of them a NOT:

```
# demo: two outputs, the OR of {x0,x1,x2} and the OR of {x2,x3}
INPUT(x0)
INPUT(x1)
INPUT(x2)
INPUT(x3)
OUTPUT(y)
OUTPUT(z)
#@ or y = x0 x1 x2
#@ or z = x2 x3
a = OR(x0, x1)
y = OR(a, x2)
z = OR(x2, x3)
spare = OR(x0, x1)
n = NOT(x3)
```

The `#@ or` lines say what each output is supposed to compute: `y` is the OR of x0, x1 and x2. Everything
else is the ordinary format, described in [`BENCH.md`](BENCH.md). Two of the gates (`spare` and `n`) do no
work. They are there so that the circuit has more gates than it needs.

Now the program, saved as `demo.ath` in the same folder:

```
let c = load demo.bench
show c
claim correct(c) by lean
claim gates(c) >= base(c)
claim hyps(c) by lean
```

Paths in a `load` line are counted from the project folder, so keep both files there. Run it:

```bash
bin/asteroid demo.ath
```

Without Lean you should see:

```
1: c loaded (4 inputs, 5 gates)
2: c: gates 5, nots 1, base 3, witness 4, orwitness 4, correct True
3: claim correct(c): python TRUE (correct = True)
4: claim gates(c) >= base(c): python TRUE (5 >= 3)
5: claim hyps(c): python TRUE (hyps = True)
not proved: 2 claims were only evaluated (no proof checker in this run)
claims: 3 true, 0 false
```

The three claims: `correct` says each output computes the OR the directives asked for, on every input.
`gates(c) >= base(c)` says the circuit is not smaller than the lower bound (5 against 3). `hyps` says the side
conditions of the theorem hold for this circuit.

To see a FALSE result, change the line `z = OR(x2, x3)` to `z = OR(x2, x1)` and run again. The output gets:

```
2: c: gates 5, nots 1, base 3, witness 4, orwitness 4, correct False
3: claim correct(c): python FALSE (correct = False)
...
claims: 2 true, 1 false
```

FALSE means the claim does not hold for this circuit, not that asteroid broke. Here `z` no longer
computes the OR of x2 and x3. Read the numbers in the brackets to see what was compared, fix the circuit
(or the claim), and run again.

## 5. Add Lean so claims are proved

Install elan, the Lean version manager, from Git Bash:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Close Git Bash and open it again so that `lake` is on the PATH. Then fetch the prebuilt libraries. This
is several GB and you do it once:

```bash
cd one-not/lean && lake exe cache get && cd ../..
```

Run the first program again:

```bash
bin/asteroid hello.ath
```

The claims marked `by lean` now end in `proved: ...` lines. That means the Lean kernel checked them, which is
stronger than the Python evaluation.

## 6. When something goes wrong

```bash
bin/asteroid --doctor
```

This checks Python, the `.venv`, matplotlib and Lean, and says what is missing. Older checkouts do not
have it: run `git pull` and try again.

- "python not found": install Python from python.org with the PATH box ticked, then open a new Git
  Bash window. If `python` still fails, try `py -3` in place of `python`.
- Plots are skipped, with a note about matplotlib: run `bin/setup` again.
- Lean not found: evaluate-only runs are fine. Do section 5 when you want proofs.
- A path with spaces, such as `bin/asteroid "my files/demo.ath"`: put it in quotes. The same goes for
  a folder with spaces in its name when you `cd` into it.

## 7. Where to go next

- [`README.md`](README.md): the manual for the whole language.
- [`SPEC.md`](SPEC.md): the grammar of `.ath` programs.
- [`BENCH.md`](BENCH.md): the `.bench` circuit format.
- [`programs/`](programs/): the programs the project itself uses. Reading them is the quickest way to see
  what a real one looks like.
