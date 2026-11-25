# PyInstaller spec of the one-file `asteroid`: the full Python implementation, every extension, numpy and matplotlib.
# Build from the repository root, in a Python that has pyinstaller, numpy and matplotlib (and nothing heavy):
#   pyinstaller --noconfirm --distpath DIR --workpath DIR packaging/universal/asteroid.spec
# Not inside: torch and transformers (ext_qwen and `ask --model` say the model is missing), Lean (a run proves only
# when it finds the repository and `lake`), tkinter where the Python has none.
import glob, os, sys
from PyInstaller.utils.hooks import collect_submodules

R = os.path.abspath(".")
if not os.path.isfile(os.path.join(R, "asteroid", "universal_exe.py")): sys.exit("run pyinstaller from the repository root")
SEARCH = os.path.join(R, "one-not", "tools", "search")
mods = lambda d: sorted(os.path.basename(f)[:-3] for f in glob.glob(os.path.join(R, d, "*.py")))

# The interpreter imports its extensions by name (asteroid/ext_*.py, found with glob): list them all.
hidden = ["asteroid." + m for m in mods("asteroid") if m not in ("__main__", "universal_exe", "idle_exe")]
hidden += ["boards", "core", "conjectures", "continuous", "hunt", "matplotlib.backends.backend_agg"]
# Repository checks (`check "python3 -I FILE.py"`) and hunt run as child programs of this binary, with its Python:
# the whole standard library is packed, so such a file finds any standard module it imports.
SKIP = {"tkinter", "turtle", "turtledemo", "idlelib", "test", "lib2to3", "ensurepip", "venv", "antigravity", "this"}
for name in sorted(sys.stdlib_module_names):
    if name in SKIP or name.startswith("_") or (os.name != "nt" and name in ("msilib", "winreg", "winsound", "msvcrt", "_winapi")): continue
    try: __import__(name)
    except Exception: continue
    hidden.append(name)
    if hasattr(sys.modules[name], "__path__"):
        hidden += collect_submodules(name, filter=lambda n: ".test" not in n and "idle_test" not in n)
try:
    import tkinter; hidden += ["tkinter", "tkinter.ttk", "tkinter.font", "tkinter.scrolledtext", "tkinter.filedialog", "tkinter.messagebox"]
except ImportError: pass

# Files read by path, so a run outside a repository still has them (inside one, the repository's own are used).
datas = [(f, "asteroid") for f in glob.glob(os.path.join(R, "asteroid", "*.py"))]
datas += [(os.path.join(R, "asteroid", "demo.ath"), "asteroid")]
datas += [(f, os.path.join("one-not", "tools", "search")) for f in glob.glob(os.path.join(SEARCH, "*.py"))]
datas += [(os.path.join(R, "boards.py"), "."), (os.path.join(R, "core", "ontology", "ask.py"), os.path.join("core", "ontology"))]

a = Analysis([os.path.join(R, "asteroid", "universal_exe.py")], pathex=[R, SEARCH], hiddenimports=hidden, datas=datas,
             excludes=["torch", "transformers", "tensorflow", "jax", "scipy", "pandas", "IPython", "PyQt5", "PyQt6", "PySide2", "PySide6", "wx", "gi"],
             noarchive=False)
pyz = PYZ(a.pure)
icon = os.path.join(R, "packaging", "universal", "icon.ico")
exe = EXE(pyz, a.scripts, a.binaries, a.datas, [], name="asteroid", console=True, strip=False, upx=False,
          icon=icon if os.path.isfile(icon) else None)
