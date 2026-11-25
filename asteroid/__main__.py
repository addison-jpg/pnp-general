import sys, os
if sys.version_info < (3, 9):
    sys.exit("asteroid needs Python 3.9 or newer; this is Python %d.%d (%s)" % (sys.version_info[0], sys.version_info[1], sys.executable))
# Works as `python -m asteroid` from the repository and as `python path/to/asteroid/__main__.py` from anywhere
# (the launchers in bin/ use the second form): the repository goes first on the module path, this folder comes off it.
_here = os.path.dirname(os.path.abspath(__file__))
sys.path[:] = [os.path.dirname(_here)] + [p for p in sys.path if p and os.path.abspath(p) != _here]
from asteroid.asteroid import main
sys.exit(main(sys.argv[1:]))
