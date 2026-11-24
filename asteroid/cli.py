"""Entry point for `pip install -e .`: the command `asteroid` (same as `python3 -m asteroid`). Run it from the repository root."""
import sys

def cli():
    from asteroid.asteroid import main
    sys.exit(main(sys.argv[1:]))
