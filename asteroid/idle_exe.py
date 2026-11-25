"""The old entry point of the Windows .exe (PyInstaller, until 2026-11-25): starts `asteroid idle`, Lean off. No workflow builds it now;
the one-file asteroid is built from asteroid/universal_exe.py (packaging/universal/asteroid.spec).
`asteroid-idle.exe --selftest` runs hello.ath without a window and exits 0 if it evaluates."""
import sys
from asteroid.idle import main
sys.exit(main(sys.argv[1:]))
