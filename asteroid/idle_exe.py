"""Entry point of the Windows .exe (built by .github/workflows/exe.yml with PyInstaller): starts `asteroid idle`, Lean off.
`asteroid-idle.exe --selftest` runs hello.ath without a window and exits 0 if it evaluates."""
import sys
from asteroid.idle import main
sys.exit(main(sys.argv[1:]))
