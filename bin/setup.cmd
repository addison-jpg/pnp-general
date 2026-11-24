@echo off
rem One-time: make a private Python environment INSIDE this folder (.venv) with numpy and matplotlib.
rem Nothing goes to your user Python or AppData. Delete the .venv folder to undo it.
setlocal
set "HERE=%~dp0.."
python -m venv "%HERE%\.venv" || exit /b 1
"%HERE%\.venv\Scripts\python.exe" -m pip install --quiet numpy matplotlib || exit /b 1
echo ready: %HERE%\.venv
