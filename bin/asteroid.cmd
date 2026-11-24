@echo off
rem Run asteroid straight from this folder: nothing is installed anywhere else.
rem Uses the repository's own .venv if bin\setup made one, otherwise python from PATH.
setlocal
set "HERE=%~dp0.."
set "PY=%HERE%\.venv\Scripts\python.exe"
if not exist "%PY%" set "PY=python"
set "PYTHONPATH=%HERE%;%PYTHONPATH%"
"%PY%" -m asteroid %*
