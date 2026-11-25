@echo off
rem Run asteroid straight from this folder: nothing is installed anywhere else.
rem Python used: the repository's own .venv if bin\setup.cmd made one, otherwise py -3, then python.
setlocal
for %%I in ("%~dp0..") do set "HERE=%%~fI"
set "PY=%HERE%\.venv\Scripts\python.exe"
set "PYARG="
if exist "%PY%" goto run
set "PY=py"
set "PYARG=-3"
"%PY%" %PYARG% -c "import sys; sys.exit(0 if sys.version_info >= (3, 9) else 1)" >nul 2>&1
if not errorlevel 1 goto run
set "PY=python"
set "PYARG="
"%PY%" -c "import sys; sys.exit(0 if sys.version_info >= (3, 9) else 1)" >nul 2>&1
if not errorlevel 1 goto run
echo asteroid: no Python 3.9 or newer found. Tried .venv, py -3 and python. 1>&2
echo           Install Python from https://www.python.org/downloads/ and run this again. 1>&2
exit /b 1
:run
set "PYTHONPATH=%HERE%"
"%PY%" %PYARG% -X utf8 "%HERE%\asteroid\__main__.py" %*
exit /b %ERRORLEVEL%
