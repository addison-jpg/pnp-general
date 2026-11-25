@echo off
rem Once: make a private Python environment INSIDE this folder (.venv) with numpy and matplotlib.
rem Nothing goes to your user Python or AppData. Delete the .venv folder to undo it. Safe to run again.
setlocal
for %%I in ("%~dp0..") do set "HERE=%%~fI"
set "VPY=%HERE%\.venv\Scripts\python.exe"
if not exist "%VPY%" goto make
"%VPY%" -m pip --version >nul 2>&1
if errorlevel 1 goto make
echo setup: using the .venv that is already here
goto install
:make
set "PY=py"
set "PYARG=-3"
"%PY%" %PYARG% -c "import sys; sys.exit(0 if sys.version_info >= (3, 9) else 1)" >nul 2>&1
if not errorlevel 1 goto venv
set "PY=python"
set "PYARG="
"%PY%" -c "import sys; sys.exit(0 if sys.version_info >= (3, 9) else 1)" >nul 2>&1
if not errorlevel 1 goto venv
echo setup: no Python 3.9 or newer found. Tried py -3 and python. 1>&2
echo        Install Python from https://www.python.org/downloads/ and run this again. 1>&2
exit /b 1
:venv
echo setup: making "%HERE%\.venv"
"%PY%" %PYARG% -m venv --clear "%HERE%\.venv"
if errorlevel 1 goto novenv
if exist "%VPY%" goto install
:novenv
echo setup: could not make the environment. 1>&2
exit /b 1
:install
"%VPY%" -m pip install --quiet --disable-pip-version-check numpy matplotlib
if errorlevel 1 goto nopip
echo ready: "%HERE%\.venv"   Check with: bin\asteroid.cmd --doctor
exit /b 0
:nopip
echo setup: could not install numpy and matplotlib. Is there a network? 1>&2
echo        asteroid still runs: only plots and the continuous and mixed lines are skipped. Run this again later. 1>&2
exit /b 1
