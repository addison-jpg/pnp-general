@echo off
rem bin\sync.cmd: keep this folder and GitHub in step (runs bin\sync.ps1). Usage: bin\sync  [ "message" | --check ]
powershell -NoProfile -ExecutionPolicy Bypass -File "%~dp0sync.ps1" %*
exit /b %errorlevel%
