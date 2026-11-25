# Run asteroid straight from this folder: nothing is installed anywhere else. PowerShell form of bin\asteroid.cmd.
# Python used: the repository's own .venv if bin\setup made one, otherwise py -3, then python, then python3.
# If PowerShell refuses to run scripts, use bin\asteroid.cmd, which does the same.
$ErrorActionPreference = 'Continue'
$here = Split-Path -Parent $PSScriptRoot
function Test-Python([string[]]$Cmd) {
    $exe = $Cmd[0]; $rest = @(); if ($Cmd.Length -gt 1) { $rest = $Cmd[1..($Cmd.Length - 1)] }
    try {
        & $exe @rest -c "import sys; sys.exit(0 if sys.version_info >= (3, 9) else 1)" *> $null
        return ($LASTEXITCODE -eq 0)
    } catch { return $false }
}
$candidates = @(
    @((Join-Path (Join-Path (Join-Path $here '.venv') 'Scripts') 'python.exe')),
    @((Join-Path (Join-Path (Join-Path $here '.venv') 'bin') 'python')),
    @('py', '-3'), @('python'), @('python3'))
$py = $null
foreach ($c in $candidates) { if (Test-Python $c) { $py = $c; break } }
if ($null -eq $py) {
    [Console]::Error.WriteLine('asteroid: no Python 3.9 or newer found. Tried .venv, py -3, python and python3.')
    [Console]::Error.WriteLine('          Install Python from https://www.python.org/downloads/ and run this again.')
    exit 1
}
$exe = $py[0]; $rest = @(); if ($py.Length -gt 1) { $rest = $py[1..($py.Length - 1)] }
$main = Join-Path (Join-Path $here 'asteroid') '__main__.py'
& $exe @rest -X utf8 $main @args
exit $LASTEXITCODE
