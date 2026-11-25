# Once: make a private Python environment INSIDE this folder (.venv) with numpy and matplotlib.
# Nothing goes to your user Python or AppData. Delete the .venv folder to undo it. Safe to run again.
# PowerShell form of bin\setup.cmd. If PowerShell refuses to run scripts, use bin\setup.cmd.
$ErrorActionPreference = 'Continue'
$here = Split-Path -Parent $PSScriptRoot
$venv = Join-Path $here '.venv'
function Test-Python([string[]]$Cmd) {
    $exe = $Cmd[0]; $rest = @(); if ($Cmd.Length -gt 1) { $rest = $Cmd[1..($Cmd.Length - 1)] }
    try {
        & $exe @rest -c "import sys; sys.exit(0 if sys.version_info >= (3, 9) else 1)" *> $null
        return ($LASTEXITCODE -eq 0)
    } catch { return $false }
}
function Get-VenvPython {
    foreach ($p in @((Join-Path (Join-Path $venv 'Scripts') 'python.exe'), (Join-Path (Join-Path $venv 'bin') 'python'))) {
        if (Test-Path -LiteralPath $p) { return $p }
    }
    return $null
}
$vpy = Get-VenvPython
$reuse = $false
if ($vpy -and (Test-Python @($vpy))) {
    try { & $vpy -m pip --version *> $null; $reuse = ($LASTEXITCODE -eq 0) } catch { $reuse = $false }
}
if ($reuse) {
    Write-Output 'setup: using the .venv that is already here'
} else {
    $py = $null
    foreach ($c in @(@('py', '-3'), @('python'), @('python3'))) { if (Test-Python $c) { $py = $c; break } }
    if ($null -eq $py) {
        [Console]::Error.WriteLine('setup: no Python 3.9 or newer found. Tried py -3, python and python3.')
        [Console]::Error.WriteLine('       Install Python from https://www.python.org/downloads/ and run this again.')
        exit 1
    }
    $exe = $py[0]; $rest = @(); if ($py.Length -gt 1) { $rest = $py[1..($py.Length - 1)] }
    Write-Output "setup: making $venv"
    & $exe @rest -m venv --clear $venv
    $vpy = Get-VenvPython
    if ($LASTEXITCODE -ne 0 -or -not $vpy) {
        [Console]::Error.WriteLine('setup: could not make the environment.')
        exit 1
    }
}
& $vpy -m pip install --quiet --disable-pip-version-check numpy matplotlib
if ($LASTEXITCODE -ne 0) {
    [Console]::Error.WriteLine('setup: could not install numpy and matplotlib. Is there a network?')
    [Console]::Error.WriteLine('       asteroid still runs: only plots and the continuous and mixed lines are skipped. Run this again later.')
    exit 1
}
Write-Output "ready: $venv   Check with: bin\asteroid.ps1 --doctor"
exit 0
