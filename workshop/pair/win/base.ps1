# The Windows terminal, per TERMINAL.md. Thin: it only dispatches.
# Windows PowerShell 5.1 compatible.

$programs = @{
    'hello' = 'hello.ath'
    'big'   = 'big.ath'
    'bus'   = 'workshop/bus/bus.ath'
}

function Get-Engine {
    if ($env:ASTEROID) { return $env:ASTEROID }
    if (Test-Path -LiteralPath '.\asteroid.exe') { return '.\asteroid.exe' }
    return 'ast.exe'
}

Write-Output 'ath> (:big :hello :bus :quit)'
while ($true) {
    $line = Read-Host -Prompt 'ath> '
    if ($line -eq ':quit') { exit 0 }
    if ($line -match '^:(hello|big|bus)$') {
        $engine = Get-Engine
        & $engine --no-lean $programs[$Matches[1]]
        Write-Output ('exit {0}' -f $LASTEXITCODE)
    }
    else {
        Write-Output 'commands: :big :hello :bus :quit'
    }
}
