# bin/sync.ps1: Windows version of bin/sync (same behaviour).
#   bin\sync              commit local changes (if any), merge GitHub's changes, push
#   bin\sync "message"    same, with your own commit message
#   bin\sync --check      only show what would happen; change nothing
# Never force-pushes; stops on a real conflict (your work stays committed); refuses secret-looking files.
param([string]$Arg = "")
$ErrorActionPreference = "Continue"
function Say($m) { Write-Host "sync: $m" }
function Git { & git @args; return $LASTEXITCODE }

$top = (& git rev-parse --show-toplevel 2>$null)
if (-not $top) { Say "not inside a git repository"; exit 1 }
Set-Location $top
$check = ($Arg -eq "--check"); $msg = if ($check) { "" } else { $Arg }
$branch = (& git rev-parse --abbrev-ref HEAD).Trim()
if ($branch -eq "HEAD") { Say "detached HEAD; check out a branch first"; exit 1 }
$remote = (& git config "branch.$branch.remote"); if (-not $remote) { $remote = "origin" }

$secret = '(^|/)(\.env(\..*)?|.*\.pem|.*\.key|id_rsa.*|id_ed25519.*|credentials(\.json)?|.*secret.*|\.npmrc|\.pypirc)$'
$changed = @(& git status --porcelain --untracked-files=normal)
if ($changed.Count -gt 0) {
  $bad = $changed | ForEach-Object { ($_.Substring(3) -split ' -> ')[-1] } | Where-Object { $_ -match $secret }
  if ($bad) { Say "these files look like secrets, so nothing was committed:"; $bad | ForEach-Object { "  $_" }
              Say "add them to .gitignore (or remove them), then run bin\sync again"; exit 1 }
  if ($check) { Say "would commit:"; $changed | ForEach-Object { "  $_" } }
  else {
    if (-not $msg) { $msg = "sync: $env:COMPUTERNAME $((Get-Date).ToUniversalTime().ToString('yyyy-MM-dd HH:mm')) UTC" }
    & git add -A; & git commit -q -m $msg; if ($LASTEXITCODE -ne 0) { Say "commit failed"; exit 1 }
    Say "committed local changes"
  }
} else { Say "no local changes" }

& git fetch -q $remote $branch; if ($LASTEXITCODE -ne 0) { Say "could not reach $remote (offline?); your work is committed locally"; exit 1 }
$ahead = (& git rev-list --count FETCH_HEAD..HEAD).Trim(); $behind = (& git rev-list --count HEAD..FETCH_HEAD).Trim()
Say "$behind new on GitHub, $ahead local to send"
if ($check) { exit 0 }

if ($behind -ne "0") {
  & git merge -q --no-edit FETCH_HEAD
  if ($LASTEXITCODE -ne 0) {
    $files = @(& git diff --name-only --diff-filter=U); & git merge --abort
    Say "conflict in these files (nothing lost; your commit is still here):"; $files | ForEach-Object { "  $_" }
    Say "fix: open them, or ask a session to merge; then run bin\sync again"; exit 2
  }
  Say "merged GitHub's changes"
}

if ((& git rev-list --count FETCH_HEAD..HEAD).Trim() -ne "0") {
  for ($i = 1; $i -le 3; $i++) {
    & git push -q $remote "HEAD:$branch"; if ($LASTEXITCODE -eq 0) { Say "pushed to $remote/$branch"; exit 0 }
    Say "push rejected (someone pushed meanwhile); merging and retrying ($i/3)"
    & git fetch -q $remote $branch; & git merge -q --no-edit FETCH_HEAD
    if ($LASTEXITCODE -ne 0) { & git merge --abort 2>$null; Say "conflict while retrying; run bin\sync again"; exit 2 }
    Start-Sleep -Seconds ($i * 2)
  }
  Say "could not push after 3 tries; your work is committed locally"; exit 1
}
Say "in sync with $remote/$branch"
