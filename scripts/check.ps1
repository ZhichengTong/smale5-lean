param([string]$Python="python", [string]$Lake="lake")
$ErrorActionPreference="Stop"
& $Python (Join-Path $PSScriptRoot "check.py") --lake $Lake
if ($LASTEXITCODE -ne 0) { throw "Lean verification failed: $LASTEXITCODE" }
