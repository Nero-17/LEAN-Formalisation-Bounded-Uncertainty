param(
    [string]$LeanExe = 'C:\Users\lzysh\Documents\Codex\bounded-noise-asymptotic-periodicity\.local-tools\elan-home\toolchains\leanprover--lean4---v4.28.0\bin\lean.exe',
    [string]$DependencyRoot = 'C:\Users\lzysh\Documents\Codex\bounded-noise-asymptotic-periodicity\.lake\packages',
    [string[]]$Modules,
    [switch]$Audit
)

$ErrorActionPreference = 'Stop'
$taskProjectRoot = Split-Path -Parent $PSScriptRoot
if (-not $PSBoundParameters.ContainsKey('Modules')) {
    $Modules = @(Get-Content -LiteralPath (Join-Path $taskProjectRoot 'BoundedUncertainty.lean') |
        Where-Object { $_ -match '^import BoundedUncertainty\.([A-Za-z][A-Za-z0-9_]*)$' } |
        ForEach-Object { $_.Substring('import BoundedUncertainty.'.Length) })
    if ($Modules.Count -eq 0) { throw 'The project entry point contains no modules.' }
}
$taskBuildRoot = Join-Path $taskProjectRoot '.lake\build\lib\lean'
$taskModuleBuild = Join-Path $taskBuildRoot 'BoundedUncertainty'
New-Item -ItemType Directory -Force -Path $taskModuleBuild | Out-Null
$taskDependencyPaths = Get-ChildItem -LiteralPath $DependencyRoot -Directory |
    ForEach-Object { Join-Path $_.FullName '.lake\build\lib\lean' } |
    Where-Object { Test-Path -LiteralPath $_ }
$taskPreviousLeanPath = $env:LEAN_PATH
$env:LEAN_PATH = (@($taskBuildRoot) + @($taskDependencyPaths)) -join ';'
Push-Location $taskProjectRoot
try {
    & $LeanExe --version
    if ($LASTEXITCODE -ne 0) { throw 'Lean toolchain check failed.' }
    foreach ($taskModule in $Modules) {
        if ($taskModule -notmatch '^[A-Za-z][A-Za-z0-9_]*$') {
            throw "Invalid module name: $taskModule"
        }
        Write-Output "Checking BoundedUncertainty.$taskModule"
        & $LeanExe "-o" (Join-Path $taskModuleBuild ($taskModule + '.olean')) (Join-Path 'BoundedUncertainty' ($taskModule + '.lean'))
        if ($LASTEXITCODE -ne 0) { throw "Lean rejected $taskModule." }
    }
    if ($Audit) {
        & $LeanExe "-o" (Join-Path $taskBuildRoot 'BoundedUncertainty.olean') 'BoundedUncertainty.lean'
        if ($LASTEXITCODE -ne 0) { throw 'Lean rejected the project entry point.' }
        $taskAuditResult = & $LeanExe 'AxiomAudit.lean' 2>&1
        $taskAuditExitCode = $LASTEXITCODE
        $taskAuditResult | ForEach-Object { Write-Output $_ }
        $taskAuditResult | Set-Content -LiteralPath (Join-Path $taskProjectRoot '.lake\build\axiom-audit.txt') -Encoding utf8
        if ($taskAuditExitCode -ne 0) { throw 'Axiom audit did not compile.' }
        if (($taskAuditResult -join [Environment]::NewLine) -match 'sorryAx') { throw 'Unproved dependency found.' }
        $taskAllowedAxioms = @('propext', 'Classical.choice', 'Quot.sound')
        $taskAxiomMatches = [regex]::Matches(($taskAuditResult -join [Environment]::NewLine), 'depends on axioms:\s*\[([^\]]*)\]')
        foreach ($taskAxiomMatch in $taskAxiomMatches) {
            foreach ($taskAxiom in ($taskAxiomMatch.Groups[1].Value -split ',')) {
                $taskAxiomName = $taskAxiom.Trim()
                if ($taskAxiomName -and $taskAxiomName -notin $taskAllowedAxioms) {
                    throw "Unexpected axiom: $taskAxiomName"
                }
            }
        }
        Write-Output 'Axiom audit passed: only propext, Classical.choice and Quot.sound were used.'
    }
}
finally {
    Pop-Location
    $env:LEAN_PATH = $taskPreviousLeanPath
}
