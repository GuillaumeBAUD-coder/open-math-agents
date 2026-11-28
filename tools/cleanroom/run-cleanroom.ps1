<#
.SYNOPSIS
Offline, capability-dropped Docker cleanroom runner for native Windows PowerShell (5.1+ / 7+).
#>
[CmdletBinding()]
param(
  [Parameter(Mandatory = $true, Position = 0)]
  [ValidateSet("build", "check", "lint", "lean", "self-test")]
  [string]$Command,

  [Parameter(Position = 1)]
  [string]$RepoDir = "",

  [Parameter(Position = 2)]
  [string]$TargetArg = "",

  [Parameter(Position = 3)]
  [string]$ExtraArg = ""
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$RepoDefault = (Resolve-Path (Join-Path $ScriptDir "..\..")).Path
$Image = if ($env:OMA_CLEANROOM_IMAGE) { $env:OMA_CLEANROOM_IMAGE } else { "oma-cleanroom:lean" }
$Memory = if ($env:OMA_CLEANROOM_MEMORY) { $env:OMA_CLEANROOM_MEMORY } else { "8g" }
$PidsLimit = if ($env:OMA_CLEANROOM_PIDS) { $env:OMA_CLEANROOM_PIDS } else { "512" }
$Platform = if ($env:OMA_CLEANROOM_PLATFORM) { $env:OMA_CLEANROOM_PLATFORM } else { "" }

function Resolve-ExistingDir([string]$PathArg, [string]$DefaultPath) {
  $candidate = if ([string]::IsNullOrWhiteSpace($PathArg)) { $DefaultPath } else { $PathArg }
  if (-not (Test-Path $candidate -PathType Container)) {
    throw "run-cleanroom: directory does not exist: $candidate"
  }
  return (Resolve-Path $candidate).Path
}

function Assert-RelFile([string]$RelPath) {
  $norm = $RelPath.Replace("\", "/")
  if ($norm.Contains("..")) {
    throw "run-cleanroom: path traversal rejected: $RelPath"
  }
  if ($norm -notmatch "^(proofs|reductions|statements)/[A-Za-z0-9_.'-]+\.lean$") {
    throw "run-cleanroom: invalid relative Lean file path: $RelPath"
  }
  return $norm
}

function Assert-NotSymlink([string]$FullPath, [string]$RelPath) {
  $item = Get-Item -LiteralPath $FullPath -Force
  if ($item.Attributes -band [System.IO.FileAttributes]::ReparsePoint) {
    throw "run-cleanroom: submission file must not be a symlink/reparse point: $RelPath"
  }
}

function Assert-Module([string]$Mod) {
  if ([string]::IsNullOrEmpty($Mod) -or $Mod.StartsWith("-") -or $Mod.Contains("..")) {
    throw "run-cleanroom: invalid Lean module name: $Mod"
  }
  if ($Mod -notmatch '^[A-Za-z0-9_.«»-]+$') {
    throw "run-cleanroom: invalid Lean module name: $Mod"
  }
}

function Assert-Commit([string]$Sha) {
  if ($Sha -notmatch '^[0-9a-f]{40}$') {
    throw "run-cleanroom: invalid commit hash: $Sha"
  }
}

function Assert-Platform([string]$Plat) {
  if ($Plat -notmatch '^[a-z0-9/_-]+$') {
    throw "run-cleanroom: invalid OMA_CLEANROOM_PLATFORM: $Plat"
  }
}

function Assert-Image([string]$Img) {
  if ([string]::IsNullOrEmpty($Img) -or ($Img -notmatch '^[A-Za-z0-9][A-Za-z0-9._/:@-]*$')) {
    throw "run-cleanroom: invalid OMA_CLEANROOM_IMAGE: $Img"
  }
}

function Assert-Memory([string]$Mem) {
  if ($Mem -notmatch '^[0-9]+[bBkKmMgG]?$') {
    throw "run-cleanroom: invalid OMA_CLEANROOM_MEMORY: $Mem"
  }
}

function Assert-PidsLimit([string]$PidsVal) {
  if ($PidsVal -notmatch '^[1-9][0-9]*$') {
    throw "run-cleanroom: invalid OMA_CLEANROOM_PIDS: $PidsVal"
  }
}

Assert-Image $Image
Assert-Memory $Memory
Assert-PidsLimit $PidsLimit

function Get-CommonDockerArgs {
  $argsList = @(
    "--rm",
    "--network=none",
    "--cap-drop=ALL",
    "--security-opt=no-new-privileges:true",
    "--pids-limit=$PidsLimit",
    "--memory=$Memory",
    "--user", "1001:1001",
    "-e", "OMA_FC=/opt/formal-conjectures",
    "-e", "HOME=/home/oma"
  )
  if (-not [string]::IsNullOrEmpty($Platform)) {
    Assert-Platform $Platform
    $argsList += @("--platform", $Platform)
  }
  return $argsList
}

function New-EnvMaskArgs([string]$RootPath, [string]$TempMaskDir) {
  $emptyFile = Join-Path $TempMaskDir "empty"
  $emptyDir = Join-Path $TempMaskDir "empty_dir"
  [System.IO.File]::WriteAllBytes($emptyFile, [byte[]]@())
  New-Item -ItemType Directory -Path $emptyDir -Force | Out-Null
  $maskArgs = @()
  foreach ($ef in (Get-ChildItem -LiteralPath $RootPath -Filter ".env*" -Force -ErrorAction SilentlyContinue)) {
    if (-not $ef.PSIsContainer) {
      $maskArgs += @("-v", "${emptyFile}:/work/$($ef.Name):ro")
    }
  }
  foreach ($sf in @(".npmrc", ".netrc")) {
    $p = Join-Path $RootPath $sf
    if (Test-Path -LiteralPath $p) {
      $item = Get-Item -LiteralPath $p -Force
      if (-not $item.PSIsContainer) {
        $maskArgs += @("-v", "${emptyFile}:/work/${sf}:ro")
      }
    }
  }
  foreach ($sd in @(".git", ".oma")) {
    $p = Join-Path $RootPath $sd
    if (Test-Path -LiteralPath $p) {
      $item = Get-Item -LiteralPath $p -Force
      if (($item.Attributes -band [System.IO.FileAttributes]::ReparsePoint) -or (-not $item.PSIsContainer)) {
        $maskArgs += @("-v", "${emptyFile}:/work/${sd}:ro")
      } else {
        $maskArgs += @("-v", "${emptyDir}:/work/${sd}:ro")
      }
    }
  }
  return $maskArgs
}

$maskTempDir = Join-Path ([System.IO.Path]::GetTempPath()) ("oma-cleanroom-mask-" + [System.Guid]::NewGuid().ToString("N"))
New-Item -ItemType Directory -Path $maskTempDir -Force | Out-Null

try {
  switch ($Command) {
    "build" {
      $repo = Resolve-ExistingDir $RepoDir $RepoDefault
      $catalogPath = Join-Path $repo "data\catalog.json"
      if (-not (Test-Path $catalogPath -PathType Leaf)) {
        throw "run-cleanroom: catalog not found: $catalogPath"
      }
      $fcCommit = (Get-Content -LiteralPath $catalogPath -Raw | ConvertFrom-Json).meta.upstreamCommit
      Assert-Commit $fcCommit
      $buildArgs = @("build", "--build-arg", "FC_COMMIT=$fcCommit", "-t", $Image)
      if (-not [string]::IsNullOrEmpty($Platform)) {
        Assert-Platform $Platform
        $buildArgs += @("--platform", $Platform)
      }
      $buildArgs += $ScriptDir
      & docker @buildArgs
      exit $LASTEXITCODE
    }

    "check" {
      if ([string]::IsNullOrEmpty($RepoDir) -or [string]::IsNullOrEmpty($TargetArg)) {
        throw "Usage: run-cleanroom.ps1 check <repo_dir> <rel_file_path> [out_verdict_json]"
      }
      $repo = Resolve-ExistingDir $RepoDir $RepoDefault
      $rel = Assert-RelFile $TargetArg
      $full = Join-Path $repo ($rel.Replace("/", "\"))
      if (-not (Test-Path $full -PathType Leaf)) {
        throw "run-cleanroom: file not found: $full"
      }
      Assert-NotSymlink (Split-Path -Parent $full) (Split-Path -Parent $rel)
      Assert-NotSymlink $full $rel

      $dockerArgs = @("run") + (Get-CommonDockerArgs) + @("-v", "${repo}:/work:ro") + (New-EnvMaskArgs $repo $maskTempDir) + @(
        "-w", "/work",
        $Image,
        "bash", "-lc", 'tools/check.sh "$1" /tmp/verdict.json; RC=$?; cat /tmp/verdict.json 2>/dev/null || true; exit $RC', "_", $rel
      )
      if (-not [string]::IsNullOrEmpty($ExtraArg)) {
        $outDir = Split-Path -Parent $ExtraArg
        if ($outDir -and -not (Test-Path $outDir)) {
          New-Item -ItemType Directory -Path $outDir -Force | Out-Null
        }
        $output = & docker @dockerArgs
        $rc = $LASTEXITCODE
        $utf8NoBom = New-Object System.Text.UTF8Encoding($false)
        [System.IO.File]::WriteAllText($ExtraArg, ($output -join "`n") + "`n", $utf8NoBom)
        exit $rc
      }
      & docker @dockerArgs
      exit $LASTEXITCODE
    }

    "lint" {
      if ([string]::IsNullOrEmpty($RepoDir) -or [string]::IsNullOrEmpty($TargetArg)) {
        throw "Usage: run-cleanroom.ps1 lint <repo_dir> <rel_file_path>"
      }
      $repo = Resolve-ExistingDir $RepoDir $RepoDefault
      $rel = Assert-RelFile $TargetArg
      $full = Join-Path $repo ($rel.Replace("/", "\"))
      if (-not (Test-Path $full -PathType Leaf)) {
        throw "run-cleanroom: file not found: $full"
      }
      Assert-NotSymlink (Split-Path -Parent $full) (Split-Path -Parent $rel)
      Assert-NotSymlink $full $rel

      $dockerArgs = @("run") + (Get-CommonDockerArgs) + @("-v", "${repo}:/work:ro") + (New-EnvMaskArgs $repo $maskTempDir) + @(
        "-w", "/work",
        $Image,
        "python3", "-I", "tools/lint.py", $rel, "data/catalog.json"
      )
      & docker @dockerArgs
      exit $LASTEXITCODE
    }

    "lean" {
      if ([string]::IsNullOrEmpty($RepoDir) -or [string]::IsNullOrEmpty($TargetArg)) {
        throw "Usage: run-cleanroom.ps1 lean <repo_dir> <lean_file> [module_to_build]"
      }
      $repo = Resolve-ExistingDir $RepoDir $RepoDefault
      if (-not (Test-Path $TargetArg -PathType Leaf)) {
        throw "run-cleanroom: scratch file not found: $TargetArg"
      }
      Assert-NotSymlink $TargetArg $TargetArg
      $scratchAbs = (Resolve-Path $TargetArg).Path
      if (-not [string]::IsNullOrEmpty($ExtraArg)) {
        Assert-Module $ExtraArg
      }
      $extraMounts = @()
      if ($env:OMA_BUILD_CACHE_DIR) {
        $cacheAbs = Resolve-ExistingDir $env:OMA_BUILD_CACHE_DIR $env:OMA_BUILD_CACHE_DIR
        $extraMounts += @("-v", "${cacheAbs}:/opt/formal-conjectures/.lake/build:rw")
      }
      $dockerArgs = @("run") + (Get-CommonDockerArgs) + @("-v", "${repo}:/work:ro") + (New-EnvMaskArgs $repo $maskTempDir) + @(
        "-v", "${scratchAbs}:/tmp/scratch.lean:ro"
      ) + $extraMounts + @(
        "-w", "/opt/formal-conjectures",
        $Image,
        "bash", "-lc", 'if [ -n "${1:-}" ]; then lake build "$1"; fi && lake env lean /tmp/scratch.lean', "_", $ExtraArg
      )
      & docker @dockerArgs
      exit $LASTEXITCODE
    }

    "self-test" {
      $repo = Resolve-ExistingDir $RepoDir $RepoDefault
      $sample = $TargetArg
      if ([string]::IsNullOrEmpty($sample)) {
        $defaultSample = Join-Path $repo "proofs\OeisA158110.a_0.lean"
        if (Test-Path $defaultSample -PathType Leaf) {
          $sample = "proofs/OeisA158110.a_0.lean"
        } else {
          $first = Get-ChildItem -LiteralPath (Join-Path $repo "proofs") -Filter "*.lean" -File | Select-Object -First 1
          if (-not $first) { throw "run-cleanroom: no sample proof found under $repo\proofs" }
          $sample = "proofs/$($first.Name)"
        }
      }
      $sample = Assert-RelFile $sample

      Write-Host "1/3 Negative traversal test (expect fail-closed rejection before Docker)..."
      foreach ($bad in @("../etc/passwd", "..\etc\passwd")) {
        $rejected = $false
        try {
          $null = Assert-RelFile $bad
        } catch {
          $rejected = $true
        }
        if (-not $rejected) {
          throw "self-test failed: traversal path was not rejected: $bad"
        }
      }
      Write-Host "    OK: path traversal rejected"

      Write-Host "2/3 Negative secret/state masking test (expect /work/.env*, .git, and .oma empty inside container)..."
      $tmpEnvTest = Join-Path $maskTempDir "envtest"
      New-Item -ItemType Directory -Path (Join-Path $tmpEnvTest "proofs") -Force | Out-Null
      New-Item -ItemType Directory -Path (Join-Path $tmpEnvTest ".git") -Force | Out-Null
      New-Item -ItemType Directory -Path (Join-Path $tmpEnvTest ".oma\leases") -Force | Out-Null
      Set-Content -Path (Join-Path $tmpEnvTest ".env") -Value "SECRET_TOKEN=should_never_be_visible" -NoNewline
      Set-Content -Path (Join-Path $tmpEnvTest ".env.local") -Value "OTHER_TOKEN=should_never_be_visible" -NoNewline
      Set-Content -Path (Join-Path $tmpEnvTest ".git\config") -Value "SECRET_GIT=should_never_be_visible" -NoNewline
      Set-Content -Path (Join-Path $tmpEnvTest ".oma\leases\demo") -Value "SECRET_LEASE=should_never_be_visible" -NoNewline
      $dockerMaskArgs = @("run") + (Get-CommonDockerArgs) + @("-v", "${tmpEnvTest}:/work:ro") + (New-EnvMaskArgs $tmpEnvTest $maskTempDir) + @(
        "-w", "/work",
        $Image,
        "bash", "-c", "test ! -s /work/.env && test ! -s /work/.env.local && test ! -e /work/.git/config && test ! -e /work/.oma/leases/demo"
      )
      & docker @dockerMaskArgs
      if ($LASTEXITCODE -ne 0) {
        throw "self-test failed: .env*/.git/.oma masking failed inside container"
      }
      Write-Host "    OK: .env*, .git, and .oma masked inside container"

      Write-Host "3/3 Positive cleanroom check ($sample)..."
      $verdictJson = & $MyInvocation.MyCommand.Path "check" $repo $sample
      $rc = $LASTEXITCODE
      Write-Host $verdictJson
      if ($rc -ne 0) { exit $rc }
      $parsed = ($verdictJson -join "`n") | ConvertFrom-Json
      if ($parsed.verdict -ne "accepted") {
        throw "self-test failed: expected accepted verdict, got $($parsed.verdict)"
      }
      Write-Host "    OK: cleanroom self-test passed"
    }
  }
}
finally {
  Remove-Item -Path $maskTempDir -Recurse -Force -ErrorAction SilentlyContinue
}
