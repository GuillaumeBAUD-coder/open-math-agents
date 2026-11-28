<#
.SYNOPSIS
Install a pinned, SHA-256-verified release of elan on Windows.
#>
[CmdletBinding()]
param(
  [string]$Version = $(if ($env:ELAN_VERSION) { $env:ELAN_VERSION } else { "v4.4.0" }),
  [string]$Target = $(if ($env:ELAN_TARGET) { $env:ELAN_TARGET } else { "x86_64-pc-windows-msvc" }),
  [string]$Sha256 = $(if ($env:ELAN_SHA256) { $env:ELAN_SHA256 } else { "63f50605424284927799702347e2bdbd99d017b9d80ae083c65ee2189c4caf75" }),
  [Parameter(ValueFromRemainingArguments = $true)]
  [string[]]$ExtraArgs
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"
[Net.ServicePointManager]::SecurityProtocol = [Net.ServicePointManager]::SecurityProtocol -bor [Net.SecurityProtocolType]::Tls12

if ($Version -notmatch '^v[0-9]+\.[0-9]+\.[0-9]+$') {
  throw "install-elan: invalid ELAN_VERSION: $Version"
}
if ($Target -notmatch '^[A-Za-z0-9_.-]+$') {
  throw "install-elan: invalid ELAN_TARGET: $Target"
}
$Sha256Lower = $Sha256.ToLowerInvariant()
if ($Sha256Lower -notmatch '^[0-9a-f]{64}$') {
  throw "install-elan: invalid ELAN_SHA256: $Sha256"
}
if ((($Target -ne "x86_64-pc-windows-msvc") -and ($Sha256Lower -eq "63f50605424284927799702347e2bdbd99d017b9d80ae083c65ee2189c4caf75"))) {
  throw "install-elan: must pass matching -Sha256 when overriding -Target"
}

$tmpDir = Join-Path ([System.IO.Path]::GetTempPath()) ("elan-install-" + [System.Guid]::NewGuid().ToString("N"))
New-Item -ItemType Directory -Path $tmpDir -Force | Out-Null

try {
  $archive = Join-Path $tmpDir "elan.zip"
  $url = "https://github.com/leanprover/elan/releases/download/$Version/elan-$Target.zip"
  Invoke-WebRequest -Uri $url -OutFile $archive -UseBasicParsing

  $actual = (Get-FileHash -Path $archive -Algorithm SHA256).Hash.ToLowerInvariant()
  if ($actual -ne $Sha256Lower) {
    throw "install-elan: SHA-256 mismatch for $url (expected $Sha256Lower, got $actual)"
  }

  $extractDir = Join-Path $tmpDir "unpacked"
  Expand-Archive -Path $archive -DestinationPath $extractDir -Force
  $initExe = Join-Path $extractDir "elan-init.exe"
  if (-not (Test-Path $initExe -PathType Leaf)) {
    throw "install-elan: elan-init.exe not found inside archive"
  }

  $initArgs = @("-y", "--no-modify-path", "--default-toolchain", "none")
  if ($ExtraArgs) { $initArgs += $ExtraArgs }
  & $initExe @initArgs
  if ($LASTEXITCODE -ne 0) {
    exit $LASTEXITCODE
  }
}
finally {
  Remove-Item -Path $tmpDir -Recurse -Force -ErrorAction SilentlyContinue
}
