#!/usr/bin/env bash
# Install a pinned, SHA-256-verified release of elan on Linux or macOS (never curl | sh from a moving branch).
set -euo pipefail

ELAN_VERSION="${ELAN_VERSION:-v4.4.0}"
ELAN_SHA256_LINUX_X86_64="0e8250aa2be86c7af929ade68db617af9edc8b9ccf6eaf5ece228250d0d032e2"
ELAN_SHA256_LINUX_ARM64="45cde3006f82f98804c94cf2ca4949d117060a5f3cc8afa62f523759947ee21f"
ELAN_SHA256_DARWIN_X86_64="a5123096d662216ceaf69d68d6bbabb118c024d20d270bf0d639a830dd4ff97e"
ELAN_SHA256_DARWIN_ARM64="27af24edeace839730e8c9119783f12d5f694327d4771605021ca09db1ab0a87"

if [ -n "${ELAN_TARGET:-}" ] || [ -n "${ELAN_SHA256:-}" ]; then
  [ -n "${ELAN_TARGET:-}" ] && [ -n "${ELAN_SHA256:-}" ] || {
    echo "install-elan: both ELAN_TARGET and ELAN_SHA256 must be set when overriding defaults" >&2
    exit 2
  }
  TARGET="$ELAN_TARGET"
  SHA="$ELAN_SHA256"
else
  OS="$(uname -s)"
  ARCH="$(uname -m)"
  case "$OS:$ARCH" in
    Linux:x86_64|Linux:amd64)
      TARGET="x86_64-unknown-linux-gnu"
      SHA="$ELAN_SHA256_LINUX_X86_64"
      ;;
    Linux:aarch64|Linux:arm64)
      TARGET="aarch64-unknown-linux-gnu"
      SHA="$ELAN_SHA256_LINUX_ARM64"
      ;;
    Darwin:x86_64)
      TARGET="x86_64-apple-darwin"
      SHA="$ELAN_SHA256_DARWIN_X86_64"
      ;;
    Darwin:arm64|Darwin:aarch64)
      TARGET="aarch64-apple-darwin"
      SHA="$ELAN_SHA256_DARWIN_ARM64"
      ;;
    *)
      echo "install-elan: unsupported OS/arch '$OS:$ARCH' (set ELAN_TARGET and ELAN_SHA256 explicitly)" >&2
      exit 2
      ;;
  esac
fi

if [[ ! "$ELAN_VERSION" =~ ^v[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
  echo "install-elan: invalid ELAN_VERSION: $ELAN_VERSION" >&2
  exit 2
fi
if [[ ! "$TARGET" =~ ^[A-Za-z0-9_.-]+$ ]]; then
  echo "install-elan: invalid ELAN_TARGET: $TARGET" >&2
  exit 2
fi
if [[ ! "$SHA" =~ ^[0-9a-f]{64}$ ]]; then
  echo "install-elan: invalid ELAN_SHA256: $SHA" >&2
  exit 2
fi

verify_sha256() {
  local expected="$1"
  local file="$2"
  if command -v sha256sum >/dev/null 2>&1; then
    printf '%s  %s\n' "$expected" "$file" | sha256sum -c -
  elif command -v shasum >/dev/null 2>&1; then
    printf '%s  %s\n' "$expected" "$file" | shasum -a 256 -c -
  else
    echo "install-elan: neither sha256sum nor shasum is installed" >&2
    return 2
  fi
}

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

URL="https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/elan-${TARGET}.tar.gz"
ARCHIVE="$TMP/elan.tar.gz"

curl -fsSL --retry 3 "$URL" -o "$ARCHIVE"
verify_sha256 "$SHA" "$ARCHIVE"
tar -xzf "$ARCHIVE" -C "$TMP"
"$TMP/elan-init" -y --no-modify-path --default-toolchain none "$@"
