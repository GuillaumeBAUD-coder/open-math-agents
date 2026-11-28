#!/usr/bin/env bash
# Offline, capability-dropped Docker cleanroom runner for Linux, macOS, and Windows (WSL2 / Git Bash).
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd -P)"
REPO_DEFAULT="$(cd "$SCRIPT_DIR/../.." && pwd -P)"
IMAGE="${OMA_CLEANROOM_IMAGE:-oma-cleanroom:lean}"
MEMORY="${OMA_CLEANROOM_MEMORY:-8g}"
PIDS_LIMIT="${OMA_CLEANROOM_PIDS:-512}"
PLATFORM="${OMA_CLEANROOM_PLATFORM:-}"

# Prevent Git Bash / MSYS2 on Windows from rewriting Linux container paths such as /work or /tmp/scratch.lean.
export MSYS_NO_PATHCONV=1
export MSYS2_ARG_CONV_EXCL="*"

MASK_DIR=""
cleanup() {
  if [ -n "$MASK_DIR" ] && [ -d "$MASK_DIR" ]; then
    rm -rf "$MASK_DIR"
  fi
}
trap cleanup EXIT

die() { echo "run-cleanroom: $*" >&2; exit 1; }

usage() {
  cat >&2 <<'USAGE'
Usage:
  run-cleanroom.sh build     [repo_dir]
  run-cleanroom.sh check     <repo_or_worktree_dir> <rel_file_path> [out_verdict_json]
  run-cleanroom.sh lint      <repo_or_worktree_dir> <rel_file_path>
  run-cleanroom.sh lean      <repo_or_worktree_dir> <lean_file> [module_to_build]
  run-cleanroom.sh self-test [repo_or_worktree_dir] [sample_proof_rel_path]
USAGE
  exit 2
}

validate_dir() {
  local d="$1"
  [ -d "$d" ] || die "directory does not exist: $d"
  (cd "$d" && pwd -P)
}

validate_rel_file() {
  local f="$1"
  [[ "$f" != *".."* ]] || die "path traversal rejected: $f"
  if [[ ! "$f" =~ ^(proofs|reductions|statements)/[A-Za-z0-9_.\'-]+\.lean$ ]]; then
    die "invalid relative Lean file path: $f"
  fi
}

validate_module() {
  local m="$1"
  [[ -n "$m" ]] || die "empty module name"
  [[ "$m" != -* ]] || die "invalid module name: $m"
  [[ "$m" != *".."* ]] || die "invalid module name: $m"
  if [[ ! "$m" =~ ^[A-Za-z0-9_.«»-]+$ ]]; then
    die "invalid Lean module name: $m"
  fi
}

validate_commit() {
  local c="$1"
  if [[ ! "$c" =~ ^[0-9a-f]{40}$ ]]; then
    die "invalid commit hash: $c"
  fi
}

validate_platform() {
  local p="$1"
  if [[ ! "$p" =~ ^[a-z0-9/_-]+$ ]]; then
    die "invalid OMA_CLEANROOM_PLATFORM: $p"
  fi
}

validate_image() {
  local img="$1"
  [[ -n "$img" ]] || die "empty OMA_CLEANROOM_IMAGE"
  if [[ ! "$img" =~ ^[A-Za-z0-9][A-Za-z0-9._/:@-]*$ ]]; then
    die "invalid OMA_CLEANROOM_IMAGE: $img"
  fi
}

validate_memory() {
  local mem="$1"
  if [[ ! "$mem" =~ ^[0-9]+[bBkKmMgG]?$ ]]; then
    die "invalid OMA_CLEANROOM_MEMORY: $mem"
  fi
}

validate_pids() {
  local pids="$1"
  if [[ ! "$pids" =~ ^[1-9][0-9]*$ ]]; then
    die "invalid OMA_CLEANROOM_PIDS: $pids"
  fi
}

validate_image "$IMAGE"
validate_memory "$MEMORY"
validate_pids "$PIDS_LIMIT"

to_docker_path() {
  local p="$1"
  case "$(uname -s)" in
    MINGW*|MSYS*|CYGWIN*)
      command -v cygpath >/dev/null 2>&1 || die "cygpath required on MSYS/Git Bash"
      cygpath -w "$p"
      ;;
    *)
      printf '%s' "$p"
      ;;
  esac
}

# Overlay sensitive host files/dirs (.env*, .npmrc, .netrc, .git, .oma) read-only inside /work.
build_env_masks() {
  local repo_dir="$1"
  env_mask_args=()
  MASK_DIR="$(mktemp -d)"
  local empty_file="$MASK_DIR/empty"
  local empty_dir="$MASK_DIR/empty_dir"
  : > "$empty_file"
  mkdir -p "$empty_dir"
  local empty_mount empty_dir_mount
  empty_mount="$(to_docker_path "$empty_file")"
  empty_dir_mount="$(to_docker_path "$empty_dir")"
  shopt -s nullglob
  for ef in "$repo_dir"/.env* "$repo_dir/.npmrc" "$repo_dir/.netrc"; do
    if [ -L "$ef" ] || [ -f "$ef" ]; then
      env_mask_args+=(-v "$empty_mount:/work/$(basename "$ef"):ro")
    fi
  done
  for sd in "$repo_dir/.git" "$repo_dir/.oma"; do
    if [ -L "$sd" ] || [ -f "$sd" ]; then
      env_mask_args+=(-v "$empty_mount:/work/$(basename "$sd"):ro")
    elif [ -d "$sd" ]; then
      env_mask_args+=(-v "$empty_dir_mount:/work/$(basename "$sd"):ro")
    fi
  done
  shopt -u nullglob
}

common_docker_args=(
  --rm
  --network=none
  --cap-drop=ALL
  --security-opt=no-new-privileges:true
  --pids-limit="$PIDS_LIMIT"
  --memory="$MEMORY"
  --user 1001:1001
  -e OMA_FC=/opt/formal-conjectures
  -e HOME=/home/oma
)

if [ -n "$PLATFORM" ]; then
  validate_platform "$PLATFORM"
  common_docker_args+=(--platform "$PLATFORM")
fi

cmd="${1:-}"; shift || true
case "$cmd" in
  build)
    [ $# -le 1 ] || usage
    REPO_DIR="$(validate_dir "${1:-$REPO_DEFAULT}")"
    CATALOG="$REPO_DIR/data/catalog.json"
    [ -f "$CATALOG" ] || die "catalog not found: $CATALOG"
    FC_COMMIT="$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["meta"]["upstreamCommit"])' "$CATALOG")"
    validate_commit "$FC_COMMIT"
    build_args=(--build-arg "FC_COMMIT=$FC_COMMIT" -t "$IMAGE")
    if [ -n "$PLATFORM" ]; then
      build_args+=(--platform "$PLATFORM")
    fi
    docker build "${build_args[@]}" "$(to_docker_path "$SCRIPT_DIR")"
    ;;
  check)
    [ $# -ge 2 ] && [ $# -le 3 ] || usage
    REPO_DIR="$(validate_dir "$1")"
    REL_FILE="$2"
    OUT_FILE="${3:-}"
    validate_rel_file "$REL_FILE"
    [ -f "$REPO_DIR/$REL_FILE" ] || die "file not found: $REPO_DIR/$REL_FILE"
    [ ! -L "$REPO_DIR/$(dirname "$REL_FILE")" ] || die "parent directory must not be a symlink: $(dirname "$REL_FILE")"
    [ ! -L "$REPO_DIR/$REL_FILE" ] || die "submission file must not be a symlink: $REL_FILE"
    build_env_masks "$REPO_DIR"
    REPO_MOUNT="$(to_docker_path "$REPO_DIR")"
    if [ -n "$OUT_FILE" ]; then
      mkdir -p "$(dirname "$OUT_FILE")"
      set +e
      docker run "${common_docker_args[@]}" \
        -v "$REPO_MOUNT:/work:ro" \
        ${env_mask_args[@]+"${env_mask_args[@]}"} \
        -w /work \
        "$IMAGE" \
        bash -lc 'tools/check.sh "$1" /tmp/verdict.json; RC=$?; cat /tmp/verdict.json 2>/dev/null || true; exit $RC' _ "$REL_FILE" > "$OUT_FILE"
      RC=$?
      set -e
      exit "$RC"
    fi
    docker run "${common_docker_args[@]}" \
      -v "$REPO_MOUNT:/work:ro" \
      ${env_mask_args[@]+"${env_mask_args[@]}"} \
      -w /work \
      "$IMAGE" \
      bash -lc 'tools/check.sh "$1" /tmp/verdict.json; RC=$?; cat /tmp/verdict.json 2>/dev/null || true; exit $RC' _ "$REL_FILE"
    ;;
  lint)
    [ $# -eq 2 ] || usage
    REPO_DIR="$(validate_dir "$1")"
    REL_FILE="$2"
    validate_rel_file "$REL_FILE"
    [ -f "$REPO_DIR/$REL_FILE" ] || die "file not found: $REPO_DIR/$REL_FILE"
    [ ! -L "$REPO_DIR/$(dirname "$REL_FILE")" ] || die "parent directory must not be a symlink: $(dirname "$REL_FILE")"
    [ ! -L "$REPO_DIR/$REL_FILE" ] || die "submission file must not be a symlink: $REL_FILE"
    build_env_masks "$REPO_DIR"
    REPO_MOUNT="$(to_docker_path "$REPO_DIR")"
    docker run "${common_docker_args[@]}" \
      -v "$REPO_MOUNT:/work:ro" \
      ${env_mask_args[@]+"${env_mask_args[@]}"} \
      -w /work \
      "$IMAGE" \
      python3 -I tools/lint.py "$REL_FILE" data/catalog.json
    ;;
  lean)
    [ $# -ge 2 ] && [ $# -le 3 ] || usage
    REPO_DIR="$(validate_dir "$1")"
    SCRATCH_FILE="$2"
    [ -f "$SCRATCH_FILE" ] || die "scratch file not found: $SCRATCH_FILE"
    [ ! -L "$SCRATCH_FILE" ] || die "scratch file must not be a symlink: $SCRATCH_FILE"
    SCRATCH_ABS="$(cd "$(dirname "$SCRATCH_FILE")" && pwd -P)/$(basename "$SCRATCH_FILE")"
    MOD="${3:-}"
    if [ -n "$MOD" ]; then
      validate_module "$MOD"
    fi
    build_env_masks "$REPO_DIR"
    REPO_MOUNT="$(to_docker_path "$REPO_DIR")"
    SCRATCH_MOUNT="$(to_docker_path "$SCRATCH_ABS")"
    extra_args=()
    if [ -n "${OMA_BUILD_CACHE_DIR:-}" ]; then
      CACHE_DIR="$(validate_dir "$OMA_BUILD_CACHE_DIR")"
      extra_args+=(-v "$(to_docker_path "$CACHE_DIR"):/opt/formal-conjectures/.lake/build:rw")
    fi
    docker run "${common_docker_args[@]}" \
      -v "$REPO_MOUNT:/work:ro" \
      ${env_mask_args[@]+"${env_mask_args[@]}"} \
      -v "$SCRATCH_MOUNT:/tmp/scratch.lean:ro" \
      ${extra_args[@]+"${extra_args[@]}"} \
      -w /opt/formal-conjectures \
      "$IMAGE" \
      bash -lc 'if [ -n "${1:-}" ]; then lake build "$1"; fi && lake env lean /tmp/scratch.lean' _ "$MOD"
    ;;
  self-test)
    [ $# -le 2 ] || usage
    REPO_DIR="$(validate_dir "${1:-$REPO_DEFAULT}")"
    SAMPLE_FILE="${2:-}"
    if [ -z "$SAMPLE_FILE" ]; then
      if [ -f "$REPO_DIR/proofs/OeisA158110.a_0.lean" ]; then
        SAMPLE_FILE="proofs/OeisA158110.a_0.lean"
      else
        first_proof="$(find "$REPO_DIR/proofs" -maxdepth 1 -name '*.lean' -print -quit 2>/dev/null || true)"
        [ -n "$first_proof" ] || die "no sample proof found under $REPO_DIR/proofs"
        SAMPLE_FILE="proofs/$(basename "$first_proof")"
      fi
    fi
    validate_rel_file "$SAMPLE_FILE"

    echo "1/3 Negative traversal test (expect fail-closed rejection before Docker)..."
    if "$0" check "$REPO_DIR" "../etc/passwd" >/dev/null 2>&1; then
      die "self-test failed: path traversal was not rejected"
    fi
    echo "    OK: path traversal rejected"

    echo "2/3 Negative secret/state masking test (expect /work/.env*, .git, and .oma empty inside container)..."
    TMP_TEST_DIR="$(mktemp -d)"
    trap 'rm -rf "$TMP_TEST_DIR"; cleanup' EXIT
    mkdir -p "$TMP_TEST_DIR/proofs" "$TMP_TEST_DIR/.git" "$TMP_TEST_DIR/.oma/leases"
    printf 'SECRET_TOKEN=should_never_be_visible\n' > "$TMP_TEST_DIR/.env"
    printf 'OTHER_TOKEN=should_never_be_visible\n' > "$TMP_TEST_DIR/.env.local"
    printf 'SECRET_GIT=should_never_be_visible\n' > "$TMP_TEST_DIR/.git/config"
    printf 'SECRET_LEASE=should_never_be_visible\n' > "$TMP_TEST_DIR/.oma/leases/demo"
    build_env_masks "$TMP_TEST_DIR"
    TEST_MOUNT="$(to_docker_path "$TMP_TEST_DIR")"
    docker run "${common_docker_args[@]}" \
      -v "$TEST_MOUNT:/work:ro" \
      ${env_mask_args[@]+"${env_mask_args[@]}"} \
      -w /work \
      "$IMAGE" \
      bash -c 'test ! -s /work/.env && test ! -s /work/.env.local && test ! -e /work/.git/config && test ! -e /work/.oma/leases/demo'
    echo "    OK: .env*, .git, and .oma masked inside container"

    echo "3/3 Positive cleanroom check ($SAMPLE_FILE)..."
    OUT="$("$0" check "$REPO_DIR" "$SAMPLE_FILE")"
    printf '%s\n' "$OUT"
    python3 -I -c 'import json,sys; d=json.loads(sys.argv[1]); sys.exit(0 if d.get("verdict")=="accepted" else 1)' "$OUT"
    echo "    OK: cleanroom self-test passed"
    ;;
  *)
    usage
    ;;
esac
