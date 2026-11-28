#!/usr/bin/env bash
# Adversarial security regression tests for tools/oma.sh, tools/check.sh, tools/fleet.sh,
# tools/cleanroom/run-cleanroom.sh, tools/install-elan.sh, and .github/workflows/*.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
T="$(mktemp -d)"
PORT=$((20000 + RANDOM % 20000))
export MOCK_LOG="$T/requests.log"; : > "$MOCK_LOG"

cat > "$T/malicious_desk.py" <<'PY'
import http.server, json, os, sys, urllib.parse

MODE_FILE = sys.argv[2]

class H(http.server.BaseHTTPRequestHandler):
    def log_message(self, *a): pass
    def do_GET(self):
        p = urllib.parse.urlparse(self.path)
        if p.path == "/api/stats":
            self._json(200, {"liveAgents": 1, "solved": []}); return
        if p.path == "/api/desk/next":
            mode = open(MODE_FILE).read().strip() if os.path.exists(MODE_FILE) else "bad_id"
            if mode == "bad_id":
                self._json(200, {
                    "problem": {"id": "../../../pwn", "title": "x", "kind": "known", "page": "x", "statement": "x", "lean": "x"},
                    "file": "proofs/Ok.lean", "lease": "lease-1", "othersWorking": 0, "lastNote": 1
                })
            elif mode == "bad_file_hook":
                self._json(200, {
                    "problem": {"id": "OkId", "title": "x", "kind": "known", "page": "x", "statement": "x", "lean": "x"},
                    "file": ".git/hooks/post-checkout", "lease": "lease-1", "othersWorking": 0, "lastNote": 1
                })
            elif mode == "bad_file_dotdot":
                self._json(200, {
                    "problem": {"id": "OkId", "title": "x", "kind": "known", "page": "x", "statement": "x", "lean": "x"},
                    "file": "proofs/../../escape.lean", "lease": "lease-1", "othersWorking": 0, "lastNote": 1
                })
            elif mode == "bad_lease":
                self._json(200, {
                    "problem": {"id": "OkId", "title": "x", "kind": "known", "page": "x", "statement": "x", "lean": "x"},
                    "file": "proofs/OkId.lean", "lease": "abc&reason=hacked", "othersWorking": 0, "lastNote": 1
                })
            elif mode == "good":
                self._json(200, {
                    "problem": {"id": "OkId", "title": "x", "kind": "known", "page": "x", "statement": "x", "lean": "x"},
                    "file": "proofs/OkId.lean", "lease": "lease-123", "othersWorking": 0, "lastNote": 1,
                    "skeleton": "-- ok\n"
                })
            return
        if p.path.startswith("/p/"):
            self.send_response(200); self.end_headers(); self.wfile.write(b"brief\n"); return
        self._json(404, {"error": "not_found"})

    def do_POST(self):
        with open(os.environ["MOCK_LOG"], "a") as f:
            f.write(self.path + "\n")
        self._json(200, {"ok": True, "role": "lead", "team": [], "notes": [], "last_note": 2})

    def _json(self, code, obj):
        b = json.dumps(obj).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(b)))
        self.end_headers()
        self.wfile.write(b)

http.server.ThreadingHTTPServer(("127.0.0.1", int(sys.argv[1])), H).serve_forever()
PY

MODE_FILE="$T/mode"
python3 -I "$T/malicious_desk.py" "$PORT" "$MODE_FILE" & MOCK=$!
trap 'kill $MOCK 2>/dev/null || true; rm -rf "$T"' EXIT

FAILS=0
pass() { echo "PASS $1"; }
fail() { echo "FAIL $1"; FAILS=$((FAILS+1)); }
check() { if eval "$2"; then pass "$1"; else fail "$1"; fi; }

# Prepare bare origin and repo whose directory path contains single and double quotes
REPO="$T/repo'with\"quotes"
git init -q --bare "$T/origin.git"
git clone -q "$T/origin.git" "$REPO" 2>/dev/null
cp -r "$ROOT/tools" "$ROOT/data" "$REPO/"
mkdir -p "$REPO/proofs"
cp "$ROOT/proofs/OeisA158110.a_0.lean" "$REPO/proofs/OeisA158110.a_0.lean"
printf 'theorem test : True := trivial\n' > "$REPO/proofs/OkId.lean"
cd "$REPO" && git add -A && git -c user.name=t -c user.email=t@t commit -qm init && git push -q origin HEAD:main 2>/dev/null
git remote set-head origin main 2>/dev/null || git symbolic-ref refs/remotes/origin/HEAD refs/remotes/origin/main

mkdir -p "$T/bin"
cat > "$T/bin/gh" <<'EOF'
#!/usr/bin/env bash
if [ "$1" = "api" ] && [ "$2" = "user" ]; then echo tester; exit 0; fi
exit 1
EOF
cat > "$T/bin/stubcheck" <<'EOF'
#!/usr/bin/env bash
echo '{"verdict":"accepted","reason":"stub ok","log":""}' > "$2"
EOF
cat > "$T/bin/docker" <<'EOF'
#!/usr/bin/env bash
printf '%s\n' "$@" > "$DOCKER_LOG"
# Verify stdout verdict propagation for check subcommand
printf '{"verdict":"accepted","reason":"mock docker ok","log":""}\n'
EOF
cat > "$T/bin/tmux" <<'EOF'
#!/usr/bin/env bash
case "${1:-}" in
  has-session) exit 1 ;;
  new-session|kill-window) exit 0 ;;
  new-window) printf '%s\n' "${@: -1}" > "${TMUX_WIN_CMD:-/dev/null}"; exit 0 ;;
  *) echo "tmux unexpected call: $*" >&2; exit 99 ;;
esac
EOF
chmod +x "$T/bin/gh" "$T/bin/stubcheck" "$T/bin/docker" "$T/bin/tmux"

export PATH="$T/bin:$PATH"
export OMA_SITE="http://127.0.0.1:$PORT"
export DOCKER_LOG="$T/docker.log"
export TMUX_WIN_CMD="$T/tmux_win_cmd"
: > "$TMUX_WIN_CMD"

for i in $(seq 1 30); do curl -s -o /dev/null "http://127.0.0.1:$PORT/api/stats" && break; sleep 0.1; done

# 1. Path traversal / malicious desk JSON responses
echo bad_id > "$MODE_FILE"
OUT="$(tools/oma.sh next 2>&1)"; RC=$?
check "next rejects ../ problem.id" '[ $RC -ne 0 ] && [ ! -e "$REPO/.oma/leases/../../../pwn" ] && [ ! -e "$T/pwn" ]'

echo bad_file_hook > "$MODE_FILE"
OUT="$(tools/oma.sh next 2>&1)"; RC=$?
check "next rejects .git/hooks/post-checkout file" '[ $RC -ne 0 ] && [ ! -e "$REPO/.git/hooks/post-checkout" ] && [ ! -e "$REPO/.oma/leases/OkId" ]'

echo bad_file_dotdot > "$MODE_FILE"
OUT="$(tools/oma.sh next 2>&1)"; RC=$?
check "next rejects proofs/../../escape.lean" '[ $RC -ne 0 ] && [ ! -e "$T/escape.lean" ] && [ ! -e "$REPO/.oma/leases/OkId" ]'

echo bad_lease > "$MODE_FILE"
OUT="$(tools/oma.sh next 2>&1)"; RC=$?
check "next rejects query-injecting lease" '[ $RC -ne 0 ] && [ ! -e "$REPO/.oma/leases/OkId" ]'

# 2. CLI argument validation across subcommands
for cmd in beat check submit reduce brief explore release board plan bundle; do
  OUT="$(tools/oma.sh "$cmd" "../etc/passwd" 2>&1)"; RC=$?
  check "CLI rejects traversal in $cmd" '[ $RC -ne 0 ]'
done
OUT="$(tools/oma.sh take "../etc/passwd" 1 2>&1)"; RC=$?
check "CLI rejects traversal in take" '[ $RC -ne 0 ]'
OUT="$(tools/oma.sh release "OkId" "bad&injected=1" 2>&1)"; RC=$?
check "CLI rejects non-alnum release reason" '[ $RC -ne 0 ]'

# 3. Lease / since injection on beat and board
mkdir -p "$REPO/.oma/leases" "$REPO/.oma/seen"
printf 'good-lease\n' > "$REPO/.oma/leases/OkId"
printf '0&injected=1\n' > "$REPO/.oma/seen/OkId"
OUT="$(tools/oma.sh beat OkId 2>&1)"; RC=$?
check "beat rejects non-numeric seen file" '[ $RC -ne 0 ]'
OUT="$(tools/oma.sh board OkId 2>&1)"; RC=$?
check "board rejects non-numeric seen file" '[ $RC -ne 0 ]'

printf 'bad&reason=evil\n' > "$REPO/.oma/leases/OkId"
printf '0\n' > "$REPO/.oma/seen/OkId"
OUT="$(tools/oma.sh beat OkId 2>&1)"; RC=$?
check "beat rejects query-injecting lease token" '[ $RC -ne 0 ]'

# 4. Shell-to-Python injection in directory path containing single & double quotes
rm -f "$T/pwned_marker"
OUT="$(OMA_CHECK="$T/bin/stubcheck" tools/oma.sh check OkId 2>&1)"; RC=$?
check "oma.sh check handles quotes in REPO path safely" '[ $RC -eq 0 ] && [[ "$OUT" == *"ACCEPTED: stub ok"* ]]'

# Test tools/check.sh directly with quoted path up to FC validation (ensures catalog read works without injection)
OUT="$(OMA_FC="$T/missing_fc" tools/check.sh proofs/OeisA158110.a_0.lean "$T/verdict_q.json" 2>&1 || true)"
check "tools/check.sh parses catalog.json safely with quotes in ROOT" '[ -f "$T/verdict_q.json" ] && grep -q "expected" "$T/verdict_q.json"'

# 5. Cleanroom runner fail-closed checks + mock docker flag audit
OUT="$(tools/cleanroom/run-cleanroom.sh check "$REPO" "../etc/passwd" 2>&1)"; RC=$?
check "run-cleanroom check rejects ../etc/passwd" '[ $RC -ne 0 ]'
OUT="$(tools/cleanroom/run-cleanroom.sh check "$REPO" "proofs/../../etc/passwd" 2>&1)"; RC=$?
check "run-cleanroom check rejects proofs/../../etc/passwd" '[ $RC -ne 0 ]'
OUT="$(tools/cleanroom/run-cleanroom.sh lean "$REPO" "$REPO/proofs/OkId.lean" "Foo;id" 2>&1)"; RC=$?
check "run-cleanroom lean rejects injected module name" '[ $RC -ne 0 ]'
OUT="$(tools/cleanroom/run-cleanroom.sh bogus 2>&1)"; RC=$?
check "run-cleanroom rejects unknown subcommand" '[ $RC -eq 2 ]'

printf 'SECRET=1\n' > "$REPO/.env"
printf 'SECRET2=2\n' > "$REPO/.env.local"
printf 'SECRET_NPM=1\n' > "$REPO/.npmrc"
printf 'SECRET_NETRC=1\n' > "$REPO/.netrc"
mkdir -p "$REPO/.oma/leases"
printf 'SECRET_LEASE=1\n' > "$REPO/.oma/leases/demo"
ln -s "$REPO/proofs/OkId.lean" "$T/scratch_link.lean"
OUT="$(OMA_CLEANROOM_IMAGE='--privileged' tools/cleanroom/run-cleanroom.sh check "$REPO" "proofs/OkId.lean" 2>&1)"; RC=$?
check "run-cleanroom rejects flag-injecting OMA_CLEANROOM_IMAGE" '[ $RC -ne 0 ] && [[ "$OUT" == *"invalid OMA_CLEANROOM_IMAGE"* ]]'
OUT="$(OMA_CLEANROOM_MEMORY='8g;id' tools/cleanroom/run-cleanroom.sh check "$REPO" "proofs/OkId.lean" 2>&1)"; RC=$?
check "run-cleanroom rejects unsafe OMA_CLEANROOM_MEMORY" '[ $RC -ne 0 ] && [[ "$OUT" == *"invalid OMA_CLEANROOM_MEMORY"* ]]'
OUT="$(OMA_CLEANROOM_PIDS='0' tools/cleanroom/run-cleanroom.sh check "$REPO" "proofs/OkId.lean" 2>&1)"; RC=$?
check "run-cleanroom rejects unsafe OMA_CLEANROOM_PIDS" '[ $RC -ne 0 ] && [[ "$OUT" == *"invalid OMA_CLEANROOM_PIDS"* ]]'
OUT="$(tools/cleanroom/run-cleanroom.sh lean "$REPO" "$T/scratch_link.lean" 2>&1)"; RC=$?
check "run-cleanroom lean rejects symlink scratch file" '[ $RC -ne 0 ] && [[ "$OUT" == *"symlink"* ]]'
: > "$DOCKER_LOG"
OUT="$(tools/cleanroom/run-cleanroom.sh check "$REPO" "proofs/OkId.lean" "$T/cr_verdict.json")"; RC=$?
check "run-cleanroom check succeeds with mock docker and writes verdict" '[ $RC -eq 0 ] && [ -s "$T/cr_verdict.json" ] && grep -q "accepted" "$T/cr_verdict.json"'
check "run-cleanroom passes --network=none --cap-drop=ALL --user 1001:1001" 'grep -qx -- "--network=none" "$DOCKER_LOG" && grep -qx -- "--cap-drop=ALL" "$DOCKER_LOG" && grep -qx -- "--security-opt=no-new-privileges:true" "$DOCKER_LOG" && grep -qx -- "1001:1001" "$DOCKER_LOG"'
check "run-cleanroom mounts repo :ro with zero :rw mounts" 'grep -qx -- "$REPO:/work:ro" "$DOCKER_LOG" && ! grep -q ":rw$" "$DOCKER_LOG"'
check "run-cleanroom masks .env*, .npmrc, .netrc, .git, and .oma :ro" 'grep -Eq "^.+:/work/\.env:ro$" "$DOCKER_LOG" && grep -Eq "^.+:/work/\.env\.local:ro$" "$DOCKER_LOG" && grep -Eq "^.+:/work/\.npmrc:ro$" "$DOCKER_LOG" && grep -Eq "^.+:/work/\.netrc:ro$" "$DOCKER_LOG" && grep -Eq "^.+:/work/\.git:ro$" "$DOCKER_LOG" && grep -Eq "^.+:/work/\.oma:ro$" "$DOCKER_LOG" && ! grep -q "$REPO/\.env:/work" "$DOCKER_LOG"'
rm -rf "$REPO/.env" "$REPO/.env.local" "$REPO/.npmrc" "$REPO/.netrc" "$REPO/.oma"

# 6. fleet.sh OMA_KIND injection & prompt quoting
: > "$TMUX_WIN_CMD"
OUT="$(OMA_KIND='known; id' tools/fleet.sh 2 2>&1)"; RC=$?
check "fleet.sh rejects unsafe OMA_KIND before tmux" '[ $RC -ne 0 ] && [[ "$OUT" == *"invalid OMA_KIND"* ]] && [ ! -s "$TMUX_WIN_CMD" ]'
: > "$TMUX_WIN_CMD"
OUT="$(OMA_SITE="http://example.invalid/\$(touch $T/fleet_pwned)" OMA_AGENT_CMD='printf "%s\n"' tools/fleet.sh 1 2>&1)"; RC=$?
WORKER_CMD="$(sed 's/; while true; do.*//' "$TMUX_WIN_CMD" 2>/dev/null || true)"
bash -c "$WORKER_CMD; bash -c 'eval \"\\\$OMA_WORKER_CMD \\\"\\\$1\\\"\"' _ \"\$OMA_WORKER_PROMPT\"" > "$T/fleet_out" 2>&1 || true
check "fleet.sh quotes OMA_WORKER_PROMPT without shell expansion" '[ $RC -eq 0 ] && [ ! -e "$T/fleet_pwned" ] && grep -Fq "http://example.invalid/\$(touch" "$T/fleet_out"'
rm -rf "$REPO/.oma"
git -C "$REPO" worktree prune 2>/dev/null || true

# 7. check.sh tampered catalog upstreamCommit & workflow injection checks
mkdir -p "$T/bad_cat/data" "$T/bad_cat/proofs"
cp -r "$ROOT/tools" "$T/bad_cat/"
cp "$ROOT/proofs/OeisA158110.a_0.lean" "$T/bad_cat/proofs/OeisA158110.a_0.lean"
python3 -I -c 'import json,sys; d=json.load(open(sys.argv[1])); d["meta"]["upstreamCommit"]="not-a-sha && id"; json.dump(d, open(sys.argv[2], "w"))' "$ROOT/data/catalog.json" "$T/bad_cat/data/catalog.json"
OUT="$(OMA_FC="$T/missing_fc" bash -c 'cd "$1" && tools/check.sh proofs/OeisA158110.a_0.lean "$2" 2>&1' _ "$T/bad_cat" "$T/bad_cat/verdict.json" || true)"
check "tools/check.sh rejects non-40-hex upstreamCommit" '[ -f "$T/bad_cat/verdict.json" ] && grep -q "invalid upstreamCommit" "$T/bad_cat/verdict.json"'

# 8. Cross-platform supply-chain & PowerShell security checks across tools
check "no raw.githubusercontent.com/leanprover/elan/master/elan-init.sh remains in tools/" '! grep -rn "raw.githubusercontent.com/leanprover/elan/master/elan-init.sh" "$ROOT/tools"'
for sha in \
  0e8250aa2be86c7af929ade68db617af9edc8b9ccf6eaf5ece228250d0d032e2 \
  45cde3006f82f98804c94cf2ca4949d117060a5f3cc8afa62f523759947ee21f \
  a5123096d662216ceaf69d68d6bbabb118c024d20d270bf0d639a830dd4ff97e \
  27af24edeace839730e8c9119783f12d5f694327d4771605021ca09db1ab0a87; do
  check "install-elan.sh pins $sha" 'grep -q "$sha" "$ROOT/tools/install-elan.sh"'
done
check "install-elan.sh supports macOS shasum fallback" 'grep -q "shasum -a 256" "$ROOT/tools/install-elan.sh"'
check "Dockerfile pins both amd64 and arm64 digests matching install-elan.sh" 'grep -q "0e8250aa2be86c7af929ade68db617af9edc8b9ccf6eaf5ece228250d0d032e2" "$ROOT/tools/cleanroom/Dockerfile" && grep -q "45cde3006f82f98804c94cf2ca4949d117060a5f3cc8afa62f523759947ee21f" "$ROOT/tools/cleanroom/Dockerfile"'
check "install-elan.ps1 pins Windows SHA-256 and uses Get-FileHash" 'grep -q "63f50605424284927799702347e2bdbd99d017b9d80ae083c65ee2189c4caf75" "$ROOT/tools/install-elan.ps1" && grep -q "Get-FileHash" "$ROOT/tools/install-elan.ps1"'
check "run-cleanroom.ps1 enforces isolation flags, validators, symlink checks, and masking" 'grep -q -- "--network=none" "$ROOT/tools/cleanroom/run-cleanroom.ps1" && grep -q -- "--cap-drop=ALL" "$ROOT/tools/cleanroom/run-cleanroom.ps1" && grep -q "no-new-privileges:true" "$ROOT/tools/cleanroom/run-cleanroom.ps1" && grep -q "1001:1001" "$ROOT/tools/cleanroom/run-cleanroom.ps1" && grep -q ":/work:ro" "$ROOT/tools/cleanroom/run-cleanroom.ps1" && grep -q "\.env\*" "$ROOT/tools/cleanroom/run-cleanroom.ps1" && grep -q "Assert-Image" "$ROOT/tools/cleanroom/run-cleanroom.ps1" && grep -q "Assert-Memory" "$ROOT/tools/cleanroom/run-cleanroom.ps1" && grep -q "Assert-PidsLimit" "$ROOT/tools/cleanroom/run-cleanroom.ps1" && grep -q "\.git" "$ROOT/tools/cleanroom/run-cleanroom.ps1" && grep -q "\.oma" "$ROOT/tools/cleanroom/run-cleanroom.ps1"'
if command -v pwsh >/dev/null 2>&1; then
  check "PowerShell scripts parse cleanly with pwsh" 'pwsh -NoProfile -Command '\''$err=$null; [System.Management.Automation.Language.Parser]::ParseFile("'\''"$ROOT/tools/install-elan.ps1"'\''", [ref]$null, [ref]$err) | Out-Null; if($err.Count){exit 1}; [System.Management.Automation.Language.Parser]::ParseFile("'\''"$ROOT/tools/cleanroom/run-cleanroom.ps1"'\''", [ref]$null, [ref]$err) | Out-Null; if($err.Count){exit 1}'\'''
fi

echo
[ $FAILS -eq 0 ] && echo "ALL PASSED" || echo "$FAILS FAILED"
exit $FAILS
