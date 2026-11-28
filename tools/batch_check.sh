#!/usr/bin/env bash
# Batch checker: one runner restores the Lean tree once and checks many pull requests, each in its own sandbox.
# Runs in .github/workflows/batch-check.yml (on main, read-only token, no secrets). Trusted harness: this script, and
# the checker it runs (tools/check.sh, tools/lint.py, tools/prooflen.py), come from main; a pull request contributes
# its one Lean file and nothing else. Verdicts are those of check-proof.yml, step for step (same diff rule, same
# duplicate rule, same lint, same compile and axiom audit); the merger reads them from this job's artifact bv-<shard>
# (tools/batch_verdicts.sh) and gives them exactly as it gives a check-proof run's (tools/verdict_one.sh).
#
#   batch_check.sh worker     long-running (started in the background by the workflow): finds the open pull requests
#                             of this shard that have no verdict yet (git ls-remote: no API budget), checks them
#                             oldest first, LANES at a time (a Lean check uses about one core of the runner's four)
#   batch_check.sh publish    one round: waits (bounded) for new verdicts and writes $BC/pub (the next step uploads it)
#   batch_check.sh stop       end of the job: no new check, running ones may finish, last publish
#   batch_check.sh once <pr>  check one pull request now and print the verdict (by hand; nothing is recorded)
#
# Each pull request is checked by tools/check.sh inside bubblewrap: no network, empty environment (no token), its own
# pid/ipc/uts/user namespaces, the toolchain, Mathlib and the repository read-only, a fresh writable copy of
# formal-conjectures (its sources and prebuilt libraries) that is thrown away afterwards, a private /tmp, and one output
# directory that only this harness reads. Nothing a check writes survives into another one. A check that fails to
# compile or runs out of time while others ran beside it is checked again alone before that verdict is given, so
# sharing the runner never turns a proof that passes alone into a rejection.
#
# Env: SHARD SHARDS (this job takes the pull requests whose number % SHARDS == SHARD), BC (work dir), WS (checkout of
# main: tools data reductions statements), OMA_FC, ELAN_HOME, BATCH_DEADLINE (unix time: no new check after it), LANES.
# State in $BC: done.tsv (pull request, head, time: verdict given), verdicts.jsonl, since.txt (where the batch path
# starts), inherited from the previous job of the shard through its artifact.
set -uo pipefail
CMD="${1:-}"
BC="${BC:?}"; WS="${WS:?}"; SHARD="${SHARD:-0}"; SHARDS="${SHARDS:-1}"; LANES="${LANES:-2}"
mkdir -p "$BC/pub"
touch "$BC/done.tsv" "$BC/verdicts.jsonl" "$BC/skip.txt"
log() { echo "$(date -u +%T) $*"; }

# ---- one check, in two parts -----------------------------------------------------------------------------------------
# prepare: everything that reads git (the diff rule, the duplicate rule, the tree the check will see). Runs in the
# worker itself, one at a time, never while main is being refreshed. Returns 0 with $W/verdict.json when that is the
# verdict already, 1 when the sandbox must decide ($W/file names the file).
prepare() {  # $1 work dir, $2 PR, $3 merge commit
  local W="$1" PR="$2" M="$3" ST F
  rm -rf "$W"; mkdir -p "$W/root" "$W/out"
  # Exactly one new file under proofs/, reductions/ or statements/ (check-proof.yml, same texts).
  git -C "$WS" diff --name-status "$M^1" "$M" > "$W/diff.txt" 2>/dev/null || { echo '{"verdict":"fault","reason":"could not read the pull request diff"}' > "$W/verdict.json"; return 0; }
  if [ "$(wc -l < "$W/diff.txt")" != "1" ]; then
    echo '{"verdict":"rejected","reason":"a pull request must add exactly one file under proofs/, reductions/ or statements/ and change nothing else"}' > "$W/verdict.json"; return 0
  fi
  read -r ST F < "$W/diff.txt"
  if ! printf '%s' "$F" | grep -Eq "^(proofs|reductions|statements)/[A-Za-z0-9_.'-]+\.lean$" || { [ "$ST" != "A" ] && ! { [ "$ST" = "M" ] && printf '%s' "$F" | grep -q '^proofs/'; }; }; then
    echo '{"verdict":"rejected","reason":"the one change must be a new file proofs/<id>.lean, reductions/<id>.R<n>.lean or statements/<id>.lean (letters, digits, _ . - only), or a shorter version of a proofs/<id>.lean already on main"}' > "$W/verdict.json"; return 0
  fi
  # The tree the check sees: main as it is now (hard links, read-only in the sandbox) plus the submitted file.
  cp -al "$WS/tools" "$WS/data" "$WS/reductions" "$WS/statements" "$W/root/"
  mkdir -p "$W/root/$(dirname "$F")"; rm -f "$W/root/$F"
  git -C "$WS" show "$M:$F" > "$W/root/$F" 2>/dev/null || { echo '{"verdict":"fault","reason":"could not read the submitted file"}' > "$W/verdict.json"; return 0; }
  # Already on main? (shortest-proof rule for a proof; anything else is turned away)
  if git -C "$WS" cat-file -e "HEAD:$F" 2>/dev/null; then
    if printf '%s' "$F" | grep -q '^proofs/'; then
      git -C "$WS" show "HEAD:$F" > "$W/old.lean"
      local RES NEW OLD; read -r RES NEW OLD < <(python3 -I "$WS/tools/prooflen.py" "$W/old.lean" "$W/root/$F")
      if [ "$RES" != shorter ]; then
        FILE="$F" NEW="$NEW" OLD="$OLD" OUTF="$W/verdict.json" python3 -I -c 'import json,os; json.dump({"verdict":"rejected","reason":"already proved: "+os.environ["FILE"]+" is on main. A new proof replaces it only if it is at least 5% and 20 characters shorter, comments and spaces not counted (yours: "+os.environ["NEW"]+", current: "+os.environ["OLD"]+"); otherwise take another problem"},open(os.environ["OUTF"],"w"))'
        return 0
      fi
    else
      FILE="$F" OUTF="$W/verdict.json" python3 -I -c 'import json,os; json.dump({"verdict":"rejected","reason":"already on main: "+os.environ["FILE"]+" (someone else'"'"'s was merged first); take another problem"},open(os.environ["OUTF"],"w"))'
      return 0
    fi
  fi
  printf '%s' "$F" > "$W/file"
  return 1
}

# sandbox: lint, compile and audit (tools/check.sh) in bubblewrap. formal-conjectures gets a fresh writable copy
# (sources and prebuilt libraries); Mathlib and the toolchain are bound read-only. Writes $W/verdict.json.
sandbox() {  # $1 work dir
  local W="$1" F FW RC; F=$(cat "$W/file"); FW="$W/up"; mkdir -p "$FW/.lake/packages"
  (cd "$OMA_FC" && tar --exclude=./.lake -cf - .) | tar -xf - -C "$FW"
  cp -a "$OMA_FC/.lake/build" "$FW/.lake/build"
  timeout -k 30 3400 bwrap --unshare-all --die-with-parent --new-session --clearenv \
    --ro-bind /usr /usr --symlink usr/bin /bin --symlink usr/sbin /sbin --symlink usr/lib /lib --symlink usr/lib64 /lib64 \
    --ro-bind /etc /etc --proc /proc --dev /dev --tmpfs /tmp \
    --ro-bind "$ELAN_HOME" "$ELAN_HOME" \
    --bind "$FW" "$OMA_FC" --ro-bind "$OMA_FC/.lake/packages" "$OMA_FC/.lake/packages" \
    --ro-bind "$W/root" /work/root --bind "$W/out" /work/out --chdir /work/root \
    --setenv PATH "$ELAN_HOME/bin:/usr/bin:/bin" --setenv HOME /tmp --setenv LANG C.UTF-8 \
    --setenv ELAN_HOME "$ELAN_HOME" --setenv OMA_FC "$OMA_FC" \
    bash tools/check.sh "$F" /work/out/verdict.json > "$W/sandbox.log" 2>&1
  RC=$?
  if [ -s "$W/out/verdict.json" ]; then cp "$W/out/verdict.json" "$W/verdict.json"
  else printf '{"verdict":"fault","reason":"checker produced no verdict (exit %s)"}' "$RC" > "$W/verdict.json"; fi
  rm -rf "$FW"
}

# ---- record a verdict ------------------------------------------------------------------------------------------------
# Only the fields the merger reads, with their types checked; the pull request and commits come from here, never from
# the file a check wrote. A fault is retried (up to 3 checks) before it is published.
record() {  # $1 work dir, $2 PR, $3 merge, $4 head; sets RECORDED=1 once the verdict is kept for publishing
  local W="$1" PR="$2" M="$3" H="$4" OUT V; RECORDED=0
  OUT=$(PR="$PR" M="$M" H="$H" python3 -I - "$W/verdict.json" <<'PY'
import json, os, sys, time
try:
    d = json.load(open(sys.argv[1]))
    assert isinstance(d, dict)
except Exception:
    d = {"verdict": "fault", "reason": "unreadable verdict"}
v = d.get("verdict")
if v not in ("accepted", "rejected", "fault"):
    v, d["reason"] = "fault", "unknown verdict"
s = lambda k: d.get(k) if isinstance(d.get(k), str) else None
print(json.dumps({"pr": int(os.environ["PR"]), "head": os.environ["H"], "merge": os.environ["M"], "verdict": v,
                  "reason": (s("reason") or "")[:2000], "problem": s("problem"), "kind": s("kind"),
                  "polarity": s("polarity"), "t": int(time.time())}, ensure_ascii=False))
PY
)
  [ -n "$OUT" ] || return 0
  V=$(printf '%s' "$OUT" | python3 -I -c 'import json,sys;print(json.load(sys.stdin)["verdict"])')
  if [ "$V" = fault ]; then
    local T; T=$(( $(cat "$BC/tries.$PR.$H" 2>/dev/null || echo 0) + 1 )); echo "$T" > "$BC/tries.$PR.$H"
    if [ "$T" -lt 3 ]; then log "#$PR ${H:0:10}: fault (attempt $T), retried later: $(printf '%s' "$OUT" | head -c 300)"; return 0; fi
  fi
  printf '%s\n' "$OUT" >> "$BC/verdicts.jsonl"
  printf '%s\t%s\t%s\n' "$PR" "$H" "$(date -u +%s)" >> "$BC/done.tsv"; RECORDED=1
  log "#$PR ${H:0:10}: $V $(printf '%s' "$OUT" | python3 -I -c 'import json,sys;print(json.load(sys.stdin)["reason"][:120])')"
}

# did this check fail in a way that sharing the runner could have caused? (then it is checked again alone)
contended() {  # $1 work dir
  python3 -I -c 'import json,sys
try: d = json.load(open(sys.argv[1]))
except Exception: sys.exit(1)
r = d.get("reason") or ""
sys.exit(0 if d.get("verdict") in ("rejected", "fault") and (r.startswith("does not compile") or r.startswith("timeout") or r.startswith("compiler reported errors") or r.startswith("checker produced no verdict") or r.startswith("could not build")) else 1)' "$1/verdict.json"
}

# ---- the worker loop -------------------------------------------------------------------------------------------------
worker() {
  declare -A DONE=() SKIP=() STALE=() FETCHED=() LANE_ITEM=() LANE_PID=() LANE_T0=()
  while IFS=$'\t' read -r P H _; do [ -n "$H" ] && DONE["$P.$H"]=1; done < "$BC/done.tsv"
  while read -r K; do [ -n "$K" ] && SKIP["$K"]=1; done < "$BC/skip.txt"
  local LAST_MAIN=0 LAST_REFS=0 BATCH_FROM_PR BATCH_SINCE SOLO="" L
  # Where the batch path starts: kept from job to job (since.txt travels in the artifact), set by the first job to
  # "pull requests opened from now on, and newer heads of older ones"; the older ones are check-proof.yml's.
  if [ ! -s "$BC/since.txt" ]; then
    local MAXPR; MAXPR=$(git -C "$WS" ls-remote origin 'refs/pull/*/head' 2>/dev/null | awk -F/ '{if ($3 > m) m = $3} END {print m + 0}')
    [ "$MAXPR" -gt 0 ] || { log "worker: cannot list pull requests"; touch "$BC/worker.done"; return 1; }
    echo "$(( MAXPR + 1 )) $(date -u +%s)" > "$BC/since.txt"
  fi
  read -r BATCH_FROM_PR BATCH_SINCE < "$BC/since.txt"
  log "worker: shard $SHARD of $SHARDS, $LANES lanes, ${#DONE[@]} verdicts inherited; pull requests from #$BATCH_FROM_PR, and heads of older ones committed after $(date -u -d "@$BATCH_SINCE" +%FT%TZ)"
  busy() { local n=0 l; for l in "${!LANE_PID[@]}"; do n=$((n + 1)); done; echo "$n"; }
  finish() {  # $1 lane: its check ended
    local L="$1" P H M W="$BC/w$1"; read -r P H M <<< "${LANE_ITEM[$1]}"
    if [ "$LANES" -gt 1 ] && contended "$W"; then
      SOLO="$P $H $M"; log "#$P ${H:0:10}: $(python3 -I -c 'import json,sys;print(json.load(open(sys.argv[1])).get("reason","")[:60])' "$W/verdict.json") beside other checks: checked again alone"
    else
      record "$W" "$P" "$M" "$H"; [ "$RECORDED" = 1 ] && DONE["$P.$H"]=1
      log "#$P checked in $(( $(date -u +%s) - ${LANE_T0[$1]:-0} )) s"
    fi
    unset "LANE_ITEM[$1]" "LANE_PID[$1]" "LANE_T0[$1]"
  }
  while :; do
    # collect the lanes whose check ended
    for L in "${!LANE_PID[@]}"; do kill -0 "${LANE_PID[$L]}" 2>/dev/null || { wait "${LANE_PID[$L]}" 2>/dev/null; finish "$L"; }; done
    if [ "$(date -u +%s)" -ge "$BATCH_DEADLINE" ] || [ -e "$BC/stop" ]; then
      [ "$(busy)" = 0 ] && break; sleep 2; continue
    fi
    # a check to repeat alone: wait until the runner is free, then run it in the foreground
    if [ -n "$SOLO" ]; then
      [ "$(busy)" = 0 ] || { sleep 2; continue; }
      local P H M; read -r P H M <<< "$SOLO"; SOLO=""
      local T0; T0=$(date -u +%s)
      prepare "$BC/w0" "$P" "$M" || sandbox "$BC/w0"
      record "$BC/w0" "$P" "$M" "$H"; [ "$RECORDED" = 1 ] && DONE["$P.$H"]=1
      log "#$P checked alone in $(( $(date -u +%s) - T0 )) s"; continue
    fi
    if [ "$(busy)" -ge "$LANES" ]; then sleep 2; continue; fi
    local NOW; NOW=$(date -u +%s)
    # main as it is now, at most every 2 minutes, only while no check is being prepared (they read it)
    if [ $(( NOW - LAST_MAIN )) -ge 120 ]; then
      git -C "$WS" fetch -q --depth 1 origin main 2>/dev/null && git -C "$WS" checkout -q -f FETCH_HEAD 2>/dev/null && LAST_MAIN=$NOW
    fi
    # open pull requests (GitHub keeps refs/pull/<n>/merge only while a pull request is open and mergeable): read
    # again at most every 15 seconds
    if [ $(( NOW - LAST_REFS )) -ge 15 ] || [ ! -s "$BC/todo.txt" ]; then
      [ $(( NOW - LAST_REFS )) -ge 15 ] || { sleep $(( 15 - NOW + LAST_REFS )); NOW=$(date -u +%s); }
      LAST_REFS=$NOW
      if ! git -C "$WS" ls-remote origin 'refs/pull/*/head' 'refs/pull/*/merge' > "$BC/refs.txt" 2>/dev/null; then sleep 10; continue; fi
      awk -v s="$SHARD" -v n="$SHARDS" '{split($2,a,"/"); if (a[3] % n == s) print a[3], a[4], $1}' "$BC/refs.txt" > "$BC/mine.txt"
      # pull request, head, merge: only those with both refs, oldest first
      awk '$2=="head"{h[$1]=$3} $2=="merge"{m[$1]=$3} END{for (p in m) if (p in h) print p, h[p], m[p]}' "$BC/mine.txt" | sort -n > "$BC/open.txt"
      : > "$BC/todo.txt"
      while read -r P H M; do
        [ -n "${DONE[$P.$H]:-}" ] || [ -n "${SKIP[$P.$H]:-}" ] || [ -n "${STALE[$P.$M]:-}" ] || echo "$P $H $M" >> "$BC/todo.txt"
      done < "$BC/open.txt"
      # merge commits not fetched yet (one fetch per hundred; those already here are not asked for again)
      # (refs, not objects, are compared: asking a partial clone for a missing object makes it fetch that object)
      if [ -s "$BC/todo.txt" ]; then
        git -C "$WS" for-each-ref --format='%(refname:lstrip=3) %(objectname)' refs/oma/m/ > "$BC/fetched.txt"
        awk 'NR == FNR {f[$1] = $2; next} f[$1] != $3 {print "+refs/pull/" $1 "/merge:refs/oma/m/" $1}' "$BC/fetched.txt" "$BC/todo.txt" \
          | xargs -r -n 100 git -C "$WS" fetch -q --no-tags --depth 2 origin 2>/dev/null || true
        git -C "$WS" for-each-ref --format='%(refname:lstrip=3) %(objectname)' refs/oma/m/ > "$BC/fetched.txt"
        FETCHED=(); while read -r P M; do FETCHED["$P"]=$M; done < "$BC/fetched.txt"
      fi
    fi
    local PICK="" P H M
    while read -r P H M; do
      [ -n "${DONE[$P.$H]:-}" ] || [ -n "${SKIP[$P.$H]:-}" ] && continue
      local RUNNING=0 IT; for IT in "${LANE_ITEM[@]}"; do [ "${IT%% *}" = "$P" ] && RUNNING=1; done
      [ "$RUNNING" = 0 ] || continue
      [ "${FETCHED[$P]:-}" = "$M" ] || continue                                                   # not fetched yet
      # a merge ref that GitHub has not recomputed for the newest head: skipped until it changes
      [ "$(git -C "$WS" rev-parse -q --verify "$M^2" 2>/dev/null)" = "$H" ] || { STALE["$P.$M"]=1; continue; }
      # left to check-proof.yml: pull requests filed before the batch path existed (number below BATCH_FROM_PR) unless
      # their head was committed after it started, and pull requests that touch none of proofs/, reductions/,
      # statements/ (check-proof does not run for them either)
      if { [ "$P" -lt "$BATCH_FROM_PR" ] && [ "$(git -C "$WS" log -1 --format=%ct "$H" 2>/dev/null || echo 0)" -lt "$BATCH_SINCE" ]; } \
         || ! git -C "$WS" diff --name-only "$M^1" "$M" 2>/dev/null | grep -qE '^(proofs|reductions|statements)/'; then
        SKIP["$P.$H"]=1; echo "$P.$H" >> "$BC/skip.txt"; continue
      fi
      PICK="$P $H $M"; break
    done < "$BC/todo.txt"
    if [ -z "$PICK" ]; then : > "$BC/todo.txt"; [ "$(busy)" = 0 ] && sleep 5; continue; fi
    read -r P H M <<< "$PICK"
    # a free lane
    for L in $(seq 1 "$LANES"); do [ -z "${LANE_PID[$L]:-}" ] && break; done
    LANE_T0[$L]=$(date -u +%s); LANE_ITEM[$L]="$P $H $M"
    if prepare "$BC/w$L" "$P" "$M"; then
      record "$BC/w$L" "$P" "$M" "$H"; [ "$RECORDED" = 1 ] && DONE["$P.$H"]=1
      log "#$P decided before compiling"; unset "LANE_ITEM[$L]" "LANE_T0[$L]"; continue
    fi
    sandbox "$BC/w$L" & LANE_PID[$L]=$!
  done
  log "worker: stopped"
  touch "$BC/worker.done"
}

# ---- publishing ------------------------------------------------------------------------------------------------------
# pub/verdicts.jsonl: every verdict of the last 3 hours (this job's and the ones it inherited), so a merger that was
# slow to read one round still finds them in the next; pub/done.tsv: what the next job of this shard must not redo.
publish_now() {
  python3 -I - "$BC" <<'PY'
import json, os, sys, time
bc = sys.argv[1]; now = time.time(); keep = []; n = 0
for line in open(os.path.join(bc, "verdicts.jsonl"), encoding="utf-8"):
    if not line.endswith("\n"):
        break   # being written: the next round takes it
    n += 1
    try:
        d = json.loads(line)
    except Exception:
        continue
    if now - d.get("t", 0) <= 10800:
        keep.append(line)
open(os.path.join(bc, "pub", "verdicts.jsonl"), "w", encoding="utf-8").writelines(keep)
rows = {}
for line in open(os.path.join(bc, "done.tsv")):
    p = line.rstrip("\n").split("\t")
    if len(p) >= 3 and p[2].isdigit() and now - int(p[2]) <= 4 * 86400:
        rows[(p[0], p[1])] = p[2]
with open(os.path.join(bc, "pub", "done.tsv"), "w") as f:
    for (a, b), t in rows.items():
        f.write(f"{a}\t{b}\t{t}\n")
open(os.path.join(bc, "published.count"), "w").write("%d\n" % n)
PY
  [ -s "$BC/since.txt" ] && cp "$BC/since.txt" "$BC/pub/since.txt"
  [ -n "${GITHUB_ENV:-}" ] && echo "BV_CHANGED=1" >> "$GITHUB_ENV"
  log "published $(wc -l < "$BC/pub/verdicts.jsonl") verdicts"
}
publish() {  # one round: new verdicts go out at most once a minute; a round waits at most PUBLISH_WAIT seconds
  [ -n "${GITHUB_ENV:-}" ] && echo "BV_CHANGED=0" >> "$GITHUB_ENV"
  local START; START=$(date -u +%s)
  while :; do
    local N P NOW LASTP; N=$(wc -l < "$BC/verdicts.jsonl"); P=$(cat "$BC/published.count" 2>/dev/null || echo 0)
    NOW=$(date -u +%s); LASTP=$(stat -c %Y "$BC/published.count" 2>/dev/null || echo 0)
    if [ "$N" -gt "$P" ] && { [ $(( NOW - LASTP )) -ge "${PUBLISH_EVERY:-60}" ] || [ -e "$BC/worker.done" ] || [ $(( NOW - START )) -ge "${PUBLISH_WAIT:-120}" ]; }; then
      publish_now; break
    fi
    if [ -e "$BC/worker.done" ] || [ $(( NOW - START )) -ge "${PUBLISH_WAIT:-120}" ]; then break; fi
    sleep 5
  done
  tail -n 3 "$BC/worker.log" 2>/dev/null || true
}
stop() {
  touch "$BC/stop"
  local I; for I in $(seq 1 "${STOP_WAIT:-600}"); do [ -e "$BC/worker.done" ] && break; sleep 1; done
  publish_now
  echo "--- worker log (last 40 lines)"; tail -n 40 "$BC/worker.log" 2>/dev/null || true
}

once() {  # $1 PR
  local P="$1" M H
  git -C "$WS" fetch -q --no-tags --depth 2 origin "+refs/pull/$P/merge:refs/oma/m/$P" || { echo "no merge ref for #$P" >&2; return 1; }
  M=$(git -C "$WS" rev-parse "refs/oma/m/$P"); H=$(git -C "$WS" rev-parse "$M^2")
  prepare "$BC/w0" "$P" "$M" || sandbox "$BC/w0"
  python3 -I -c 'import json,sys;d=json.load(open(sys.argv[1]));d.pop("log",None);print(json.dumps(d))' "$BC/w0/verdict.json"
}

case "$CMD" in
  worker) worker ;;
  once) once "${2:?pull request number}" ;;
  publish) publish ;;
  stop) stop ;;
  *) echo "usage: batch_check.sh worker|publish|stop|once <pr>" >&2; exit 2 ;;
esac
