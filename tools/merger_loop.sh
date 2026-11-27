#!/usr/bin/env bash
# The merger: one long-running trusted job that gives every finished check-proof run its verdict (tools/verdict_one.sh)
# within about a minute, and runs the backlog pass (tools/backlog_pass.sh) when the API budget allows. One runner slot
# instead of one queued verdict job per proof. Never checks out or runs pull request code.
# GitHub's API budget for GITHUB_TOKEN is shared by every job of the repository, so polling is kept cheap: the runs
# in progress are listed every 30 s (1-2 calls) and a run that leaves that list is handled; a full scan of the last
# two hours (a few pages) runs every 10 minutes to catch runs too short to be seen in progress.
# v3: a green check run means accepted and its title carries the PR number, so accepted runs need no artifact
# download; the loop also restarts itself on a new version of this script pushed to main (state kept in done/).
# Needs: GH_TOKEN REPO [OMA_SITE]; base/ (a checkout of main) in the current directory.
set -uo pipefail
export MERGER_V2=1 MERGER_V3=1
# Every GitHub call has a time limit: one call that never answers must not stall all verdicts.
GH_BIN="$(type -P gh)"; export GH_BIN
gh() { timeout 90 "$GH_BIN" "$@"; }
export -f gh
ROOT="$PWD"; mkdir -p "$ROOT/done"
SELF="$ROOT/base/tools/merger_loop.sh"; SELF_SHA=$(sha1sum "$SELF" | cut -d' ' -f1)
if [ -n "${MERGER_RESUME:-}" ]; then
  # restarted by an older version of this loop after an update: same job, same deadline, same state
  START=$MERGER_START; END=$MERGER_END; BPID=${MERGER_BPID:-}; LAST_BACKLOG=${MERGER_LAST_BACKLOG:-0}; LAST_SCAN=$(date -u +%s)
  touch "$ROOT/watch.txt" "$ROOT/prev_inprog.tsv"
  echo "merger: resumed on version $SELF_SHA"
else
  : > "$ROOT/watch.txt"; : > "$ROOT/prev_inprog.tsv"
  START=$(date -u +%s); END=$(( START + ${MERGER_SECONDS:-20400} ))   # 5 h 40 min, under the 6 h job limit
  BPID=""; LAST_BACKLOG=0; LAST_SCAN=0
fi
SLOTS=${SLOTS:-4}; declare -A SPID; LAST_REFRESH=0; LAST_OLD=0; OLDJOBS=1
iso() { date -u -d "@$1" +%Y-%m-%dT%H:%M:%SZ; }
JQ_RUN='[.id, .head_sha, .run_attempt, .html_url, .updated_at, (.conclusion // ""), (.display_title // "")] | @tsv'
remaining() { gh api rate_limit --jq '"\(.resources.core.remaining) \(.resources.core.reset)"' 2>/dev/null || echo "999 0"; }
budget() {  # never let the repository run dry: other jobs (checks, deploys) need the API too; GraphQL is checked too
  local rem reset grem greset; read -r rem reset grem greset < <(gh api rate_limit --jq '"\(.resources.core.remaining) \(.resources.core.reset) \(.resources.graphql.remaining) \(.resources.graphql.reset)"' 2>/dev/null || echo "999 0 999 0")
  echo "budget: core $rem, graphql $grem"
  if [ "${rem:-999}" -lt 300 ]; then echo "API budget low ($rem left), waiting for the reset"; sleep $(( reset - $(date -u +%s) + 5 )); fi
  if [ "${grem:-999}" -lt 60 ]; then echo "GraphQL budget low ($grem left), waiting for the reset"; sleep $(( greset - $(date -u +%s) + 5 )); fi
}
refresh() {  # main moved on (merges): pull it and sync each verdict slot's copy (rsync: only what changed)
  git -C "$ROOT/base" fetch -q --depth 1 origin main && git -C "$ROOT/base" reset -q --hard FETCH_HEAD; git -C "$ROOT/base" clean -fdq
  for d in $(seq 1 "$SLOTS"); do
    if command -v rsync >/dev/null; then rsync -a --delete "$ROOT/base/" "$ROOT/base_$d/"; else rm -rf "$ROOT/base_$d"; cp -a "$ROOT/base" "$ROOT/base_$d"; fi
  done
}
verdict() {  # $1 run id, $2 head sha, $3 attempt, $4 url, $5 completed before this loop started (1/0), $6 slot, $7 conclusion, $8 title
  local ID="$1" SHA="$2" ATT="$3" URL="$4" OLD="$5" B="$ROOT/base_$6" W="$ROOT/work_$6" CONC="$7" TITLE="$8" PR
  rm -rf "$W"; mkdir -p "$W"; ln -s "$B" "$W/base"
  if [ "$CONC" = success ] && [[ "$TITLE" =~ ^check-proof\ \#([0-9]+)$ ]]; then
    # green = accepted (check-proof fails every other verdict); kind and polarity come from the trusted re-lint
    mkdir -p "$W/artifact"; echo "${BASH_REMATCH[1]}" > "$W/artifact/pr.txt"; echo '{"verdict":"accepted","reason":""}' > "$W/artifact/verdict.json"
  elif ! gh run download "$ID" --repo "$REPO" -n verdict -D "$W/artifact" >/dev/null 2>&1; then
    # not finished yet (left the in-progress list for a re-run or a queue) or no artifact: look again later
    echo "$ID" >> "$ROOT/watch.txt"; rm -f "$ROOT/done/$ID.$ATT"; return 0
  fi
  PR=$(head -c 12 "$W/artifact/pr.txt" 2>/dev/null | tr -cd '0-9'); [ -n "$PR" ] || return 0
  if [ "$OLD" = 1 ] && gh api "repos/$REPO/issues/$PR/comments?per_page=100" --jq '.[].body' 2>/dev/null | grep -qF "$URL"; then
    return 0                                            # already reported (by verdict.yml or an earlier merger)
  fi
  mkdir -p "$ROOT/remerge"; local RM; RM=$(cat "$ROOT/remerge/$PR" 2>/dev/null || echo 0)
  ( cd "$W" && RELINT="$W/relint.json" RUN_ID="$ID" RUN_ATTEMPT="$ATT" HEAD_SHA="$SHA" RUN_URL="$URL" REMERGE="$RM" \
      timeout 900 bash "$B/tools/verdict_one.sh" ) > "$W/log.txt" 2>&1
  echo "#$PR run $ID.$ATT: exit $? $(grep -m1 -oiE 'rate limit|ACCEPTED|REJECTED|FAULT|already on main' "$W/log.txt" || true)"
  [ -e "$W/rerun.flag" ] && echo "$ID" >> "$ROOT/watch.txt"   # a fault re-runs the check: same run id, next attempt
  if [ -e "$W/remerge.flag" ]; then                               # merge refused: try the same verdict again later
    echo $((RM + 1)) > "$ROOT/remerge/$PR"; rm -f "$ROOT/done/$ID.$ATT"; echo "$ID" >> "$ROOT/watch.txt"
  fi
  git -C "$B" clean -fdq -- proofs reductions statements 2>/dev/null || true
}
refresh
while [ "$(date -u +%s)" -lt "$END" ]; do
  NOW=$(date -u +%s); budget
  : > cand.tsv
  # 1. runs that were in progress at the last poll and are not any more
  gh api --paginate "repos/$REPO/actions/workflows/check-proof.yml/runs?status=in_progress&per_page=100" --jq ".workflow_runs[] | $JQ_RUN" > inprog.tsv 2>/dev/null || cp prev_inprog.tsv inprog.tsv
  cut -f1 inprog.tsv | sort > now_ids; cut -f1 prev_inprog.tsv | sort > prev_ids
  comm -23 prev_ids now_ids > left_ids
  for LID in $(cat left_ids); do
    gh api "repos/$REPO/actions/runs/$LID" --jq "select(.status == \"completed\" and .conclusion != \"cancelled\") | $JQ_RUN" >> cand.tsv 2>/dev/null \
      || echo "$LID" >> watch.txt
  done
  mv inprog.tsv prev_inprog.tsv
  # 2. every 10 minutes (and at start): a full scan of runs created in the last two hours
  if [ $(( NOW - LAST_SCAN )) -ge 600 ]; then
    W0=$(( LAST_SCAN == 0 ? 3*3600 : 2*3600 )); LAST_SCAN=$NOW
    gh api --paginate "repos/$REPO/actions/workflows/check-proof.yml/runs?status=completed&per_page=100&created=>$(iso $(( NOW - W0 )))" \
      --jq ".workflow_runs[] | select(.conclusion != \"cancelled\") | $JQ_RUN" >> cand.tsv 2>/dev/null || true
  fi
  # 3. re-runs and runs that were not finished when first seen
  for WID in $(sort -u watch.txt); do
    gh api "repos/$REPO/actions/runs/$WID" --jq "select(.status == \"completed\" and .conclusion != \"cancelled\") | $JQ_RUN" >> cand.tsv 2>/dev/null || true
  done
  : > watch.txt
  # verdict jobs queued by the old per-proof trigger still run: leave their commits to them (no double report)
  if [ "$OLDJOBS" = 1 ] && [ $(( NOW - LAST_OLD )) -ge 300 ]; then
    LAST_OLD=$NOW; : > pending.txt
    gh api --paginate "repos/$REPO/actions/workflows/verdict.yml/runs?status=queued&per_page=100" \
      --jq '.workflow_runs[] | select(.event == "workflow_run") | .head_sha' >> pending.txt 2>/dev/null || echo x >> pending.txt
    [ -s pending.txt ] || OLDJOBS=0
  fi
  if [ $(( NOW - LAST_REFRESH )) -ge 120 ]; then
    LAST_REFRESH=$NOW; refresh
    if [ "$(sha1sum "$SELF" | cut -d' ' -f1)" != "$SELF_SHA" ]; then
      echo "merger: new version on main, restarting in place"
      export MERGER_RESUME=1 MERGER_START=$START MERGER_END=$END MERGER_BPID=$BPID MERGER_LAST_BACKLOG=$LAST_BACKLOG
      exec bash "$SELF"
    fi
  fi
  sort -u -t$'\t' -k1,1 cand.tsv > cand_u.tsv
  while IFS=$'\t' read -r ID SHA ATT URL UPD CONC TITLE; do
    [ -n "$ID" ] || continue
    [ -n "$CONC" ] || { echo "$ID" >> watch.txt; continue; }   # not finished yet
    [ -e "done/$ID.$ATT" ] && continue
    touch "done/$ID.$ATT"
    [ "$OLDJOBS" = 1 ] && grep -qx "$SHA" pending.txt 2>/dev/null && continue   # an old verdict job reports this one
    OLD=0; [ "$(date -u -d "$UPD" +%s 2>/dev/null || echo 0)" -lt "$START" ] && OLD=1
    while :; do
      FREE=""; for i in $(seq 1 "$SLOTS"); do { [ -z "${SPID[$i]:-}" ] || ! kill -0 "${SPID[$i]}" 2>/dev/null; } && { FREE=$i; break; }; done
      [ -n "$FREE" ] && break; sleep 1
    done
    verdict "$ID" "$SHA" "$ATT" "$URL" "$OLD" "$FREE" "$CONC" "$TITLE" & SPID[$FREE]=$!
  done < cand_u.tsv
  for i in $(seq 1 "$SLOTS"); do [ -n "${SPID[$i]:-}" ] && wait "${SPID[$i]}" 2>/dev/null; SPID[$i]=""; done
  # backlog: only when no pass is running, at most every 15 minutes, and with budget to spare for the verdicts
  read -r REM _ < <(remaining)
  if { [ -z "$BPID" ] || ! kill -0 "$BPID" 2>/dev/null; } && [ $(( NOW - LAST_BACKLOG )) -ge 900 ] && [ "${REM:-0}" -gt 1500 ]; then
    LAST_BACKLOG=$NOW; B="$ROOT/backlog"; rm -rf "$B"; mkdir -p "$B"; cp -a "$ROOT/base" "$B/base"
    ( cd "$B" && LANES=1 BACKLOG_MIN_BUDGET=800 timeout 3000 bash "$B/base/tools/backlog_pass.sh" 2>&1 | grep -E "merged|batch|done:|budget" | sed 's/^/backlog: /' ) &
    BPID=$!
  fi
  sleep 30
done
wait
echo "merger: time is up; the next scheduled run takes over"
