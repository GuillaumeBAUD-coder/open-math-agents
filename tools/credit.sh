#!/usr/bin/env bash
# Reports a merged submission to the site: PR number, problem, author, outcome, agent/model lines from the PR body.
# Authenticated by this workflow's GitHub OIDC token (audience OIDC_AUDIENCE); the site checks repository and workflow.
set -euo pipefail
PR="$1"; OUTCOME="${2:-}"; REPO="${GITHUB_REPOSITORY}"
SITE="$(python3 -I -c 'import json,re;print(json.loads(re.sub(r"//[^\n]*","",open("base/wrangler.jsonc").read()))["vars"]["SITE"])')"
AUD="$(python3 -I -c 'import json,re;print(json.loads(re.sub(r"//[^\n]*","",open("base/wrangler.jsonc").read()))["vars"]["OIDC_AUDIENCE"])')"
gh api "repos/$REPO/pulls/$PR" > pr.json
gh api "repos/$REPO/pulls/$PR/files?per_page=100" --jq '[.[]|{filename,status}]' > files.json
(cd base && python3 -I tools/classify.py < ../files.json) > class.json
[ "$(jq -r .ok class.json)" = "true" ] || { echo "not a submission"; exit 0; }
KIND=$(jq -r .kind class.json); VERIFY=$(jq -r .verify class.json); ID=$(jq -r .id class.json)
# The outcome follows the problem's verification contract: a Lean proof settles only a `lean` problem (otherwise it is
# a formalised special case), an interval claim is "certified", a re-run is "reproduced", a review is "reviewed".
if [ -z "$OUTCOME" ]; then
  case "$KIND" in
    lean) [ "$VERIFY" = "lean" ] && OUTCOME=proved || OUTCOME=formalized ;;
    compute) jq -e 'has("interval")' "base/evidence/$ID/claim.json" >/dev/null 2>&1 && OUTCOME=certified || OUTCOME=reproduced ;;
    review) OUTCOME=reviewed ;;
  esac
fi
BODY="$(jq -r '.body // ""' pr.json)"
AGENT="$(printf '%s' "$BODY" | sed -n 's/^Agent:[[:space:]]*//p' | head -1 | cut -c1-64)"
MODEL="$(printf '%s' "$BODY" | sed -n 's/^Model:[[:space:]]*//p' | head -1 | cut -c1-64)"
TOKEN="$(curl -sS -H "Authorization: bearer $ACTIONS_ID_TOKEN_REQUEST_TOKEN" "$ACTIONS_ID_TOKEN_REQUEST_URL&audience=$AUD" | jq -r .value)"
jq -n --arg token "$TOKEN" --argjson pr "$PR" --arg problem "$ID" --arg handle "$(jq -r .user.login pr.json)" --arg outcome "$OUTCOME" --arg agent "$AGENT" --arg model "$MODEL" \
  '{token:$token, pr:$pr, problem:$problem, handle:$handle, outcome:$outcome, agent:$agent, model:$model}' \
  | curl -sS -X POST "$SITE/api/verdict" -H 'content-type: application/json' --data-binary @-; echo
