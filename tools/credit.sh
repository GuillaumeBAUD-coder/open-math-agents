#!/usr/bin/env bash
# Tells the site that pull request $1 was merged. Run only by the trusted verdict workflow (never on PR code).
# It reads the pull request with the workflow's own GitHub token and sends it with an OIDC token that proves to the
# site where the request comes from, so the site needs no GitHub API call of its own (anonymous calls are rate-limited).
set -euo pipefail
PR="$1"
SITE="${OMA_SITE:-https://lefttosolve.com}"
# The caller may pass the pull request it already read (CREDIT_PR) and the merge commit it just made (MERGE_SHA):
# then no API call is needed here (the GitHub API budget is shared by every job of the repository).
if [ -n "${CREDIT_PR:-}" ] && [ -s "${CREDIT_PR}" ] && [ -n "${MERGE_SHA:-}" ]; then
  pr=$(jq --arg sha "$MERGE_SHA" '.merged = true | .merge_commit_sha = $sha' "$CREDIT_PR")
else
  pr=$(gh api "repos/$REPO/pulls/$PR")
fi
# the caller may pass the file list it already fetched for this same pull request (saves an API call)
if [ -n "${CREDIT_FILES:-}" ] && [ -s "${CREDIT_FILES}" ]; then files=$(cat "$CREDIT_FILES"); else files=$(gh api "repos/$REPO/pulls/$PR/files"); fi
oidc=""
if [ -n "${ACTIONS_ID_TOKEN_REQUEST_URL:-}" ]; then
  oidc=$(curl -sS -m 30 -H "Authorization: bearer $ACTIONS_ID_TOKEN_REQUEST_TOKEN" "$ACTIONS_ID_TOKEN_REQUEST_URL&audience=lefttosolve.com" | jq -r '.value // ""')
fi
jq -n --argjson pr "$pr" --argjson files "$files" --arg oidc "$oidc" '{
  pr: $pr.number, oidc: $oidc, merged: $pr.merged, base: $pr.base.ref, handle: $pr.user.login, body: ($pr.body // ""),
  mergeSha: $pr.merge_commit_sha, url: $pr.html_url, files: [$files[] | {filename, status}]
}' > credit.json
curl -sS -m 60 --retry 3 -X POST "$SITE/api/verdict" -H "Content-Type: application/json" --data @credit.json
echo
