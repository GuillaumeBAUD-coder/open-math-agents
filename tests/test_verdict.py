"""Exercise the merger's verdict reporting with mocked GitHub and Git commands."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


VERDICT = Path(__file__).resolve().parents[1] / "tools" / "verdict_one.sh"
RUN_URL = "https://example.test/actions/runs/1"

GITHUB = '''#!/usr/bin/env python3
import json
import os
from pathlib import Path
import sys

scenario = os.environ["SCENARIO"]
events = Path("events.jsonl")
calls = [json.loads(line) for line in events.read_text().splitlines()] if events.exists() else []
with events.open("a") as f:
    print(json.dumps(sys.argv[1:]), file=f)
match sys.argv[1:]:
    case ["api", "repos/owner/repo/pulls/42"] as call:
        head = "new-head" if scenario == "new-head" and call in calls else "checked-head"
        merged = scenario == "graphql-merged" and call in calls
        state = "closed" if merged or Path("closed").exists() else "open"
        print(json.dumps({"state": state, "base": {"ref": "main"}, "head": {"sha": head},
                          "labels": [], "draft": False, "merged": merged, "merge_commit_sha": "squash-head",
                          "user": {"login": "solver"}}))
    case ["api", "repos/owner/repo/pulls/42/files"]:
        print(json.dumps([{"filename": "proofs/Target.lean",
                           "status": "modified" if scenario == "shorter" else "added"}]))
    case ["api", "repos/owner/repo/contents/proofs/Target.lean?ref=checked-head", "--jq", ".content"]:
        print("VHJ1ZQo=")
    case ["api", "repos/owner/repo/contents/proofs/Target.lean?ref=main", "--jq", ".content"]:
        print("RmFsc2UK")
    case ["api", "-X", "PUT", "repos/owner/repo/pulls/42/merge", "-f", "merge_method=squash", "-f", "sha=checked-head"]:
        if scenario in {"success", "shorter", "credit-failed"}:
            print('{"merged":true,"sha":"squash-head"}')
        elif scenario == "merge-false":
            print('{"merged":false,"message":"merge refused"}')
        elif scenario.startswith("graphql-"):
            sys.exit("Resource not accessible by integration")
        else:
            sys.exit("merge refused")
    case ["pr", "merge", "42", "--repo", "owner/repo", "--squash", "--match-head-commit", "checked-head"]:
        pass
    case ["api", "repos/owner/repo/contents/proofs/Target.lean?ref=main"]:
        if scenario not in {"duplicate", "new-head", "close-failed"}:
            sys.exit(1)
        print('{}')
    case ["api", "-X", "PATCH", "repos/owner/repo/pulls/42", "-f", "state=closed"]:
        if scenario == "close-failed":
            sys.exit("closure refused")
        Path("closed").touch()
    case ["api", "repos/owner/repo/issues/42/comments", "-f", body] if body.startswith("body="):
        pass
    case _:
        sys.exit("unexpected GitHub call")
'''

GIT = '''#!/usr/bin/env bash
[[ "$SCENARIO" == local-duplicate ]] || exit 1
case "$*" in
  '-C base fetch -q --depth 1 origin main'|'-C base checkout -q FETCH_HEAD -- statements reductions data'|\
  '-C base cat-file -e FETCH_HEAD:proofs/Target.lean') exit 0 ;;
  *) exit 1 ;;
esac
'''


class VerdictTest(unittest.TestCase):
    def setUp(self):
        work = tempfile.TemporaryDirectory()
        self.addCleanup(work.cleanup)
        self.work = Path(work.name)
        for folder in ("bin", "artifact", "base/data", "base/tools"):
            (self.work / folder).mkdir(parents=True)
        self.write("artifact/pr.txt", "42\n")
        self.write("artifact/verdict.json", '{"verdict":"accepted"}')
        self.write("base/data/catalog.json", '{"problems":[]}')
        self.write("base/tools/lint.py", '''print('{"type":"proof","kind":"known","polarity":"proof"}')''')
        self.write("base/tools/prooflen.py", 'print("shorter 50 100")')
        self.write("base/tools/credit.sh", '''printf '%s\\n' '["credit","42"]' >> events.jsonl
test "$SCENARIO" != credit-failed''')
        self.write("bin/gh", GITHUB).chmod(0o755)
        self.write("bin/git", GIT).chmod(0o755)

    def write(self, name, content):
        path = self.work / name
        path.write_text(content)
        return path

    def run_verdict(self, scenario, remerge=0):
        result = subprocess.run(
            ["bash", str(VERDICT)], cwd=self.work, text=True, capture_output=True, timeout=10,
            env={**os.environ, "PATH": f"{self.work / 'bin'}:{os.environ['PATH']}",
                 "SCENARIO": scenario, "REPO": "owner/repo", "HEAD_SHA": "checked-head",
                 "RUN_URL": RUN_URL, "REMERGE": str(remerge), "RELINT": str(self.work / "relint.json"),
                 "OMA_SITE": "https://lefttosolve.test", "CREDIT_RETRY_FILE": str(self.work / "credit-retry")},
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.calls = [json.loads(line) for line in (self.work / "events.jsonl").read_text().splitlines()]
        self.comments = [call[-1].removeprefix("body=") for call in self.calls
                         if call[:2] == ["api", "repos/owner/repo/issues/42/comments"]]

    def assert_closed_duplicate(self):
        self.assertTrue((self.work / "closed").exists())
        self.assertFalse((self.work / "remerge.flag").exists())
        self.assertNotIn(["credit", "42"], self.calls)
        self.assertEqual(self.comments, [f"Closed because `proofs/Target.lean` is already on main. [Run]({RUN_URL})"])

    def test_duplicate_found_after_merge_attempt_closes_once(self):
        self.run_verdict("duplicate")
        self.run_verdict("duplicate")
        self.assert_closed_duplicate()
        self.assertEqual(sum(call[:3] == ["api", "-X", "PATCH"] for call in self.calls), 1)

    def test_duplicate_on_fetched_main_skips_merge(self):
        self.run_verdict("local-duplicate")
        self.assert_closed_duplicate()
        self.assertFalse(any(call[:3] == ["api", "-X", "PUT"] for call in self.calls))

    def test_success_reports_merge_after_credit_even_on_retry(self):
        self.run_verdict("success", remerge=1)
        self.assertEqual(len(self.comments), 1)
        self.assertIn("Merged.", self.comments[0])
        self.assertEqual(self.calls[-2], ["credit", "42"])

    def test_success_with_credit_failure_links_to_profile_without_claiming_credit(self):
        self.run_verdict("credit-failed")
        self.assertEqual(len(self.comments), 1)
        self.assertIn("Merged.", self.comments[0])
        self.assertIn("track credit on [Left to Solve](https://lefttosolve.test/a/solver)", self.comments[0])
        self.assertNotIn("credited", self.comments[0])
        self.assertFalse((self.work / "remerge.flag").exists())

    def test_shorter_proof_is_merged_as_a_replacement(self):
        self.run_verdict("shorter")
        self.assertFalse((self.work / "closed").exists())
        self.assertIn(["credit", "42"], self.calls)
        self.assertEqual(len(self.comments), 1)
        self.assertIn("Merged as the shortest proof.", self.comments[0])

    def test_graphql_fallback_confirms_the_merge(self):
        self.run_verdict("graphql-merged")
        self.assertIn(["credit", "42"], self.calls)
        self.assertEqual(len(self.comments), 1)
        self.assertIn("Merged.", self.comments[0])

    def test_graphql_fallback_without_a_confirmed_merge_retries(self):
        self.run_verdict("graphql-pending")
        self.assertEqual((self.work / "credit-retry").read_text(), "42\n")
        self.assertFalse((self.work / "closed").exists())
        self.assertTrue((self.work / "remerge.flag").exists())
        self.assertNotIn(["credit", "42"], self.calls)
        self.assertEqual(len(self.comments), 1)
        self.assertNotIn("Merged", self.comments[0])

    def test_refused_merge_queues_retry_without_claiming_a_merge(self):
        self.run_verdict("merge-false")
        self.assertTrue((self.work / "remerge.flag").exists())
        self.assertNotIn(["credit", "42"], self.calls)
        self.assertEqual(len(self.comments), 1)
        self.assertIn("GitHub has yet to finish merging this pull request", self.comments[0])
        self.assertNotIn("Merged", self.comments[0])

    def test_changed_head_is_left_for_the_new_check(self):
        self.run_verdict("new-head")
        self.assertFalse((self.work / "closed").exists())
        self.assertFalse((self.work / "remerge.flag").exists())
        self.assertEqual(self.comments, [])

    def test_refused_close_queues_retry_and_reports_duplicate(self):
        self.run_verdict("close-failed")
        self.assertFalse((self.work / "closed").exists())
        self.assertTrue((self.work / "remerge.flag").exists())
        self.assertEqual(len(self.comments), 1)
        self.assertIn("GitHub has yet to finish closing this duplicate", self.comments[0])


if __name__ == "__main__":
    unittest.main()
