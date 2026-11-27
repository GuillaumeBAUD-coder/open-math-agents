#!/usr/bin/env python3
"""Classifies a pull request from its list of changed files (JSON list of {filename, status} on stdin).
A submission is exactly one new file proofs/<id>.lean, or new files under one directory evidence/<id>/ among
run.py, claim.json, review.md, README.md. <id> must be a problem of data/catalogue.json.
Prints JSON {ok, kind: lean|compute|review, id, files, reason}."""
import json, re, sys
files = json.load(sys.stdin)
ids = {p["id"]: p for p in json.load(open("data/catalogue.json", encoding="utf-8"))["problems"]}
def out(**k): print(json.dumps(k)); sys.exit(0)
added = [f["filename"] for f in files if f.get("status") == "added"]
if len(added) != len(files): out(ok=False, reason="only new files are accepted (nothing modified, renamed or deleted)")
if len(added) == 1 and re.fullmatch(r"proofs/[A-Za-z0-9_.\-]+\.lean", added[0]):
    pid = added[0][len("proofs/"):-len(".lean")]
    if pid not in ids: out(ok=False, reason=f"no problem with id {pid}")
    out(ok=True, kind="lean", id=pid, files=added, track=ids[pid]["track"])
m = {re.match(r"evidence/([A-Za-z0-9_.\-]+)/", f).group(1) if re.match(r"evidence/([A-Za-z0-9_.\-]+)/", f) else None for f in added}
if len(m) == 1 and None not in m:
    pid = m.pop()
    names = {f.split("/", 2)[2] for f in added}
    if not names <= {"run.py", "claim.json", "review.md", "README.md"}: out(ok=False, reason="evidence/<id>/ may only hold run.py, claim.json, review.md, README.md")
    if pid not in ids: out(ok=False, reason=f"no problem with id {pid}")
    if {"run.py", "claim.json"} <= names: out(ok=True, kind="compute", id=pid, files=added, track=ids[pid]["track"])
    if "review.md" in names and "run.py" not in names: out(ok=True, kind="review", id=pid, files=added, track=ids[pid]["track"])
    out(ok=False, reason="a computation needs run.py and claim.json; a review needs review.md")
out(ok=False, reason="a submission is one new proofs/<id>.lean or one new evidence/<id>/ directory")
