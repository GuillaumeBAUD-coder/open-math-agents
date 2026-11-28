#!/usr/bin/env python3
"""Refresh the erdosproblems.com status of every Erdős problem in data/catalog.json.

erdosproblems.com (github.com/teorth/erdosproblems, data/problems.yaml) is the curated record of which Erdős problems
are proved, disproved or solved. The catalogue keeps that status in `erdosState`; scripts/build_data.mjs then treats an
open problem whose main problem is settled upstream as a known result (unless it was proved here: a proof in proofs/).
Run daily by .github/workflows/status-sync.yml; prints what changed and exits 0 with no change when nothing moved.

Usage: python3 -I scripts/sync_erdos_status.py [path/to/problems.yaml]   (default: downloads the upstream file)
"""
import json
import os
import re
import sys
import urllib.request

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
CATALOG = os.path.join(ROOT, "data", "catalog.json")
UPSTREAM = "https://raw.githubusercontent.com/teorth/erdosproblems/main/data/problems.yaml"


def parse(text: str) -> dict[int, dict]:
    """The few fields we need from problems.yaml (a regular list of mappings; no YAML library needed)."""
    out: dict[int, dict] = {}
    cur: dict | None = None
    block = None
    for line in text.splitlines():
        m = re.match(r'^- number:\s*"?(\d+)"?\s*$', line)
        if m:
            cur = {"number": int(m.group(1))}
            out[cur["number"]] = cur
            block = None
            continue
        if cur is None:
            continue
        m = re.match(r"^  (\w+):\s*(.*)$", line)
        if m:
            block = m.group(1)
            continue
        m = re.match(r'^    (\w+):\s*"?([^"]*)"?\s*$', line)
        if m and block == "status" and m.group(1) == "state":
            cur["state"] = m.group(2).strip()
        elif m and block == "forum" and m.group(1) == "posts":
            cur["posts"] = int(m.group(2) or 0)
    return out


def main() -> int:
    if len(sys.argv) > 1:
        text = open(sys.argv[1], encoding="utf-8").read()
    else:
        with urllib.request.urlopen(UPSTREAM, timeout=60) as r:
            text = r.read().decode("utf-8")
    up = parse(text)
    if len(up) < 1000:  # a truncated or changed file: never rewrite the catalogue from it
        print(f"sync_erdos_status: only {len(up)} problems parsed upstream, nothing changed")
        return 0
    raw = open(CATALOG, encoding="utf-8").read()
    cat = json.loads(raw)
    changes = []
    for p in cat["problems"]:
        n = p.get("erdos")
        if not n or n not in up or "state" not in up[n]:
            continue
        new_state = up[n]["state"]
        if new_state and new_state != p.get("erdosState"):
            changes.append(f"{p['id']}: {p.get('erdosState')} -> {new_state}")
            p["erdosState"] = new_state
        posts = up[n].get("posts")
        if posts is not None and posts != p.get("forumPosts"):
            p["forumPosts"] = posts
    out = json.dumps(cat, ensure_ascii=False, separators=(",", ":"))
    if out != raw:
        with open(CATALOG, "w", encoding="utf-8") as f:
            f.write(out)
    print(f"sync_erdos_status: {len(changes)} status changes")
    for c in changes[:200]:
        print("  " + c)
    return 0


if __name__ == "__main__":
    sys.exit(main())
