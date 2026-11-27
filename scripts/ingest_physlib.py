#!/usr/bin/env python3
"""Lean-track targets from Physlib (Apache-2.0, https://github.com/leanprover-community/physlib):
 - informal_lemma / informal_definition blocks: results Physlib states in prose and has not formalised or proved yet;
 - TODO notes that ask for a mathematical result (prove / show / derive / state and prove / generalize the statement).
Refactors, renames and file moves are left out. Output: data/src_physlib.json.
Usage: python3 -I scripts/ingest_physlib.py <physlib checkout> <commit>"""
import json, os, re, sys

root, commit = sys.argv[1], sys.argv[2]
MATH = re.compile(r"(?i)^\s*(prove|show|derive|state and prove|generali[sz]e the (statement|theorem|result|lemma)|find (the|a|an)|compute|establish|verify that|deduce)\b")
SKIP = re.compile(r"(?i)\b(refactor|rename|move |file|namespace|docstring|lint|simp lemma|golf|clean up|deprecat)")
rows = []
def field_of(path):
    parts = path.split("/")
    return (parts[1] if len(parts) > 2 else parts[0]).replace("And", " & ")
for dp, _, fs in os.walk(root):
    if "/.lake" in dp or "/.git" in dp: continue
    for f in fs:
        if not f.endswith(".lean"): continue
        path = os.path.join(dp, f); rel = os.path.relpath(path, root)
        if not rel.startswith(("Physlib/", "PhyslibAlpha/", "QuantumInfo/")): continue
        src = open(path, encoding="utf-8").read()
        module = rel[:-5].replace("/", ".")
        url = f"https://github.com/leanprover-community/physlib/blob/{commit}/{rel}"
        for m in re.finditer(r"(/--(?P<doc>(?:(?!-/).)*)-/\s*)?informal_(?P<kind>lemma|definition)\s+(?P<name>[^\s]+)\s+where(?P<body>.*?)(?=\n\S|\Z)", src, re.S):
            doc = re.sub(r"\s+", " ", (m.group("doc") or "")).strip()
            tag = re.search(r'tag\s*:=\s*"([^"]+)"', m.group("body") or "")
            if len(doc) < 30: continue
            line = src[:m.start()].count("\n") + 1
            name = m.group("name")
            rows.append({"id": "physlib-" + re.sub(r"[^A-Za-z0-9_.-]+", "-", (tag.group(1) if tag else module + "." + name))[:90],
                         "title": f"{name.split('.')[-1].replace('_', ' ')} ({module.split('.')[-1]})", "track": "lean",
                         "kind": "informal_" + m.group("kind"), "field": field_of(rel), "statement": doc,
                         "module": module, "decl": name, "ref": f"{url}#L{line}",
                         "source": "Physlib (informal results)", "license": "Apache-2.0 (Physlib contributors)", "fame": 60})
        for m in re.finditer(r'TODO\s+"((?:[^"\\]|\\.)*)"', src):
            text = re.sub(r"\s+", " ", m.group(1)).strip()
            if not MATH.search(text) or SKIP.search(text) or len(text) < 25: continue
            line = src[:m.start()].count("\n") + 1
            rows.append({"id": f"physlib-todo-{module}-L{line}".replace("/", "-")[:100], "title": text[:90].rstrip(" .") + ("…" if len(text) > 90 else ""),
                         "track": "lean", "kind": "todo", "field": field_of(rel), "statement": text, "module": module,
                         "ref": f"{url}#L{line}", "source": "Physlib (TODO list)", "license": "Apache-2.0 (Physlib contributors)", "fame": 50})
seen = set(); out = []
for r in rows:
    if r["id"] in seen: continue
    seen.add(r["id"]); out.append(r)
json.dump(out, open("data/src_physlib.json", "w", encoding="utf-8"), ensure_ascii=False, indent=0)
print(len(out), "targets:", sum(1 for r in out if r["kind"] != "todo"), "informal results,", sum(1 for r in out if r["kind"] == "todo"), "TODOs")
