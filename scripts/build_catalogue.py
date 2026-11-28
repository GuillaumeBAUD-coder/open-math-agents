#!/usr/bin/env python3
"""Merges data/src_*.json into data/catalogue.json and writes data/seed.sql (the desk's problems table).
Tracks: lean (formalise and prove against Physlib; statements are reviewed by a person), open (an open question of
physics: a proof here settles it only if it can be stated formally; computations and literature work count as
evidence, never as a solution), compute (reproducible computations; none sourced yet).

Every problem also gets a verification contract `verify` (how a contribution to it can be checked) and `verify_note`
(one sentence: what a checkable deliverable would be, or why there is none):
  lean          a precise mathematical statement, checked by Lean against Mathlib/Physlib (and a person for the statement)
  certified     a precise computational question, checked exactly or with rigorous bounds by a small trusted checker
  reproducible  a computation or simulation, checked by re-running it and comparing within a tolerance
  review        a theoretical argument, checked only by careful reading (independent reviewers and a person)
  none          not a well-posed question that any deliverable could settle: not offered by the desk
Deterministic rules cover the sources where they are reliable (Physlib, formal-conjectures). Everything else (the
arXiv harvest, MathOverflow, Wikipedia's list) was judged statement by statement into data/verify.json, which also
overrides the rules. The build fails if any problem is left without a contract."""
import json, glob, sys
rows, seen = [], set()
for f in sorted(glob.glob("data/src_*.json")):
    for r in json.load(open(f, encoding="utf-8")):
        if r["id"] in seen: continue
        seen.add(r["id"]); rows.append(r)
# One vocabulary of fields across sources (Physlib module names, arXiv categories, MathOverflow tags).
FIELD_NAMES = {"ClassicalMechanics": "Classical physics", "QuantumMechanics": "Quantum physics", "QFT": "High-energy theory",
               "Particles": "Particle physics", "Relativity": "Gravitation & cosmology", "Cosmology & GR": "Gravitation & cosmology",
               "Space & Time": "Gravitation & cosmology", "Cosmology": "Gravitation & cosmology", "States": "Quantum information",
               "Capacity": "Quantum information", "ClassicalInfo": "Quantum information", "Meta": "Mathematical physics",
               "High-energy astrophysics": "Astrophysics", "General": "Foundations", "Lattice QFT": "High-energy theory"}
for r in rows: r["field"] = FIELD_NAMES.get(r["field"], r["field"])

# ---------- verification contracts ----------
VERIFY = ("lean", "certified", "reproducible", "review", "none")
def rule(r):
    """Deterministic contracts, only where the source makes them reliable. Returns (verify, note) or None."""
    if r["source"].startswith("Physlib"):
        mod, decl = r.get("module", ""), r.get("decl")
        if mod.startswith("Physlib.Meta."):  # tooling TODOs (tactics, linters): software work inside Physlib, not physics
            return "none", "A maintenance task in Physlib's own tooling, not a mathematical statement; it can only be fixed in Physlib itself, where AI-written pull requests are not accepted."
        if r.get("kind") == "informal_definition":
            return "lean", f"A Lean 4 definition of `{decl}` against the pinned Physlib matching the informal one in `{mod}`, with lemmas showing it behaves as stated; it must compile with audited axioms, and a person checks it is the intended definition."
        if r.get("kind") == "informal_lemma":
            return "lean", f"A Lean 4 proof of `{decl}` (stated informally in `{mod}`) against the pinned Physlib; the checker compiles it and audits its axioms, and a person checks the formal statement says what the informal one says."
        return "lean", f"A Lean 4 file proving this item of `{mod}` against the pinned Physlib; the checker compiles it and audits its axioms, and a person checks the formal statement says what the TODO asks."
    if r["source"] == "Left to Solve (formal-conjectures)":
        return "lean", "A Lean 4 proof (or disproof) of the statement already formalised against Mathlib in google-deepmind/formal-conjectures; compiling with no sorry and only the standard axioms settles it."
    return None
judged = json.load(open("data/verify.json", encoding="utf-8"))
missing = []
for r in rows:
    v = judged.get(r["id"])
    if not v and rule(r): v = dict(zip(("verify", "verify_note"), rule(r)))
    if not v: missing.append(r["id"]); continue
    assert v["verify"] in VERIFY and v["verify_note"].strip(), r["id"]
    r["verify"], r["verify_note"] = v["verify"], v["verify_note"]
if missing:
    sys.exit(f"{len(missing)} problems have no verification contract (add them to data/verify.json): {missing[:10]}")
stale = set(judged) - seen
if stale: print(f"warning: {len(stale)} ids in data/verify.json are not in the catalogue", file=sys.stderr)

order = {"lean": 0, "open": 1, "compute": 2}
vorder = {v: i for i, v in enumerate(VERIFY)}
rows.sort(key=lambda r: (order.get(r["track"], 9), vorder[r["verify"]], -r.get("fame", 0), r["id"]))
sources = sorted({r["source"] for r in rows})
meta = {"total": len(rows), "tracks": {t: sum(1 for r in rows if r["track"] == t) for t in order},
        "verify": {v: sum(1 for r in rows if r["verify"] == v) for v in VERIFY},
        "verify_by_source": {s: {v: sum(1 for r in rows if r["source"] == s and r["verify"] == v) for v in VERIFY} for s in sources},
        "sources": sources,
        "fields": sorted({r["field"] for r in rows})}
json.dump({"meta": meta, "problems": rows}, open("data/catalogue.json", "w", encoding="utf-8"), ensure_ascii=False, separators=(",", ":"))
q = lambda s: "'" + str(s).replace("'", "''") + "'"
with open("data/seed.sql", "w", encoding="utf-8") as out:
    # The problems table only mirrors the catalogue, so it is rebuilt from scratch (this also adds the verify column to
    # an existing database; leases, events and results are untouched).
    out.write("drop table if exists problems;\n")
    out.write("create table problems (id text primary key, track text not null, field text, title text not null, verify text not null default 'review');\n")
    out.write("create index if not exists problems_track on problems (track, verify);\n")
    for i in range(0, len(rows), 200):
        chunk = rows[i:i + 200]
        out.write("insert into problems (id, track, field, title, verify) values " + ",".join(f"({q(r['id'])},{q(r['track'])},{q(r['field'])},{q(r['title'][:200])},{q(r['verify'])})" for r in chunk) + ";\n")
    out.write(f"insert or replace into meta (k, v) values ('catalogue', {q(json.dumps(meta['tracks']))});\n")
    out.write(f"insert or replace into meta (k, v) values ('verify', {q(json.dumps(meta['verify']))});\n")
print(json.dumps(meta["tracks"]), json.dumps(meta["verify"]), "total", len(rows))
