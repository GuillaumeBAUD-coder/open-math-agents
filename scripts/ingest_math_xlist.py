#!/usr/bin/env python3
"""Problems of physics that the maths catalogue (Left to Solve, open-math-agents) already lists: formal-conjectures entries
in quantum theory, mechanics and fluids (Open Quantum Problems, Navier–Stokes, Yang–Mills...), and arXiv abstracts whose
field is physics. They are listed here as open questions with a link to their page there, where they can be proved
in Lean against Mathlib. Statements: formal-conjectures (Apache-2.0), arXiv metadata (CC0).
Usage: python3 -I scripts/ingest_math_xlist.py <open-math-agents checkout>  ->  data/src_mathxlist.json"""
import json, os, sys
ROOT = sys.argv[1]
PF = {"Quantum Theory": "Quantum physics", "Mechanics": "Classical physics", "Optics": "Optics", "Statistical Mechanics": "Statistical physics",
      "Relativity": "Gravitation & cosmology", "Fluid Mechanics": "Fluid dynamics", "Thermodynamics": "Statistical physics"}
def fields(v): return v if isinstance(v, list) else json.loads(v.replace("'", '"')) if v.startswith("[") else [v]
rows = []
for p in json.load(open(os.path.join(ROOT, "data/catalog.json"), encoding="utf-8"))["problems"]:
    fs = fields(p["fields"]); hit = [PF[f] for f in fs if f in PF]
    special = p["id"].startswith(("NavierStokes", "OpenQuantumProblem"))
    if not hit and not special: continue
    if p.get("kind") not in ("open", None): continue
    field = hit[0] if hit else ("Fluid dynamics" if p["id"].startswith("NavierStokes") else "Quantum physics")
    rows.append({"id": "lts-" + p["id"], "title": p["title"][:200], "track": "open", "field": field, "statement": p.get("statement", "")[:1500],
                 "source": "Left to Solve (formal-conjectures)", "ref": f"https://lefttosolve.com/p/{p['id']}",
                 "note": "Stated in Lean (Mathlib) in google-deepmind/formal-conjectures; prove it on Left to Solve.",
                 "license": "Apache-2.0 (formal-conjectures)", "fame": 40 + min(40, int(p.get("difficulty", 50) or 50) // 2)})
e2 = json.load(open(os.path.join(ROOT, "data/extra2.json"), encoding="utf-8"))
for r in e2["rows"]:
    pid, title, _src, fs, stmt, ref = r[:6]
    hit = [PF[f] for f in fs if f in PF]
    if not hit or pid.startswith(("oeis", "mo-", "mse")): continue
    rows.append({"id": pid if pid.startswith("arxiv-") else "lts-" + pid, "title": title[:200], "track": "open", "field": hit[0],
                 "statement": (stmt or "")[:1500], "source": "Left to Solve (curated)" if not pid.startswith("arxiv-") else "arXiv abstracts",
                 "ref": ref or f"https://lefttosolve.com/p/{pid}", "license": "see the source", "fame": 70 if pid.startswith("wpc-") else 25})
json.dump(rows, open("data/src_mathxlist.json", "w", encoding="utf-8"), ensure_ascii=False, indent=0)
print(json.dumps({"kept": len(rows)}))
