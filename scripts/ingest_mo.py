#!/usr/bin/env python3
"""Open questions of mathematical physics from MathOverflow (questions without an accepted answer, from the
MathOverflow data dump already filtered for the maths catalogue: data/extra3.json.gz of open-math-agents).
Kept: questions tagged with a physics tag (mathematical physics, quantum mechanics and field theory, general
relativity, statistical physics, fluid dynamics, classical mechanics, integrable systems, string theory...).
Question text CC BY-SA by its author (4.0 after 2018-05-02, 3.0 before); every entry links to it.
Usage: python3 -I scripts/ingest_mo.py <open-math-agents>/data/extra3.json.gz  ->  data/src_mo.json"""
import gzip, json, sys
TAGS = {
    "mp.mathematical-physics": "Mathematical physics", "quantum-field-theory": "High-energy theory", "conformal-field-theory": "High-energy theory",
    "topological-quantum-field-theory": "High-energy theory", "extended-tqft": "High-energy theory", "string-theory": "High-energy theory",
    "gauge-theory": "High-energy theory", "quantum-mechanics": "Quantum physics", "quantum-computation": "Quantum physics",
    "general-relativity": "Gravitation & cosmology", "special-relativity": "Gravitation & cosmology", "statistical-physics": "Statistical physics",
    "fluid-dynamics": "Fluid dynamics", "classical-mechanics": "Classical physics", "hamiltonian-mechanics": "Classical physics",
    "integrable-systems": "Mathematical physics", "physics": "Mathematical physics", "condensed-matter": "Condensed matter",
}
PRIORITY = ["general-relativity", "fluid-dynamics", "statistical-physics", "quantum-field-theory", "conformal-field-theory", "string-theory",
            "gauge-theory", "topological-quantum-field-theory", "quantum-mechanics", "quantum-computation", "classical-mechanics",
            "hamiltonian-mechanics", "condensed-matter", "integrable-systems", "special-relativity", "extended-tqft", "physics", "mp.mathematical-physics"]
d = json.load(gzip.open(sys.argv[1], "rt", encoding="utf-8"))
rows = []
for r in d["rows"]:
    qid, title, _fields, tags, score, views, _ans, date, author, body = r[:10]
    hit = [t for t in PRIORITY if t in tags]
    if not hit: continue
    stmt = body if len(body) <= 1500 else body[:1450].rsplit(" ", 1)[0] + " …"
    rows.append({"id": f"mo-{qid}", "title": title[:200], "track": "open", "field": TAGS[hit[0]], "statement": stmt,
                 "source": "MathOverflow (mathematical physics)", "ref": f"https://mathoverflow.net/questions/{qid}",
                 "authors": [author] if author else [], "tags": tags[:6],
                 "note": f"Open question asked on MathOverflow ({date}, score {score}); no accepted answer in the 2026-09-30 data dump.",
                 "license": "Question text by its MathOverflow author, CC BY-SA (4.0 after 2018-05-02, 3.0 before)", "fame": 18 + min(30, int(score) // 3)})
json.dump(rows, open("data/src_mo.json", "w", encoding="utf-8"), ensure_ascii=False, indent=0)
print(json.dumps({"kept": len(rows)}))
