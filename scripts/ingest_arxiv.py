#!/usr/bin/env python3
"""Open questions stated in arXiv physics abstracts (metadata CC0; the question is the authors', see the paper).
Strict, as for the maths catalogue: the abstract must state something as open in the authors' own words; dropped when
the paper itself then answers it ("remains open ... here we show"), when the sentence only announces open questions
without stating them, when it is vague (no specific object), and before 2018. Output: data/src_arxiv.json.
Usage: python3 -I scripts/ingest_arxiv.py <raw.jsonl>"""
import json, re, sys

FIELD = {"hep-th": "High-energy theory", "hep-ph": "Particle physics", "hep-lat": "Lattice QFT", "gr-qc": "Gravitation & cosmology",
         "astro-ph.CO": "Cosmology", "astro-ph.HE": "High-energy astrophysics", "quant-ph": "Quantum physics", "math-ph": "Mathematical physics",
         "nucl-th": "Nuclear physics", "nlin.CD": "Chaos & nonlinear dynamics", "physics.flu-dyn": "Fluid dynamics",
         "physics.class-ph": "Classical physics", "physics.atom-ph": "Atomic physics", "physics.optics": "Optics", "physics.plasm-ph": "Plasma physics"}
POSE = re.compile(r"(?i)\b(we (also |further |now )?conjecture|we (pose|formulate|propose|state) (a |an |the |two |several )?(conjecture|question|problem|open problem)|we ask whether|remains? (an )?open( (problem|question))?|remain open|(is|are) still open|left open|(it is|is) (still |currently )?(an )?open (problem|question)|(it is|is) (still |currently )?(unknown|not known|unclear) (whether|if|how|why)|remains? (unknown|unclear|a (long-?standing )?(puzzle|mystery))|long-?standing (puzzle|open (problem|question)|problem)|(is|remains) (still )?unresolved|unresolved (problem|question|puzzle))\b")
OWN = re.compile(r"(?i)\b(we (also |further |now )?conjecture|we (pose|formulate|propose|state) (a |an |the |two |several )?(conjecture|question|problem|open problem)|we ask whether)\b")
LATER_WIN = re.compile(r"(?i)\b(in this (paper|letter|note|article|work)|here|we)\b[^.]{0,50}\b(prove|show|demonstrate|establish|resolve|answer|settle|solve|explain|clarify|address|elucidate|identify|uncover|reveal|determine|find|propose a (solution|resolution|mechanism|explanation))\b")
SETTLE = re.compile(r"(?i)\b(resolve[sd]?|resolving|settle[sd]?|answer(s|ed|ing)?|solve[sd]?|solution (to|of)|explain(s|ed|ing)?|resolution of|clarif(y|ies|ied))\b[^.]{0,80}\b(puzzle|problem|question|mystery|conjecture|tension|anomaly)\b")
EMPTY = re.compile(r"(?i)\b(some|several|a few|a number of|various|many|other|further) (\w+ )?(open )?(questions|problems|issues)\b[^.]{0,30}\b(remain|are (still )?open|are discussed|are outlined)|\bopen (questions|problems|issues) (are|is) (also )?(discussed|mentioned|listed|presented|outlined|highlighted)\b|\b(discuss|outline|highlight|list|mention|present|conclude with|end with)\b[^.]{0,30}\bopen (questions|problems|issues)\b(?![^.]{0,10}(:|whether))|\b(further|future|its|their|the) (\w+ ){0,3}(development|developments|investigation|study|studies|work|exploration|implications|applications|consequences|extensions?)\b[^.]{0,20}\bremains? open\b|\bpreviously (proposed|conjectured|suggested)\b[^.]{0,60}\bremains? (an )?open\b")
VAGUE = re.compile(r"(?i)\b(remains? (unclear|unknown))\b")
COND = re.compile(r"(?i)\b(if|unless|as long as|whenever|provided)\b[^.]{0,80}\b(remains?|is) (still )?(unknown|unclear|open|unresolved)\b")
TOPO = re.compile(r"(?i)\bopen (and|dense|set|subset|map|cover|ball|neighbou?rhood|disc|disk|system|systems|quantum system|boundary|boundaries|string|strings|channel|chain|chains|cluster|shell|circuit|orbit|orbits|cavity|ended)\b|\bopen in\b")
SENT = re.compile(r"(?<=[.!?])\s+(?=[A-Z$\\(])")
def norm(s): return re.sub(r"[^a-z0-9]+", " ", s.lower()).strip()

rows, drop, seen_t = [], {}, set()
def d(k): drop[k] = drop.get(k, 0) + 1
for line in open(sys.argv[1], encoding="utf-8"):
    r = json.loads(line)
    prim = r.get("primary") or ""
    field = FIELD.get(prim) or ("Condensed matter" if prim.startswith("cond-mat") else None)
    if not field: d("other_primary"); continue
    if int(r["published"][:4]) < 2018: d("before_2018"); continue
    s = r["summary"]; sents = [x.strip() for x in SENT.split(s) if x.strip()]
    posing = [x for x in sents if POSE.search(x) and not TOPO.search(x) and not SETTLE.search(x) and not COND.search(x)]
    if not posing: d("no_open_statement"); continue
    posing = [x for x in posing if not EMPTY.search(x) and len(x) >= 60 and (not VAGUE.search(x) or "$" in x or len(x) >= 110)]
    if not posing: d("no_stated_content"); continue
    first = sents.index(posing[0])
    if not OWN.search(" ".join(posing)) and any(LATER_WIN.search(x) for x in sents[first + 1:]): d("answered_in_paper"); continue
    if SETTLE.search(s) and not OWN.search(" ".join(posing)): d("settled_in_paper"); continue
    t = norm(r["title"])
    if t in seen_t: d("duplicate"); continue
    seen_t.add(t)
    head = " ".join(posing[:2])
    statement = head + ("\n\n" + s if len(s) > len(head) + 20 else "")
    if len(statement) > 1500: statement = statement[:1450].rsplit(" ", 1)[0] + " …"
    year = int(r["published"][:4])
    rows.append({"id": "arxiv-" + r["id"].replace("/", "_"), "title": r["title"][:200], "track": "open", "field": field, "statement": statement,
                 "source": "arXiv abstracts", "ref": f"https://arxiv.org/abs/{r['id']}", "authors": r.get("authors", [])[:6],
                 "note": f"Open as stated in arXiv {r['id']} ({r['published']}); not re-checked against later work.",
                 "license": "Abstract metadata from arXiv (CC0); the question is the authors', see the paper", "fame": 20 + max(0, min(10, year - 2016)), "year": year})
json.dump(rows, open("data/src_arxiv.json", "w", encoding="utf-8"), ensure_ascii=False, indent=0)
print(json.dumps({"kept": len(rows), "dropped": drop}))
