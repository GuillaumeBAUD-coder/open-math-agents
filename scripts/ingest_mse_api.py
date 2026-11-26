#!/usr/bin/env python3
"""Add hard open questions from Mathematics Stack Exchange to data/extra2.json.

Input: JSON pages from the Stack Exchange API, /questions/unanswered?site=math&sort=votes&filter=withbody (questions
with no upvoted answer), fetched in score slices because anonymous paging stops at page 25. An unanswered question is not
an open problem: most unanswered Math.SE questions are exercises nobody took up. So only questions that look like
research questions are kept: tagged open-problem / conjectures, or whose title asks an existence, classification,
"is it true", "infinitely many" or asymptotic question, and not an exercise ("evaluate", "how to prove", "proof of").
Also: score >= MIN_SCORE, not closed, no accepted answer, outside soft tags (reference requests, proof checks, software). The question text is shown with its author and link: CC BY-SA (4.0 after 2018-05-02, 3.0 before).

Usage: python3 -I scripts/ingest_mse_api.py <dir of API pages>... [--min-score 5]
"""
import glob, html, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
EXTRA2 = os.path.join(HERE, "..", "data", "extra2.json")
args = [a for a in sys.argv[1:] if not a.startswith("--")]
MIN_SCORE = int(sys.argv[sys.argv.index("--min-score") + 1]) if "--min-score" in sys.argv else 5
if "--min-score" in sys.argv: args.remove(str(MIN_SCORE))
SRC = "Mathematics Stack Exchange (not formalized)"
LICENSE = "Question text by its Mathematics Stack Exchange author, CC BY-SA (4.0 after 2018-05-02, 3.0 before); see the link"

BAD_TAGS = {"soft-question", "reference-request", "big-list", "career", "advice", "education", "learning", "self-learning",
            "book-recommendation", "online-resources", "math-history", "terminology", "notation", "definition", "intuition",
            "proof-verification", "solution-verification", "proof-writing", "proof-explanation", "alternative-proof",
            "homework", "math-software", "mathematica", "wolfram-alpha", "python", "programming", "matlab", "maple",
            "sagemath", "latex", "calculator", "puzzle", "recreational-mathematics", "gre-exam", "contest-math-history",
            "philosophy", "meta-math", "fake-proofs", "visualization", "graphing-functions", "word-problem", "mathematical-physics-history"}
BAD_TITLE = re.compile(r"(?i)\b(reference|references|book|textbook|lecture notes|survey|who (first|introduced|coined)|history of|origin of|name (for|of)|what is (this|the name)|terminology|notation|intuition|motivation|explain|explanation|understand|confus|is my proof|check my|verify my|proof check|proof verification|mistake in|error in|typo|homework|exercise|software|mathematica|wolfram|python|matlab|latex|how (to|do i|can i) (learn|study|read|start)|career|phd|advisor|recommend)\b")

FIELDS = [
    (("number-theory", "prime", "diophantine", "modular-forms", "riemann-zeta", "analytic-number-theory", "arithmetic"), "Number Theory"),
    (("combinatorics", "graph-theory", "ramsey", "permutations", "combinatorial", "extremal", "coloring", "integer-partitions", "discrete-mathematics"), "Combinatorics"),
    (("sequences-and-series", "summation", "power-series", "continued-fractions", "products"), "Sequences & Series"),
    (("integration", "definite-integrals", "improper-integrals", "measure-theory", "lebesgue", "closed-form"), "Measure & Integration"),
    (("special-functions", "gamma-function", "polylogarithm", "hypergeometric", "zeta-functions", "elliptic-integrals", "bessel"), "Special Functions"),
    (("probability", "stochastic", "random", "statistics", "martingales", "brownian", "markov"), "Probability"),
    (("group-theory", "finite-groups", "group-actions", "representation-theory", "lie-groups", "abstract-algebra"), "Group Theory"),
    (("ring-theory", "commutative-algebra", "field-theory", "galois", "polynomials", "algebraic-number-theory", "modules"), "Commutative Algebra"),
    (("linear-algebra", "matrices", "eigenvalues", "determinant", "matrix"), "Linear Algebra"),
    (("algebraic-geometry", "schemes", "algebraic-curves", "elliptic-curves"), "Algebraic Geometry"),
    (("general-topology", "algebraic-topology", "homotopy", "homology", "knot", "topology"), "General Topology"),
    (("differential-geometry", "riemannian", "manifolds", "smooth-manifolds", "symplectic"), "Manifolds"),
    (("geometry", "euclidean-geometry", "triangles", "polygons", "convex", "discrete-geometry", "packing", "tiling", "polyhedra"), "Geometry"),
    (("complex-analysis", "analytic", "holomorphic", "complex-numbers"), "Complex Analysis"),
    (("functional-analysis", "operator-theory", "banach", "hilbert", "c-star"), "Functional Analysis"),
    (("fourier", "harmonic-analysis"), "Harmonic Analysis"),
    (("ordinary-differential-equations", "partial-differential-equations", "pde", "differential-equations"), "PDEs"),
    (("dynamical-systems", "ergodic", "chaos", "fractals"), "Dynamical Systems"),
    (("logic", "set-theory", "model-theory", "computability", "first-order-logic", "ordinals", "cardinals", "axiom"), "Logic & Foundations"),
    (("category-theory", "homological-algebra"), "Category Theory"),
    (("algorithms", "computational-complexity", "computer-science", "automata", "formal-languages"), "Computer Science"),
    (("game-theory", "optimization", "economics"), "Game Theory & Economics"),
    (("real-analysis", "calculus", "inequality", "limits", "functions", "analysis", "convex-analysis"), "Real Functions"),
]

OPEN_TAGS = {"open-problem", "conjectures", "unsolved"}
OPEN_TITLE = re.compile(r"(?i)\b(conjecture|open problem|open question|unsolved|is it known|does there exist|do there exist|is there (a|an|any)\b|are there (infinitely|any)|is it true that|prove or disprove|counter-?example|infinitely many|asymptotic|characteriz|classif)")
EXERCISE = re.compile(r"(?i)\b(evaluate|compute|calculate|find the (value|sum|limit)|how (to|do i|can i|would i) (prove|show|solve|compute|evaluate|find)|help|exercise|proof of|elementary proof|combinatorial proof|alternative proof|simple proof|another proof|nice proof|slick proof|intuitive|explanation|textbook|book|why is|why does|what steps|known results)\b")

def looks_open(title, tags):
    return bool(set(tags) & OPEN_TAGS) or (bool(OPEN_TITLE.search(title)) and not EXERCISE.search(title))

def fields_for(tags):
    out = []
    for t in tags:
        for keys, f in FIELDS:
            if any(k in t for k in keys):
                if f not in out: out.append(f)
                break
    return out[:2] or ["Real Functions"]

def plain(body):
    s = re.sub(r"(?is)<pre[^>]*>.*?</pre>", " [code] ", body)
    s = re.sub(r"(?i)<br\s*/?>|</p>|</li>|</h\d>|</blockquote>", "\n", s)
    s = re.sub(r"(?i)<li[^>]*>", "• ", s)
    s = re.sub(r"<[^>]+>", "", s)
    s = html.unescape(s)
    s = re.sub(r"[ \t]+", " ", s)
    s = re.sub(r"\n\s*\n+", "\n\n", s).strip()
    if len(s) > 1200:
        cut = s.rfind(" ", 0, 1200)
        s = s[: cut if cut > 900 else 1200] + " …"
    return s

items = {}
for d in args:
    for f in sorted(glob.glob(os.path.join(d, "*.json"))):
        for q in json.load(open(f, encoding="utf-8")).get("items", []):
            items[q["question_id"]] = q

kept, drop = {}, {"score": 0, "closed": 0, "accepted": 0, "tags": 0, "title": 0, "not_open": 0, "short": 0}
for qid, q in items.items():
    tags = q.get("tags", [])
    title = html.unescape(q.get("title", "")).strip()
    if q.get("score", 0) < MIN_SCORE: drop["score"] += 1; continue
    if q.get("closed_date") or q.get("closed_reason"): drop["closed"] += 1; continue
    if q.get("accepted_answer_id"): drop["accepted"] += 1; continue
    if set(tags) & BAD_TAGS: drop["tags"] += 1; continue
    if BAD_TITLE.search(title): drop["title"] += 1; continue
    if not looks_open(title, tags): drop["not_open"] += 1; continue
    text = plain(q.get("body", ""))
    if len(text) < 40: drop["short"] += 1; continue
    score = q["score"]
    kept[f"mse-{qid}"] = [f"mse-{qid}", title[:200], None, fields_for(tags), text, q.get("link") or f"https://math.stackexchange.com/questions/{qid}",
                          [html.unescape(q["owner"]["display_name"])] if q.get("owner", {}).get("display_name") else [],
                          20 + min(32, score // 3), 50 + min(18, score // 12), tags[:5], ", ".join(tags[:4]), q.get("answer_count", 0)]

d = json.load(open(EXTRA2, encoding="utf-8"))
si = d["sources"].index(SRC)
d["licenses"][SRC] = LICENSE
# Already elsewhere in the catalogue (core problems, extra.json, MathOverflow rows) is skipped by build_data.mjs's dedupe;
# here: replace earlier title-only Math.SE rows by the richer ones, add the rest.
before = {r[0]: i for i, r in enumerate(d["rows"])}
replaced = added = 0
for rid, row in kept.items():
    row[2] = si
    if rid in before:
        old = d["rows"][before[rid]]
        if old[2] == si: d["rows"][before[rid]] = row; replaced += 1
    else:
        d["rows"].append(row); added += 1
d["meta"]["counts"][SRC] = sum(1 for r in d["rows"] if r[2] == si)
d["meta"]["total"] = len(d["rows"])
d["meta"]["mseApi"] = {"minScore": MIN_SCORE, "fetched": len(items), "kept": len(kept), "dropped": drop}
json.dump(d, open(EXTRA2, "w", encoding="utf-8"), ensure_ascii=False, separators=(",", ":"))
print(json.dumps({"fetched": len(items), "kept": len(kept), "added": added, "replaced": replaced, "dropped": drop, "total": len(d["rows"])}))
