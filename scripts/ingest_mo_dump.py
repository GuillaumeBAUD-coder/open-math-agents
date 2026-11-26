#!/usr/bin/env python3
"""Build data/extra3.json.gz: open research questions from the MathOverflow data dump.

Kept: questions not closed, without an accepted answer, and either score >= 3 with no answer scoring 3 or more, or
score 2 with no answer scoring 2 or more (the community has not found a good answer); outside soft tags (reference requests, history, terminology, careers, big lists...).
`status.json` (optional) holds a fresh check through the Stack Exchange API: questions accepted, closed or deleted
since the dump are dropped. Question text: CC BY-SA (4.0 for posts after 2018-05-02, 3.0 before), author credited,
link kept.

Usage: python3 -I scripts/ingest_mo_dump.py <Posts.xml> <Users.xml> [status.json] [out]
"""
import gzip
import html
import json
import os
import re
import sys
import xml.etree.ElementTree as ET
from collections import defaultdict

POSTS, USERS = sys.argv[1], sys.argv[2]
STATUS = json.load(open(sys.argv[3])) if len(sys.argv) > 3 and sys.argv[3] != "-" else None
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = sys.argv[4] if len(sys.argv) > 4 else os.path.join(HERE, "..", "data", "extra3.json.gz")

BAD_TAGS = {"soft-question", "reference-request", "big-list", "career", "teaching", "terminology", "mathematics-education",
            "history-overview", "ho.history-overview", "advice", "books", "journals", "publishing", "examples", "intuition",
            "motivation", "definitions", "notation", "software", "computer-algebra", "latex", "tag-removed", "big-picture",
            "gm.general-mathematics", "recreational-mathematics"}
BAD_TITLE = re.compile(r"(?i)\b(reference|references|literature|book|survey|textbook|lecture notes|who (first|introduced|coined)|history of|origin of|name for|what is the name|terminology|notation|intuition|motivation|explanation|explain|understanding|why (is|do|does|are)|examples? of|list of|applications? of|is there a (book|text|reference)|career|phd|advisor|how to (learn|read|study|prove|compute|find|show)|soft question|homework|exercise|typo|error in|mistake in|proof check|check my|software|algorithm for computing|mathematica|sage|magma|latex)\b")

FIELD = [
    (("nt.", "number-theory", "analytic-number-theory", "prime-numbers", "diophantine"), "Number Theory"),
    (("ag.", "algebraic-geometry", "schemes", "moduli"), "Algebraic Geometry"),
    (("co.", "combinatorics", "graph-theory", "extremal", "ramsey", "partitions"), "Combinatorics"),
    (("gr.", "group-theory", "finite-groups", "geometric-group-theory"), "Group Theory"),
    (("at.", "gt.", "gn.", "homotopy", "topology", "knot"), "General Topology"),
    (("dg.", "sg.", "differential-geometry", "riemannian", "symplectic"), "Differential Geometry"),
    (("fa.", "oa.", "functional-analysis", "operator", "banach"), "Operator Theory"),
    (("ca.", "cv.", "real-analysis", "complex-analysis", "harmonic", "fourier"), "Harmonic Analysis"),
    (("pr.", "st.", "probability", "stochastic", "random"), "Probability"),
    (("lo.", "set-theory", "logic", "model-theory", "computability"), "Logic & Foundations"),
    (("ds.", "dynamical", "ergodic"), "Dynamical Systems"),
    (("cc.", "computational-complexity", "algorithms", "cs."), "Computational Complexity"),
    (("mg.", "metric-geometry", "convex", "discrete-geometry", "polytopes", "packing"), "Convex & Discrete Geometry"),
    (("ct.", "rt.", "ra.", "ac.", "qa.", "kt.", "category-theory", "representation-theory", "commutative-algebra",
      "linear-algebra", "lie-algebras", "rings", "algebra"), "General Algebra"),
    (("ap.", "pde", "differential-equations"), "Real Functions"),
]


def fields_for(tags):
    out = []
    for t in tags:
        for keys, f in FIELD:
            if any(t.startswith(k) if k.endswith(".") else k in t for k in keys):
                if f not in out:
                    out.append(f)
                break
    return out[:2] or ["Uncategorised"]


def plain(body):
    """HTML → plain text, keeping $…$ TeX, paragraphs and list items."""
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


names = {}
for _, el in ET.iterparse(USERS):
    if el.tag == "row":
        names[el.attrib.get("Id")] = el.attrib.get("DisplayName")
    el.clear()

questions, best_answer = {}, defaultdict(int)
for _, el in ET.iterparse(POSTS):
    if el.tag != "row":
        continue
    a = el.attrib
    if a.get("PostTypeId") == "1":
        questions[a["Id"]] = a.copy()
    elif a.get("PostTypeId") == "2":
        best_answer[a["ParentId"]] = max(best_answer[a["ParentId"]], int(a.get("Score", 0)))
    el.clear()

rows = []
for qid, a in questions.items():
    score = int(a.get("Score", 0))
    best = best_answer.get(qid, 0)
    if score < 2 or a.get("AcceptedAnswerId") or a.get("ClosedDate") or best >= 3 or (score == 2 and best >= 2):
        continue
    tags = [t for t in re.split(r"[<>|]", a.get("Tags", "")) if t]
    title = html.unescape(a.get("Title", "")).strip()
    if set(tags) & BAD_TAGS or BAD_TITLE.search(title):
        continue
    st = STATUS.get(qid) if STATUS is not None else None
    if STATUS is not None and (st is None or st["acc"] or st["closed"]):
        continue  # deleted, accepted or closed since the dump
    if st:
        score, views, answers = st["score"], st["views"], st["answers"]
        title = html.unescape(st["title"]).strip()
    else:
        views, answers = int(a.get("ViewCount", 0)), int(a.get("AnswerCount", 0))
    author = a.get("OwnerDisplayName") or names.get(a.get("OwnerUserId")) or ""
    created = a.get("CreationDate", "")[:10]
    # q id, title, fields, tags, score, views, answers, created, author, question text
    rows.append([int(qid), title[:200], fields_for(tags), tags[:5], score, views, answers, created, author, plain(a.get("Body", ""))])

rows.sort(key=lambda r: (-r[4], -r[5], r[0]))
meta = {"source": os.environ.get("MO_DUMP_LABEL", "MathOverflow data dump (archive.org, 2026-09-30)"), "statusChecked": STATUS is not None, "total": len(rows),
        "license": "Question text by its MathOverflow author, CC BY-SA (4.0 after 2018-05-02, 3.0 before); see the link"}
with gzip.open(OUT, "wt", encoding="utf-8") as f:
    json.dump({"meta": meta, "rows": rows}, f, ensure_ascii=False, separators=(",", ":"))
print(json.dumps(meta), file=sys.stderr)
