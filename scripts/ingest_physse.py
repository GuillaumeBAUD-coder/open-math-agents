#!/usr/bin/env python3
"""Open questions from Physics Stack Exchange (CC BY-SA, attribution: the asker, with a link). Strict: score >= 10,
not closed, no accepted answer, and the question itself says the point is open or unknown (not "is it open?" alone).
Homework-like questions are left out. Output: data/src_physse.json."""
import json, re, sys, html
raw = json.load(open(sys.argv[1]))
OPEN = re.compile(r"(?i)\b(is (still )?an open (problem|question)|remains? (an )?open|still open|unsolved (problem|question)|(it is|is) (still )?(not known|unknown) (whether|if|how|why)|nobody knows (whether|if|how|why)|no one knows (whether|if|how|why)|open problem in|long-?standing (open )?(problem|puzzle))\b")
ASKS = re.compile(r"(?i)^\s*(is (this|it|there) (still )?an open|is .{0,80}\b(still )?(an )?open (problem|question)\s*\??\s*$)")
HOMEWORK = re.compile(r"(?i)\b(homework|exercise|textbook problem|my (teacher|professor)|exam)\b")
def text(s): return html.unescape(re.sub(r"<[^>]+>", " ", s or ""))
rows = []
for q in raw:
    if q.get("score", 0) < 10 or q.get("closed_date") or q.get("accepted_answer_id"): continue
    body = text(q.get("body")); title = html.unescape(q["title"])
    if HOMEWORK.search(body + " " + title): continue
    sents = re.split(r"(?<=[.!?])\s+", body)
    claim = [s for s in sents if OPEN.search(s) and not ASKS.search(s)]
    if not claim: continue
    tags = q.get("tags", [])
    stmt = " ".join(claim[:2])
    rest = re.sub(r"\s+", " ", body).strip()
    statement = (stmt + "\n\n" + rest)[:1500]
    rows.append({"id": f"physse-{q['question_id']}", "title": title, "track": "open", "field": (tags[0] if tags else "physics").replace("-", " ").title(),
                 "statement": statement, "source": "Physics Stack Exchange (open per the asker; read the answers)",
                 "ref": q["link"], "authors": [html.unescape(q.get("owner", {}).get("display_name", ""))],
                 "license": "CC BY-SA (Physics Stack Exchange; author and link kept)", "fame": min(80, 30 + q["score"] // 5), "tags": tags[:5]})
json.dump(rows, open("data/src_physse.json", "w", encoding="utf-8"), ensure_ascii=False, indent=0)
print(len(rows), "of", len(raw))
