#!/usr/bin/env python3
"""Open problems from Wikipedia's "List of unsolved problems in physics" (CC BY-SA 4.0, attribution kept).
Input: the page wikitext as returned by the MediaWiki parse API (JSON). Only the topic sections before "Problems solved
in the past 30 years"; one entry per bullet "* [[Topic]]: question". Output: data/src_wikipedia.json."""
import json, re, sys, html

w = json.load(open(sys.argv[1], encoding="utf-8"))["parse"]["wikitext"]
w = w.split("== Problems solved in the past 30 years", 1)[0]

def clean(t):
    t = re.sub(r"<ref[^>]*/>", "", t)
    t = re.sub(r"<ref[^>]*>.*?</ref>", "", t, flags=re.S)
    for _ in range(4): t = re.sub(r"\{\{[^{}]*\}\}", "", t)
    t = re.sub(r"\[\[(?:[^|\]]*\|)?([^\]]*)\]\]", r"\1", t)
    t = re.sub(r"\[https?://\S+ ([^\]]*)\]", r"\1", t)
    t = re.sub(r"'''?", "", t)
    t = re.sub(r"<math>(.*?)</math>", r"$\1$", t, flags=re.S)
    t = re.sub(r"<[^>]+>", "", t)
    return html.unescape(re.sub(r"\s+", " ", t)).strip()

FIELD = {"General physics": "General", "Quantum gravity": "Quantum gravity", "Quantum physics": "Quantum physics",
         "Cosmology and general relativity": "Cosmology & GR", "High-energy/particle physics": "Particle physics",
         "Astronomy and astrophysics": "Astrophysics", "Nuclear physics": "Nuclear physics", "Fluid dynamics": "Fluid dynamics",
         "Condensed matter physics": "Condensed matter", "Quantum computing and quantum information": "Quantum information",
         "Plasma physics": "Plasma physics", "Biophysics": "Biophysics", "Foundations of physics": "Foundations"}
rows, section, seen = [], None, set()
for line in w.split("\n"):
    m = re.match(r"^=+\s*(.+?)\s*=+\s*$", line)
    if m: section = m.group(1); continue
    if section not in FIELD or not line.startswith("* "): continue
    m = re.match(r"^\*\s*\[\[([^\]|]+)(?:\|([^\]]+))?\]\]([^:]{0,90}):\s*(.+)$", line)
    if m:
        target, title, text = m.group(1), clean(m.group(2) or m.group(1)), clean(m.group(4))
    else:  # "* question mentioning [[Topic|...]]": the first link names it, the whole bullet is the statement
        l = re.search(r"\[\[([^\]|]+)(?:\|[^\]]+)?\]\]", line)
        if not l: continue
        target, title, text = l.group(1), clean(l.group(1)), clean(line[2:])
    if len(text) < 30 or title.lower() in seen: continue
    seen.add(title.lower())
    slug = re.sub(r"[^a-z0-9]+", "-", title.lower()).strip("-")[:60]
    rows.append({"id": f"wp-{slug}", "title": title, "track": "open", "field": FIELD[section], "statement": text,
                 "source": "Wikipedia: List of unsolved problems in physics",
                 "ref": "https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_physics",
                 "topic": "https://en.wikipedia.org/wiki/" + target.strip().replace(" ", "_"),
                 "license": "CC BY-SA 4.0 (Wikipedia contributors)", "fame": 90})
json.dump(rows, open("data/src_wikipedia.json", "w", encoding="utf-8"), ensure_ascii=False, indent=0)
print(len(rows), "problems;", {f: sum(1 for r in rows if r["field"] == f) for f in sorted(set(r["field"] for r in rows))})
