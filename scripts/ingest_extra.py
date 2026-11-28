#!/usr/bin/env python3
"""Build data/extra.json: open problems that have NO Lean statement yet (kind "unformalized").

Sources (each entry keeps a link to its source and an attribution):
  - Wikipedia, "List of unsolved problems in mathematics" (section "Unsolved problems") and
    "List of conjectures" (open, and partly open) — text CC BY-SA 4.0, attributed on every page.
  - Open Problem Garden — metadata only (title, authors, area, importance, link); statements are not copied.
  - erdosproblems.com via teorth/erdosproblems — open problems that are not formalized yet (number, tags, prize, link).
Everything already present in data/catalog.json (the Lean catalogue) is dropped, so a problem appears once.

Usage: python3 -I scripts/ingest_extra.py <wp_unsolved.wiki> <wp_conjectures.wiki> <opg.json> <erdos problems.yaml> [out]
"""
import gzip
import json
import math
import os
import re
import sys

WP_UNSOLVED, WP_CONJ, OPG, ERDOS = sys.argv[1:5]
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = sys.argv[5] if len(sys.argv) > 5 else os.path.join(HERE, "..", "data", "extra.json")
CATALOG = json.load(open(os.path.join(HERE, "..", "data", "catalog.json"), encoding="utf-8"))

STOP = re.compile(r"\b(the|a|an|of|on|for|conjecture|conjectures|problem|problems|hypothesis|question|'s|s)\b")


def norm(s):
    import unicodedata
    s = unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode().lower().replace("’", "'").replace("–", "-").replace("—", "-")
    s = re.sub(r"'s\b", "", s)
    s = STOP.sub(" ", s)
    return re.sub(r"[^a-z0-9]+", "", s)


def slug(s):
    import unicodedata
    s = unicodedata.normalize("NFKD", s.replace("–", "-").replace("—", "-")).encode("ascii", "ignore").decode().lower()
    s = re.sub(r"[^a-z0-9]+", "-", s).strip("-")
    return s[:80]


# ---- what the Lean catalogue already covers ------------------------------------------------------
covered_titles, covered_wiki = set(), set()
for p in CATALOG["problems"]:
    covered_titles.add(norm(p["title"].split(" — ")[0]))
    if p.get("ref") and "wikipedia.org/wiki/" in p["ref"]:
        covered_wiki.add(norm(p["ref"].split("/wiki/")[1].split("#")[0].replace("_", " ")))
covered_erdos = {p["erdos"] for p in CATALOG["problems"] if p.get("erdos")}

# The proof catalogue omits upstream declarations with a linked proof. The pinned
# source snapshot still contains their files, including statements split into parts.
with gzip.open(os.path.join(HERE, "..", "data", "fc_files.json.gz"), "rt", encoding="utf-8") as snapshot:
    erdos_files = {int(m[1]): path for path in json.load(snapshot)
                   if (m := re.fullmatch(r"FormalConjectures/ErdosProblems/(\d+)\.lean", path))}

# Names the Lean files and declarations already use (e.g. Wikipedia/BergeFulkersonConjecture.lean,
# Erdos508.HadwigerNelsonProblem): a new entry whose normalized title starts with one of them is covered.
def camel(s):
    return re.sub(r"(?<=[a-z0-9])(?=[A-Z])", " ", s)

GENERIC = re.compile(r"^(erdos\d*|oeis|oeisa\d+|mathoverflow\d*|green\d*|kourovka|arxiv|paper|other|conjecture|variants?|parts?)$")
GENERIC_FIRST = {"universal", "spherical", "triangular", "complete", "edge", "general", "generalization", "asymptotic", "exponential",
                 "square", "minimum", "maximum", "density", "riemann", "zeta", "sum", "prime", "primes", "even", "infinite", "finite",
                 "first", "second", "third", "strong", "weak", "large", "small", "new", "main", "lower", "upper", "the", "is", "exists",
                 "number", "graph", "set", "sets", "conjecture", "problem", "property", "no", "not"}
covered_prefix = set()
for p in CATALOG["problems"]:
    names = [os.path.basename(p["file"])[:-5]] + p["decl"].split(".")
    for n in names:
        words = camel(n).replace("_", " ").split()
        k = norm(" ".join(words))
        # at least two words (eponyms like HadwigerNelson, BergeFulkerson) and no generic first word
        if len(words) >= 2 and len(k) >= 9 and not GENERIC.match(k) and words[0].lower() not in GENERIC_FIRST:
            covered_prefix.add(k)
dropped_by_prefix = []


def covered_by_prefix(title):
    k = norm(title)
    if len(k) < 9:
        return None
    for c in covered_prefix:
        if k.startswith(c):
            return c
    return None


# ---- wikitext helpers ----------------------------------------------------------------------------
def strip_templates(s):
    out, depth, i = [], 0, 0
    while i < len(s):
        if s.startswith("{{", i):
            depth += 1
            i += 2
            continue
        if depth and s.startswith("}}", i):
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(s[i])
        i += 1
    return "".join(out)


def wiki_to_text(s):
    s = re.sub(r"<ref[^>/]*/>", "", s)
    s = re.sub(r"<ref[^>]*>.*?</ref>", "", s, flags=re.S)
    s = strip_templates(s)
    s = re.sub(r"<math[^>]*>(.*?)</math>", lambda m: "$" + m.group(1).strip() + "$", s, flags=re.S)
    s = re.sub(r"\[\[(?:File|Image):[^\]]*\]\]", "", s)
    s = re.sub(r"\[\[([^\]|]+)\|([^\]]+)\]\]", r"\2", s)
    s = re.sub(r"\[\[([^\]]+)\]\]", r"\1", s)
    s = re.sub(r"\[https?://\S+ ([^\]]+)\]", r"\1", s)
    s = re.sub(r"'''?", "", s)
    s = re.sub(r"<[^>]+>", "", s)
    s = s.replace("&nbsp;", " ").replace("&ndash;", "–")
    return re.sub(r"\s+", " ", s).strip()


def first_link(s):
    m = re.search(r"\[\[([^\]|#][^\]|]*)(?:#([^\]|]*))?(?:\|([^\]]+))?\]\]", s)
    if not m:
        return None, None
    target = m.group(1).strip()
    anchor = m.group(2)
    text = (m.group(3) or (anchor if anchor and target in s[:2] else target)).strip()
    url = "https://en.wikipedia.org/wiki/" + target.replace(" ", "_") + ("#" + anchor.replace(" ", "_") if anchor else "")
    return text, url


FIELD_MAP = {
    "algebra": "General Algebra", "group theory": "Group Theory", "representation theory": "Group Theory",
    "analysis": "Real Functions", "combinatorics": "Combinatorics", "dynamical systems": "Dynamical Systems",
    "games and puzzles": "Game Theory & Economics", "combinatorial games": "Game Theory & Economics",
    "games with imperfect information": "Game Theory & Economics", "geometry": "Geometry",
    "algebraic geometry": "Algebraic Geometry", "covering and packing": "Convex & Discrete Geometry",
    "differential geometry": "Differential Geometry", "discrete geometry": "Convex & Discrete Geometry",
    "euclidean geometry": "Geometry", "non-euclidean geometry": "Geometry", "graph theory": "Combinatorics",
    "model theory and formal languages": "Logic & Foundations", "probability theory": "Probability",
    "number theory": "Number Theory", "set theory": "Logic & Foundations", "topology": "General Topology",
}


def field_for(section, sub):
    for k in (sub, section):
        if k and k.lower() in FIELD_MAP:
            return FIELD_MAP[k.lower()]
    for k in (sub, section):
        if not k:
            continue
        kl = k.lower()
        if "number" in kl or "prime" in kl or "diophant" in kl:
            return "Number Theory"
        if "graph" in kl:
            return "Combinatorics"
        if "geometr" in kl:
            return "Geometry"
    return (section or "Uncategorised").strip()


entries = {}
dropped = {"covered": 0, "duplicate": 0, "solved_per_wikipedia": 0}

# Problems Wikipedia lists as solved (sections "Problems solved since 2015", "Conjectures now proved",
# "Disproved"): used to drop stale "open" entries from other sources.
solved_keys = set()
_w = open(WP_UNSOLVED, encoding="utf-8").read()
_c = open(WP_CONJ, encoding="utf-8").read()
for chunk in (_w[_w.index("== Problems solved since"):_w.index("== See also")],
              _c[_c.index("==Conjectures now proved"):_c.index("==Refutations of conventional")]):
    for m in re.finditer(r"\[\[([^\]|#]+)(?:#[^\]|]*)?(?:\|([^\]]+))?\]\]", chunk):
        for t in (m.group(1), m.group(2)):
            if t:
                k = norm(t)
                if len(k) >= 8:
                    solved_keys.add(k)


def add(e, keys):
    """Add unless the Lean catalogue or an earlier source already has it."""
    for k in keys:
        if k and (k in covered_titles or k in covered_wiki):
            dropped["covered"] += 1
            return
    if e["source"] == "Open Problem Garden" and norm(e["title"]) in solved_keys:
        dropped["solved_per_wikipedia"] += 1
        dropped_by_prefix.append((e["title"], "SOLVED per Wikipedia"))
        return
    if not e["id"].startswith("erdos-"):
        c = covered_by_prefix(e["title"])
        if c:
            dropped["covered"] += 1
            dropped_by_prefix.append((e["title"], c))
            return
    for k in keys:
        if k and k in seen_keys:
            dropped["duplicate"] += 1
            other = entries[seen_keys[k]]
            other.setdefault("alsoIn", [])
            if e["source"] not in other["alsoIn"] and e["source"] != other["source"]:
                other["alsoIn"].append(e["source"])
            return
    base, n = e["id"], 2
    while e["id"] in entries:
        e["id"] = f"{base}-{n}"
        n += 1
    entries[e["id"]] = e
    for k in keys:
        if k:
            seen_keys[k] = e["id"]


seen_keys = {}


def base_entry(**kw):
    e = {"decl": "", "kind": "unformalized", "category": "unformalized", "tags": [], "statement": "", "lean": "", "module": "",
         "file": "", "line": 0, "prize": None, "erdos": None, "erdosState": None, "forumPosts": 0}
    e.update(kw)
    return e


# ---- 1. Wikipedia: List of unsolved problems in mathematics --------------------------------------
wiki = open(WP_UNSOLVED, encoding="utf-8").read()
start = wiki.index("== Unsolved problems ==")
end = wiki.index("== Problems solved since")
section = sub = None
for line in wiki[start:end].splitlines():
    h3 = re.match(r"^===\s*([^=]+?)\s*===\s*$", line)
    h4 = re.match(r"^====\s*([^=]+?)\s*====\s*$", line)
    if h3:
        section, sub = h3.group(1), None
        continue
    if h4:
        sub = h4.group(1)
        continue
    if not line.startswith("*"):
        continue
    body = line.lstrip("*").strip()
    name, url = first_link(body)
    text = wiki_to_text(body)
    if not name or len(text) < 4:
        continue
    name_clean = wiki_to_text(name)
    # Title: the linked name (or the text before a colon when the item starts with prose)
    title = name_clean
    pre = text.split(":")[0].strip()
    if len(pre) < 90 and name_clean.lower() in pre.lower():
        title = pre.removeprefix("The ").strip() if pre.lower().startswith("the ") else pre
    desc = text[len(pre) + 1:].strip() if ":" in text and text.startswith(pre) else text
    if desc.lower() == title.lower():
        desc = ""
    fld = field_for(section, sub)
    e = base_entry(id="wp-" + slug(title), title=title[:140], source="Wikipedia list (not formalized)",
                   fields=[fld], statement=desc[:900], ref=url, license="Text: Wikipedia, CC BY-SA 4.0",
                   area=f"{section}{' » ' + sub if sub else ''}")
    add(e, [norm(title), norm(name_clean), norm(url.split("/wiki/")[1].split("#")[0].replace("_", " ")) if "#" not in url else None])

# ---- 2. Wikipedia: List of conjectures (open + partly open tables) -------------------------------
conj = open(WP_CONJ, encoding="utf-8").read()
s_open = conj.index("==Open problems==")
s_end = conj.index("==Conjectures now proved")
for row in conj[s_open:s_end].split("\n|-"):
    cells = [c.strip() for c in re.split(r"\n\||\|\|", "\n" + row.strip()) if c.strip()]
    if not cells or not cells[0].startswith("[["):
        continue
    name, url = first_link(cells[0])
    if not name:
        continue
    title = wiki_to_text(name)
    fieldtxt = wiki_to_text(cells[1]) if len(cells) > 1 else ""
    comment = wiki_to_text(cells[2]) if len(cells) > 2 else ""
    cites = re.findall(r"\d+", cells[-1]) if len(cells) >= 5 else []
    partial = conj.index(row) > conj.index("==Conjectures with resolved")
    e = base_entry(id="wp-" + slug(title), title=title[:140], source="Wikipedia list (not formalized)",
                   fields=[field_for(fieldtxt, None).title() if fieldtxt else "Uncategorised"],
                   statement=(("Partly resolved: " if partial else "") + comment)[:900], ref=url,
                   license="Text: Wikipedia, CC BY-SA 4.0", area=fieldtxt, cites=int(cites[0]) if cites else 0)
    add(e, [norm(title), norm(url.split("/wiki/")[1].split("#")[0].replace("_", " ")) if "#" not in url else None])

# ---- 3. Open Problem Garden (metadata only) ------------------------------------------------------
OPG_FIELD = {"algebra": "General Algebra", "analysis": "Real Functions", "combinatorics": "Combinatorics",
             "geometry": "Geometry", "graph_theory": "Combinatorics", "group_theory": "Group Theory",
             "logic": "Logic & Foundations", "number_theory_0": "Number Theory", "pdes": "PDEs",
             "probability": "Probability", "theoretical_computer_science": "Computer Science", "topology": "General Topology"}
opg = json.load(open(OPG, encoding="utf-8")) if os.path.exists(OPG) else []
for r in opg:
    title = r["title"].strip()
    if re.search(r"(?i)dragon ball|casino|crypto|guide —|\b2026\)", title):
        continue  # spam that slipped into a table
    areas = r.get("areas") or []
    flds = sorted({OPG_FIELD[a] for a in areas if a in OPG_FIELD})
    if not flds:
        kw = " ".join(areas + [title.lower()])
        for words, f in ((("graph", "colo", "flow", "domination", "cycle", "matching", "tournament", "hypergraph", "ramsey", "design", "matroid", "poset", "latin"), "Combinatorics"),
                         (("prime", "number", "diophant", "arithmetic", "integer", "modular"), "Number Theory"),
                         (("group", "algebra", "ring", "lattice"), "General Algebra"),
                         (("geometr", "polytope", "convex", "packing", "tiling", "plane"), "Geometry"),
                         (("topolog", "manifold", "knot", "dimensional"), "General Topology"),
                         (("complex", "random", "probab", "percolation"), "Probability"),
                         (("logic", "set theory", "cardinal", "syntax", "mso", "model"), "Logic & Foundations"),
                         (("complexity", "algorithm", "derandom", "approximation", "circuit"), "Computer Science")):
            if any(w in kw for w in words):
                flds = [f]
                break
    flds = flds or ["Uncategorised"]
    e = base_entry(id="opg-" + slug(r["slug"].split("/")[-1]), title=title[:140], source="Open Problem Garden",
                   fields=flds, statement="", ref="https://www.openproblemgarden.org" + r["slug"],
                   authors=r["authors"][:8], stars=r.get("stars", 0), license="Metadata from Open Problem Garden; statement on the linked page",
                   area=", ".join(a.replace("_", " ").replace(" 0", "") for a in areas[:4]))
    add(e, [norm(title)])

# ---- 4. erdosproblems.com: open and not formalized -----------------------------------------------
raw = open(ERDOS, encoding="utf-8").read()
TAGF = {"number theory": "Number Theory", "graph theory": "Combinatorics", "combinatorics": "Combinatorics",
        "geometry": "Geometry", "analysis": "Real Functions", "additive combinatorics": "Combinatorics", "primes": "Number Theory",
        "ramsey theory": "Combinatorics", "probability": "Probability", "set theory": "Logic & Foundations"}
upstream_erdos = []
for b in re.split(r"\n(?=- number:)", raw):
    m = re.match(r'- number: "?(\d+)"?', b.strip())
    if not m:
        continue
    num = int(m.group(1))
    st = re.search(r'\n  status:\n    state: "([^"]+)"', b)
    if not st:
        continue
    eligible = st.group(1).startswith(("open", "falsifiable", "verifiable", "decidable")) and num not in covered_erdos
    if not eligible:
        local_statement = os.path.join(HERE, "..", "statements", f"erdos-{num}.lean")
        if num not in erdos_files or not os.path.isfile(local_statement):
            continue
    tags = re.findall(r'"([^"]+)"', (re.search(r"\n  tags: \[(.*?)\]", b) or [None, ""])[1])
    prize = (re.search(r'\n  prize: "([^"]*)"', b) or [None, None])[1]
    prize = None if prize in (None, "", "no") else prize
    posts = int((re.search(r"\n  forum:\n    posts: (\d+)", b) or [None, 0])[1])
    e = base_entry(id=f"erdos-{num}", title=f"Erdős Problem {num}", source="Erdős Problems (not formalized)",
                   fields=sorted({TAGF[t] for t in tags if t in TAGF}) or ["Combinatorics"], tags=tags, ref=f"https://www.erdosproblems.com/{num}",
                   prize=prize, erdos=num, erdosState=st.group(1), forumPosts=posts, statement="",
                   license="Metadata from teorth/erdosproblems; statement on erdosproblems.com")
    if num in erdos_files:
        # Keep the source metadata for any OMA statement that has already merged
        # or merges before the next build. These are never new formalization tasks.
        e["source"] = "Erdős Problems"
        e["upstreamFile"] = erdos_files[num]
        del e["kind"], e["category"]
        upstream_erdos.append(e)
        dropped["covered"] += 1
    else:
        add(e, [f"erdos{num}"])

# ---- difficulty (heuristic, same scale as the Lean catalogue) ------------------------------------
def prize_usd(p):
    m = re.search(r"[$£](\d+)", (p or "").replace(",", ""))
    return int(m.group(1)) if m else 0


for e in [*entries.values(), *upstream_erdos]:
    d = 60
    d += 6 * e.get("stars", 0) if e["source"] == "Open Problem Garden" else 0
    d += min(20, 6 * math.log10(1 + prize_usd(e.get("prize")))) if e.get("prize") else 0
    d += min(15, 3 * math.log10(1 + e.get("cites", 0))) if e.get("cites") else 0
    if e.get("erdosState", "") and e["erdosState"].split(" ")[0] in ("falsifiable", "decidable", "verifiable"):
        d -= 10
    e["difficulty"] = max(20, min(99, round(d)))

for e in entries.values():
    if e["title"] and e["title"][0].islower():
        e["title"] = e["title"][0].upper() + e["title"][1:]
    if e["statement"] and norm(e["statement"]) == norm(e["title"]):
        e["statement"] = ""

problems = sorted(entries.values(), key=lambda e: (-e["difficulty"], e["id"]))
counts = {}
for e in problems:
    counts[e["source"]] = counts.get(e["source"], 0) + 1
meta = {"counts": counts, "total": len(problems), "dropped": dropped,
        "note": "Open problems without a Lean statement yet. Status follows each source at the time of import; some may have been solved since."}
json.dump({"meta": meta, "problems": problems, "upstreamErdos": upstream_erdos}, open(OUT, "w", encoding="utf-8"), ensure_ascii=False, separators=(",", ":"))
print(json.dumps(meta, ensure_ascii=False, indent=1))
if os.environ.get("SHOW_PREFIX_DROPS"):
    for t, c in dropped_by_prefix:
        print("  covered:", t, "<-", c)
