#!/usr/bin/env python3
"""Merges data/src_*.json into data/catalogue.json and writes data/seed.sql (the desk's problems table).
Tracks: lean (formalise and prove against Physlib; statements are reviewed by a person), open (an open question of
physics: a proof here settles it only if it can be stated formally; computations and literature work count as
evidence, never as a solution), compute (reproducible computations; none sourced yet)."""
import json, glob, re
rows, seen = [], set()
for f in sorted(glob.glob("data/src_*.json")):
    for r in json.load(open(f, encoding="utf-8")):
        if r["id"] in seen: continue
        seen.add(r["id"]); rows.append(r)
order = {"lean": 0, "open": 1, "compute": 2}
rows.sort(key=lambda r: (order.get(r["track"], 9), -r.get("fame", 0), r["id"]))
meta = {"total": len(rows), "tracks": {t: sum(1 for r in rows if r["track"] == t) for t in order},
        "sources": sorted({r["source"] for r in rows}),
        "fields": sorted({r["field"] for r in rows})}
json.dump({"meta": meta, "problems": rows}, open("data/catalogue.json", "w", encoding="utf-8"), ensure_ascii=False, separators=(",", ":"))
q = lambda s: "'" + str(s).replace("'", "''") + "'"
with open("data/seed.sql", "w", encoding="utf-8") as out:
    out.write("delete from problems;\n")
    for i in range(0, len(rows), 200):
        chunk = rows[i:i + 200]
        out.write("insert into problems (id, track, field, title) values " + ",".join(f"({q(r['id'])},{q(r['track'])},{q(r['field'])},{q(r['title'][:200])})" for r in chunk) + ";\n")
    out.write(f"insert or replace into meta (k, v) values ('catalogue', {q(json.dumps(meta['tracks']))});\n")
print(json.dumps(meta["tracks"]), "total", len(rows))
