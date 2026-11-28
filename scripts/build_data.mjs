#!/usr/bin/env node
// Build the catalogue for Cloudflare Workers, where a Worker has 128 MB of memory and D1 (free plan) takes 100,000 row
// writes a day:
//   data/gen/cards.json     what lists, filters and sorts need, kept in memory (no statement text)
//   data/gen/catalog.sql    core sources: statements, Lean, full-text index, upstream Lean files (one row per problem)
//   data/gen/catalog-mo.sql the MathOverflow long tail, packed ~20 questions per row with a contentless full-text
//                           index, so loading 20,000+ questions writes about 2,000 rows instead of 70,000
//   public/map-data.json    the map's static layer, served as a static file (no Worker request)
// Run after scripts/build_statements.mjs. Usage: node scripts/build_data.mjs
import fs from "node:fs";
import path from "node:path";
import zlib from "node:zlib";

const ROOT = path.join(path.dirname(new URL(import.meta.url).pathname), "..");
const D = (f) => JSON.parse(fs.readFileSync(path.join(ROOT, "data", f), "utf8"));
const catalog = D("catalog.json");
const extra = D("extra.json");
const e2 = D("extra2.json");
const statements = D("statements.json");
const overrides = D("status_overrides.json").entries;
const e3 = JSON.parse(zlib.gunzipSync(fs.readFileSync(path.join(ROOT, "data", "extra3.json.gz"))).toString("utf8"));

const lg = (x) => Math.log10(1 + x);
const prizeUsd = (p) => { const m = (p ?? "").replace(/,/g, "").match(/[$£](\d+)/); return m ? Number(m[1]) : 0; };
// formal-conjectures can lag behind erdosproblems.com: a statement still tagged "research open" upstream whose Erdős
// problem is already proved, disproved or solved is a known result, not an open problem. Main statements and their
// parts only: for a variant, the status describes the main problem, not the variant. Same rule in tools/lint.py.
const SETTLED_STATE = /^(proved|disproved|solved)\b/;
// A problem proved here stays an open problem solved here: erdosproblems.com then marks it solved because of our proof.
const provedHere = (id) => fs.existsSync(path.join(ROOT, "proofs", `${id}.lean`));
function settledUpstream(p) {
  if (p.kind !== "open" || !SETTLED_STATE.test(p.erdosState ?? "") || /\.variants?\./.test(p.id) || provedHere(p.id)) return p;
  return { ...p, kind: "known", category: "research solved (per erdosproblems.com)" };
}

function fameOf(p) {
  const base = {
    "Millennium Prize": 100, "Hilbert's Problems": 95, "Wikipedia": 85, "Green's 100 Open Problems": 78, "Kourovka Notebook": 60,
    "MathOverflow": 58, "Erdős Problems": 62, "OEIS": 42, "Wikipedia list (not formalized)": 80, "Open Problem Garden": 45,
    "Erdős Problems (not formalized)": 58,
  };
  let f = base[p.source] ?? 50;
  if (p.prize) f += Math.min(18, 4 * lg(prizeUsd(p.prize)));
  if (p.stars) f += 8 * p.stars;
  if (p.cites) f += Math.min(10, 3 * lg(p.cites));
  if (p.forumPosts) f += Math.min(6, p.forumPosts / 5);
  if (/\.variants?\.|\.parts?\./.test(p.decl)) f -= 8;
  if (p.kind === "warmup") f -= 20;
  return Math.max(1, Math.min(100, Math.round(f)));
}
const formalized = (p) => {
  const st = statements[p.id];
  return st ? { ...p, kind: "open", category: "research open (formalized here)", decl: st.decl, module: st.module, lean: st.lean, file: st.file, formalizedHere: true } : p;
};

const core = [
  ...catalog.problems.map((p) => ({ ...settledUpstream(p), fame: fameOf(p) })),
  ...extra.problems.concat((extra.upstreamErdos ?? []).filter((p) => statements[p.id]))
    .map((p) => formalized({ ...p, fame: fameOf(p) })),
  ...e2.rows.map(([id, title, si, fields, statement, ref, authors, fame, difficulty, tags, area, posts]) => formalized({
    id, title, source: e2.sources[si], kind: "unformalized", category: "unformalized", fields, tags, statement, ref, authors, fame, difficulty,
    area, decl: "", lean: "", module: "", file: "", line: 0, prize: null, erdos: null, erdosState: null, forumPosts: posts, license: e2.licenses[e2.sources[si]],
  })),
];

// MathOverflow long tail (data/extra3.json.gz), minus questions already listed.
const seen = new Set(core.map((p) => p.id));
const MO_LICENSE = "Question text by its MathOverflow author (CC BY-SA); see the link";
let mo = e3.rows.filter((r) => !seen.has(`mo-${r[0]}`)).map(([qid, title, fields, tags, score, views, answers, created, author, text]) => ({
  id: `mo-${qid}`, qid, title, source: "MathOverflow (not formalized)", kind: "unformalized", category: "unformalized", fields, tags,
  statement: text, ref: `https://mathoverflow.net/questions/${qid}`, authors: author ? [author] : [], area: tags.slice(0, 4).join(", "),
  fame: 25 + Math.min(35, Math.floor(score / 4)) + 8, difficulty: 55 + Math.min(15, Math.floor(score / 20)), decl: "", lean: "", module: "", file: "",
  line: 0, prize: null, erdos: null, erdosState: null, forumPosts: answers, license: MO_LICENSE, asked: created,
}));
// A MathOverflow question whose Lean statement has been merged becomes a provable problem: it moves to the core
// tables, which hold Lean sources.
for (let i = mo.length - 1; i >= 0; i--) if (statements[mo[i].id]) { const [p] = mo.splice(i, 1); delete p.qid; core.push(formalized(p)); }
const all = [...core, ...mo];

// Same TeX → Unicode as lib/catalog.ts texPlain, for the one-line excerpt kept in memory.
const TEX = {
  mathbb: "", mathbf: "", mathrm: "", mathcal: "", operatorname: "", text: "", textrm: "", mathfrak: "",
  le: "≤", leq: "≤", ge: "≥", geq: "≥", ne: "≠", neq: "≠", in: "∈", notin: "∉", subset: "⊂", subseteq: "⊆",
  cup: "∪", cap: "∩", infty: "∞", to: "→", rightarrow: "→", mapsto: "↦", times: "×", cdot: "·", cdots: "…", ldots: "…", dots: "…",
  sum: "∑", prod: "∏", int: "∫", sqrt: "√", log: "log", exp: "exp", lim: "lim", liminf: "liminf", limsup: "limsup", sim: "∼",
  approx: "≈", ll: "≪", gg: "≫", forall: "∀", exists: "∃", neg: "¬", land: "∧", lor: "∨", mid: "|", lvert: "|", rvert: "|", vert: "|",
  alpha: "α", beta: "β", gamma: "γ", delta: "δ", epsilon: "ε", varepsilon: "ε", zeta: "ζ", eta: "η", theta: "θ", lambda: "λ",
  mu: "μ", nu: "ν", pi: "π", rho: "ρ", sigma: "σ", tau: "τ", phi: "φ", varphi: "φ", chi: "χ", psi: "ψ", omega: "ω",
  Gamma: "Γ", Delta: "Δ", Lambda: "Λ", Sigma: "Σ", Phi: "Φ", Omega: "Ω", left: "", right: "", lfloor: "⌊", rfloor: "⌋",
  lceil: "⌈", rceil: "⌉", binom: "binom", frac: "", pmod: "mod", bmod: "mod", equiv: "≡", setminus: "∖", emptyset: "∅",
};
const BB = { N: "ℕ", Z: "ℤ", Q: "ℚ", R: "ℝ", C: "ℂ", P: "ℙ", F: "𝔽" };
const texPlain = (s) => s
  .replace(/\\mathbb\s*\{?([A-Z])\}?/g, (_, c) => BB[c] ?? c)
  .replace(/\\frac\s*\{([^{}]*)\}\s*\{([^{}]*)\}/g, "($1)/($2)")
  .replace(/\\([A-Za-z]+)/g, (m, w) => (w in TEX ? TEX[w] : w))
  .replace(/\\[,;!: ]/g, " ")
  .replace(/[{}$*`]/g, "")
  .replace(/\s+/g, " ")
  .trim();

// ---- cards.json ----------------------------------------------------------------------------------------
const sources = Array.from(new Set(all.map((p) => p.source))).sort();
const KINDS = ["open", "known", "warmup", "unformalized"];
const MO_BUCKETS = Math.max(1, Math.ceil(mo.length / 20));
// id, title, source index, kind index, fields, tags, difficulty, fame, prize, forumPosts, erdos, decl, shard (0 core, 1 MathOverflow)
// Statement excerpts are not kept in memory: list pages read them from D1 for the rows they show.
const rows = all.map((p) => [
  p.id, p.title, sources.indexOf(p.source), KINDS.indexOf(p.kind), p.fields ?? [], [], p.difficulty, p.fame, // tags: searched in D1, not kept in memory
  p.prize ?? null, p.forumPosts ?? 0, p.erdos ?? null, p.decl ?? "", p.qid ? 1 : 0,
]);
fs.mkdirSync(path.join(ROOT, "data", "gen"), { recursive: true });
fs.writeFileSync(path.join(ROOT, "data", "gen", "cards.json"), JSON.stringify({
  meta: { ...catalog.meta, extra: extra.meta, extra2: e2.meta, extra3: e3.meta, moBuckets: MO_BUCKETS }, sources, kinds: KINDS, rows,
}));

// ---- public/map-data.json (static: the map's layout never depends on live data) -----------------------
const solvedNow = new Set(overrides.filter((o) => o.status === "solved").map((o) => o.id));
const mapRows = all.filter((p) => !solvedNow.has(p.id)).map((p) => [p.id, p.title.slice(0, 70), sources.indexOf(p.source), KINDS.indexOf(p.kind), p.difficulty]);
fs.writeFileSync(path.join(ROOT, "public", "map-data.json"), JSON.stringify({ sources, rows: mapRows }));

// ---- catalog.sql ---------------------------------------------------------------------------------------
// D1 caps one SQL statement at 100 KB, so long values are split into parts of at most 12,000 characters (36 KB of UTF-8 at worst).
const q = (s) => "'" + String(s).replace(/'/g, "''") + "'";
const PART = 12000;
const parts = (s) => { const out = []; for (let i = 0; i < s.length || i === 0; i += PART) out.push(s.slice(i, i + PART)); return out; };
const out = [
  "DROP TABLE IF EXISTS problem;", "DROP TABLE IF EXISTS fts;", "DROP TABLE IF EXISTS upstream_file;",
  "CREATE TABLE problem (id TEXT NOT NULL, part INTEGER NOT NULL, data TEXT NOT NULL, PRIMARY KEY (id, part));",
  "CREATE VIRTUAL TABLE fts USING fts5(id UNINDEXED, title, statement, decl, extra, tokenize = 'unicode61 remove_diacritics 2', prefix = '2 3 4');",
  "CREATE TABLE upstream_file (path TEXT NOT NULL, part INTEGER NOT NULL, content TEXT NOT NULL, PRIMARY KEY (path, part));",
  // meta is shared with the MathOverflow part (version_mo): never dropped, or a core import would force a MathOverflow one.
  "CREATE TABLE IF NOT EXISTS meta (k TEXT PRIMARY KEY, v TEXT NOT NULL);",
];
const DETAIL = ["statement", "lean", "module", "file", "line", "category", "ref", "erdosState", "license", "authors", "area", "alsoIn", "formalizedHere"];
for (const p of core) {
  const d = {};
  for (const k of DETAIL) if (p[k] !== undefined && p[k] !== null && p[k] !== "") d[k] = p[k];
  parts(JSON.stringify(d)).forEach((s, i) => out.push(`INSERT INTO problem VALUES (${q(p.id)}, ${i}, ${q(s)});`));
  const extraText = [p.source, ...(p.fields ?? []), ...(p.tags ?? []), p.erdos ? `erdos ${p.erdos} erdős ${p.erdos}` : ""].join(" ");
  out.push(`INSERT INTO fts (id, title, statement, decl, extra) VALUES (${q(p.id)}, ${q(p.title)}, ${q((p.statement ?? "").replace(/[\\${}_^]/g, " ").slice(0, 12000))}, ${q((p.decl ?? "").replace(/[._]/g, " "))}, ${q(extraText)});`);
}
const files = JSON.parse(zlib.gunzipSync(fs.readFileSync(path.join(ROOT, "data", "fc_files.json.gz"))).toString("utf8"));
for (const [p, content] of Object.entries(files)) parts(content).forEach((s, i) => out.push(`INSERT INTO upstream_file VALUES (${q(p)}, ${i}, ${q(s)});`));
const version = `${catalog.meta.upstreamCommit.slice(0, 12)}-${core.length}-${Object.keys(statements).length}`;
out.push(`INSERT OR REPLACE INTO meta VALUES ('version', ${q(version)});`);
fs.writeFileSync(path.join(ROOT, "data", "gen", "catalog.sql"), out.join("\n") + "\n");
fs.writeFileSync(path.join(ROOT, "data", "gen", "version.txt"), version + "\n");
// ---- catalog-mo.sql -----------------------------------------------------------------------------------
const moOut = [
  "DROP TABLE IF EXISTS mo_detail;", "DROP TABLE IF EXISTS mo_fts;", "CREATE TABLE IF NOT EXISTS meta (k TEXT PRIMARY KEY, v TEXT NOT NULL);",
  "CREATE TABLE mo_detail (b INTEGER PRIMARY KEY, data TEXT NOT NULL);",
  // contentless (no copy of the text) and no column sizes: only the index segments are written; rowid = question id
  "CREATE VIRTUAL TABLE mo_fts USING fts5(title, statement, extra, content = '', columnsize = 0, tokenize = 'unicode61 remove_diacritics 2', prefix = '2 3 4');",
];
const buckets = new Map();
for (const p of mo) {
  const b = p.qid % MO_BUCKETS;
  if (!buckets.has(b)) buckets.set(b, {});
  buckets.get(b)[p.id] = { statement: p.statement, ref: p.ref, authors: p.authors, area: p.area, license: p.license, category: "unformalized", asked: p.asked };
}
let biggest = 0;
for (const [b, obj] of buckets) {
  const stmt = `INSERT INTO mo_detail VALUES (${b}, ${q(JSON.stringify(obj))});`;
  biggest = Math.max(biggest, Buffer.byteLength(stmt));
  moOut.push(stmt);
}
if (biggest > 95000) throw new Error(`a MathOverflow bucket statement is ${biggest} bytes (D1 limit 100 KB): raise the bucket count`);
for (const p of mo) {
  moOut.push(`INSERT INTO mo_fts (rowid, title, statement, extra) VALUES (${p.qid}, ${q(p.title)}, ${q(p.statement.replace(/[\\${}_^]/g, " "))}, ${q([p.source, ...p.fields, ...p.tags].join(" "))});`);
}
const moVersion = `mo-${e3.meta.total}-${mo.length}-${MO_BUCKETS}`;
moOut.push(`INSERT OR REPLACE INTO meta VALUES ('version_mo', ${q(moVersion)});`);
fs.writeFileSync(path.join(ROOT, "data", "gen", "catalog-mo.sql"), moOut.join("\n") + "\n");
fs.writeFileSync(path.join(ROOT, "data", "gen", "version-mo.txt"), moVersion + "\n");

const mb = (f) => (fs.statSync(path.join(ROOT, "data", "gen", f)).size / 1e6).toFixed(1);
console.log(`cards.json ${mb("cards.json")} MB (${rows.length} problems: ${core.length} core + ${mo.length} MathOverflow) · catalog.sql ${mb("catalog.sql")} MB (${out.length} statements, version ${version}) · catalog-mo.sql ${mb("catalog-mo.sql")} MB (${buckets.size} buckets, largest ${biggest} B, version ${moVersion})`);
