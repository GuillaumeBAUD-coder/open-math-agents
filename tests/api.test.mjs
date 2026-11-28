// Integration tests against a running site (default http://localhost:3123) wired to a real desk.
// Run: BASE=http://localhost:3123 OMA_VERDICT_SECRET=<the server's> node --test tests/api.test.mjs
// Creates data under handles "oma-test-*" and reductions "OMATEST*"; delete them afterwards (tests/cleanup.sql).
import { test } from "node:test";
import assert from "node:assert/strict";
import { existsSync, readFileSync } from "node:fs";

const BASE = process.env.BASE ?? "http://localhost:3123";
const VSECRET = process.env.OMA_VERDICT_SECRET;
const RUN = Date.now().toString(36);
const H = (n) => `oma-test-${RUN}-${n}`.slice(0, 39);
const j = async (path, init) => { const r = await fetch(BASE + path, init); let body = null; try { body = await r.json(); } catch {} return { status: r.status, body }; };
const t = async (path) => { const r = await fetch(BASE + path); return { status: r.status, text: await r.text() }; };
const post = (path, body, headers = {}) => j(path, { method: "POST", headers: { "Content-Type": "application/json", ...headers }, body: body === undefined ? undefined : JSON.stringify(body) });
const eventually = async (fn, ms = 90000) => { const end = Date.now() + ms; let last; while (Date.now() < end) { try { return await fn(); } catch (e) { last = e; await new Promise((r) => setTimeout(r, 2500)); } } throw last; };

let catalogTotal = 0;

test("stats: desk online and catalogue counts add up", async () => {
  const { status, body } = await j("/api/stats");
  assert.equal(status, 200);
  assert.equal(body.deskOnline, true);
  const c = body.catalog;
  catalogTotal = body.total;
  assert.equal(c.open + c.known + c.warmup + c.unformalized, body.total);
  assert.ok(body.total >= 10000, `at least 10,000 problems, got ${body.total}`);
});

test("search: query, kinds, sources, sorts, paging", async () => {
  const q = await j("/api/problems?q=collatz&kind=all&limit=50");
  assert.equal(q.status, 200);
  assert.ok(q.body.items.some((x) => /collatz/i.test(x.title)));
  for (const kind of ["open", "known", "warmup", "unformalized"]) {
    const r = await j(`/api/problems?kind=${kind}&limit=40`);
    assert.ok(r.body.total > 0, kind);
    assert.ok(r.body.items.every((x) => x.kind === kind), `only ${kind}`);
  }
  const all = await j("/api/problems?kind=all&limit=1");
  assert.equal(all.body.total, catalogTotal);
  const src = await j("/api/problems?kind=all&source=" + encodeURIComponent("OEIS conjectures (not formalized)") + "&limit=20");
  assert.ok(src.body.total >= 10000);
  assert.ok(src.body.items.every((x) => x.source === "OEIS conjectures (not formalized)"));
  const hard = (await j("/api/problems?kind=open&sort=hardest&limit=30")).body.items.map((x) => x.difficulty);
  assert.deepEqual(hard, [...hard].sort((a, b) => b - a));
  const easy = (await j("/api/problems?kind=open&sort=easiest&limit=30")).body.items.map((x) => x.difficulty);
  assert.deepEqual(easy, [...easy].sort((a, b) => a - b));
  const p1 = (await j("/api/problems?kind=all&limit=10&offset=0")).body.items.map((x) => x.id);
  const p2 = (await j("/api/problems?kind=all&limit=10&offset=10")).body.items.map((x) => x.id);
  assert.equal(new Set([...p1, ...p2]).size, 20, "pages do not overlap");
  const famous = (await j("/api/problems?kind=all&limit=5")).body.items;
  assert.ok(famous.some((x) => /NP|Riemann|Birch|Hodge|Navier|Poincar|Yang/i.test(x.title)), "most famous first by default: " + famous.map((x) => x.title));
  const full = await j("/api/problems?kind=open&limit=1&full=1");
  assert.ok(full.body.items[0].lean.length > 0);
  const weird = await j("/api/problems?q=%22%3Cscript%3E&limit=999&offset=-5&sort=nonsense");
  assert.equal(weird.status, 200);
  assert.ok(weird.body.items.length <= 200);
});

test("status: solved problems are gone, claimed ones are flagged and never handed out by default", async () => {
  for (const id of ["wp-riemann-hypothesis", "wp-generalized-riemann-hypothesis", "wp-do-siegel-zeros-exist", "wp-erdos-conjecture-on-arithmetic-progressions"]) {
    assert.equal((await j(`/api/problems/${id}`)).status, 404, `${id} removed`);
  }
  const rh = await j("/api/problems?kind=all&q=riemann%20hypothesis&limit=50");
  assert.ok(!rh.body.items.some((x) => /^Riemann hypothesis$/i.test(x.title) || x.id === "RiemannHypothesis.riemannHypothesis"), "RH not listed as open");
  const erh = await j("/api/problems/ERH.extended_riemann_hypothesis");
  assert.equal(erh.body.title, "Extended Riemann Hypothesis (Dedekind zeta functions)");
  const ns = await j("/api/problems/NavierStokes.navier_stokes_existence_and_smoothness_R3");
  assert.equal(ns.status, 200);
  assert.ok(ns.body.claim && /OpenAI/.test(ns.body.claim.summary), "Navier–Stokes flagged as claimed");
  const brief = await t("/p/NavierStokes.navier_stokes_existence_and_smoothness_R3/agent.txt");
  assert.match(brief.text, /A SOLUTION HAS BEEN CLAIMED/);
  const page = await t("/status");
  assert.equal(page.status, 200);
  assert.match(page.text, /Riemann hypothesis/);
  for (let i = 0; i < 8; i++) {
    const r = await j(`/api/desk/next?handle=${H("cl" + i)}&kind=open&level=legendary`);
    if (r.status !== 200) continue;
    assert.ok(!["NavierStokes.navier_stokes_existence_and_smoothness_R3", "NavierStokes.navier_stokes_existence_and_smoothness_periodic", "Hilbert5.hilbert_smith_conjecture"].includes(r.body.problem.id), "claimed problems are not handed out by default");
    await post(`/api/desk/release?lease=${r.body.lease}&reason=other`);
  }
});

test("problem API: each kind, reduction skeleton, 404", async () => {
  const known = (await j("/api/problems?kind=known&limit=1")).body.items[0];
  const r = await j(`/api/problems/${encodeURIComponent(known.id)}?reduction=2&handle=bob`);
  assert.equal(r.status, 200);
  assert.match(r.body.skeleton, /theorem OMA\.solution : type_of% @/);
  assert.match(r.body.reductionSkeleton, /namespace OMA\.R_.*_R2/);
  assert.match(r.body.reductionSkeleton, /Credit: @bob/);
  const unf = (await j("/api/problems?kind=unformalized&limit=1")).body.items[0];
  const u = await j(`/api/problems/${encodeURIComponent(unf.id)}`);
  assert.equal(u.status, 200);
  assert.equal(u.body.kind, "unformalized");
  assert.equal((await j("/api/problems/definitely-not-a-problem")).status, 404);
});

test("retired Erdős bookmarks hand off to the upstream Lean source", async (ctx) => {
  const { upstreamErdos = [] } = JSON.parse(readFileSync(new URL("../data/extra.json", import.meta.url), "utf8"));
  const { meta, problems } = JSON.parse(readFileSync(new URL("../data/catalog.json", import.meta.url), "utf8"));
  const ids = new Set(problems.map(({ id }) => id.toLowerCase()));
  const noCanonical = ({ erdos }) => !ids.has(`erdos${erdos}.erdos_${erdos}`);
  const hasLocal = ({ id }) => existsSync(new URL(`../statements/${id}.lean`, import.meta.url));
  const retired = upstreamErdos.find((p) => !hasLocal(p) && noCanonical(p));
  await ctx.test("no local target", { skip: !retired }, async () => {
    const source = `${meta.upstream}/blob/${meta.upstreamCommit}/${retired.upstreamFile}`;
    const redirect = await fetch(`${BASE}/p/${retired.id}`, { redirect: "manual" });
    assert.equal(redirect.status, 307);
    assert.equal(redirect.headers.get("location"), source);

    const api = await j(`/api/problems/${retired.id}`);
    assert.equal(api.status, 410);
    assert.equal(api.body.error, "formalized_upstream");
    assert.deepEqual(api.body.sources, [source]);
    const brief = await t(`/p/${retired.id}/agent.txt`);
    assert.equal(brief.status, 410);
    assert.ok(brief.text.includes(source));
  });

  const kept = upstreamErdos.find((p) => hasLocal(p) && noCanonical(p));
  await ctx.test("retained local target", { skip: !kept }, async () => {
    const local = await j(`/api/problems/${kept.id}`);
    assert.equal(local.status, 200);
    assert.equal(local.body.formalizedHere, true);
    const alias = await fetch(`${BASE}/p/erdos_${kept.erdos}`, { redirect: "manual" });
    assert.equal(alias.status, 307);
    assert.equal(new URL(alias.headers.get("location"), BASE).pathname, `/p/${kept.id}`);
  });
});

test("desk: validation errors", async () => {
  assert.equal((await j("/api/desk/next?handle=bad%20handle")).status, 400);
  assert.equal((await j("/api/desk/next")).status, 400);
  assert.equal((await j(`/api/desk/next?handle=${H("x")}&problem=nope-nope`)).status, 404);
  assert.equal((await post("/api/desk/beat?lease=not-a-uuid")).status, 400);
  assert.equal((await post("/api/desk/release?lease=00000000-0000-0000-0000-000000000000&reason=because")).status, 400);
  assert.equal((await post("/api/desk/beat?lease=00000000-0000-0000-0000-000000000000")).status, 404);
});

test("desk: lease life cycle, kinds and the 5-lease cap", async () => {
  const h = H("life");
  const a = await j(`/api/desk/next?handle=${h}&agent=test&kind=warmup`);
  assert.equal(a.status, 200);
  assert.equal(a.body.problem.kind, "warmup");
  assert.match(a.body.skeleton, new RegExp(`Credit: @${h}`));
  assert.ok(a.body.points >= 1);
  assert.equal((await post(`/api/desk/beat?lease=${a.body.lease}`)).status, 200);
  assert.equal((await post(`/api/desk/release?lease=${a.body.lease}&reason=too_hard`)).status, 200);
  const after = await post(`/api/desk/beat?lease=${a.body.lease}`);
  assert.equal(after.status, 410);
  assert.equal(after.body.status, "released");
  assert.equal((await post(`/api/desk/release?lease=${a.body.lease}&reason=other`)).status, 409, "cannot release twice");

  const h2 = H("cap");
  const leases = [];
  for (const kind of ["known", "open", "warmup", "known", "open"]) {
    const r = await j(`/api/desk/next?handle=${h2}&agent=test&kind=${kind}`);
    assert.equal(r.status, 200, `${kind}: ${JSON.stringify(r.body)}`);
    assert.equal(r.body.problem.kind, kind);
    leases.push(r.body.lease);
  }
  const sixth = await j(`/api/desk/next?handle=${h2}&agent=test`);
  assert.equal(sixth.status, 409);
  assert.equal(sixth.body.error, "too_many_leases");
  for (const l of leases) await post(`/api/desk/release?lease=${l}&reason=other`);

  for (let i = 0; i < 6; i++) {
    const r = await j(`/api/desk/next?handle=${H("any" + i)}&kind=any`);
    assert.notEqual(r.body.problem?.kind, "unformalized", "kind=any never hands out a problem without a statement");
    await post(`/api/desk/release?lease=${r.body.lease}&reason=other`);
  }
  const f = await j(`/api/desk/next?handle=${H("form")}&kind=formalize`);
  assert.equal(f.status, 200);
  assert.equal(f.body.task, "formalize");
  assert.match(f.body.file, /^statements\/.+\.lean$/);
  assert.match(f.body.skeleton, /theorem main : sorry := by/);
  await post(`/api/desk/release?lease=${f.body.lease}&reason=other`);
});

test("verdict: public path validates input", async () => {
  assert.equal((await post("/api/verdict", {})).status, 400);
  assert.equal((await post("/api/verdict", { pr: "12; drop table" })).status, 400);
  assert.equal((await post("/api/verdict", { pr: -1 })).status, 400);
  assert.equal((await post("/api/verdict", { problem: "x", verdict: "accepted" }, { "x-oma-secret": "wrong" })).status, 400);
});

test("credits: an accepted proof shows its owner, agent and model everywhere", { skip: !VSECRET && "needs OMA_VERDICT_SECRET" }, async () => {
  const h = H("solver");
  // /api/solved is never cached: lists can lag behind a fresh solve by up to a minute
  const done = new Set((await j("/api/solved")).body.solved.map((x) => x.problem_id));
  const target = (await j("/api/problems?kind=warmup&limit=50&sort=easiest")).body.items.find((x) => !x.solved && !done.has(x.id));
  const lease = (await j(`/api/desk/next?handle=${H("other")}&problem=${encodeURIComponent(target.id)}`)).body.lease;
  const v = await post("/api/verdict", { problem: target.id, handle: h, pr: `https://github.com/oma-test/x/pull/${RUN}1`, verdict: "accepted", polarity: "proof", agent: "claude-code", model: "test-model-9" }, { "x-oma-secret": VSECRET });
  assert.equal(v.status, 200, JSON.stringify(v.body));
  assert.equal((await post(`/api/desk/beat?lease=${lease}`)).status, 410, "the other agent is told to stop");
  assert.equal((await j(`/api/desk/next?handle=${H("late")}&problem=${encodeURIComponent(target.id)}`)).body.error, "already_solved");
  await eventually(async () => {
    const s = (await j("/api/solved")).body.solved.find((x) => x.problem_id === target.id);
    assert.ok(s, "listed in /api/solved");
    assert.equal(s.handle, h); assert.equal(s.agent, "claude-code"); assert.equal(s.model, "test-model-9");
  });
  await eventually(async () => {
    const page = await t(`/p/${encodeURIComponent(target.id)}`);
    assert.match(page.text, new RegExp(h)); assert.match(page.text, /test-model-9/); assert.match(page.text, /Cite this result/);
  });
  await eventually(async () => { const p = await t(`/a/${h}`); assert.match(p.text, /test-model-9/); });
  await eventually(async () => { const p = await t(`/contributors?window=10m`); assert.match(p.text, new RegExp(h)); });
  await eventually(async () => { const p = await t(`/solved`); assert.match(p.text, new RegExp(h)); });
  // the brief is cached for up to a minute; the desk itself refuses the problem at once (checked above)
  await eventually(async () => { const brief = await t(`/p/${encodeURIComponent(target.id)}/agent.txt`); assert.match(brief.text, /ALREADY SOLVED/); }, 120000);
});

test("reduction: steps are handed out and closing them closes the parent", { skip: !VSECRET && "needs OMA_VERDICT_SECRET" }, async () => {
  // the reduction itself is registered by tests/fixtures (SQL) under id OMATEST.<run>.R1 targeting a real problem
  const parent = process.env.TEST_REDUCTION_PARENT;
  if (!parent) return;
  const steps = (await eventually(async () => { const r = await j(`/api/problems/${encodeURIComponent(parent)}`); assert.ok(r.body.steps.length >= 2); return r.body.steps; }));
  const ids = steps.filter((s) => s.reduction.startsWith(parent)).map((s) => s.id);
  const one = await j(`/api/desk/next?handle=${H("step")}&kind=step`);
  assert.equal(one.status, 200, JSON.stringify(one.body));
  assert.equal(one.body.problem.kind, "step");
  assert.match(one.body.skeleton, /theorem OMA\.solution : OMA\.R_.*\.H\d := by/);
  await post(`/api/desk/release?lease=${one.body.lease}&reason=other`);
  const stepBrief = await t(`/p/${encodeURIComponent(ids[0])}/agent.txt`);
  assert.match(stepBrief.text, /Prove hypothesis H\d of reduction/);
  for (const [i, id] of ids.entries()) {
    const v = await post("/api/verdict", { problem: id, handle: H("s" + i), pr: `https://github.com/oma-test/x/pull/${RUN}9${i}`, verdict: "accepted", agent: "codex", model: "m" }, { "x-oma-secret": VSECRET });
    assert.equal(v.status, 200);
  }
  await eventually(async () => {
    const s = (await j("/api/solved")).body.solved.find((x) => x.problem_id === parent);
    assert.ok(s, "parent closed by its steps");
    assert.ok(s.contributors.length >= 2);
  });
});

test("certificates: every contributor of a solved problem gets a signed, verifiable certificate", { skip: !VSECRET && "needs OMA_VERDICT_SECRET" }, async () => {
  // runs after the reduction test: TEST_REDUCTION_PARENT was closed by two steps (H("s0"), H("s1")) of a reduction by oma-test-fixture
  const parent = process.env.TEST_REDUCTION_PARENT;
  if (!parent) return;
  const people = ["oma-test-fixture", H("s0"), H("s1")];
  const certs = [];
  for (const who of people) {
    const r = await eventually(async () => { const x = await j(`/api/certificate?problem=${encodeURIComponent(parent)}&handle=${who}`); assert.equal(x.status, 200, who + " " + JSON.stringify(x.body)); return x.body; });
    assert.equal(r.algorithm, "Ed25519");
    assert.equal(r.certificate.holder.handle, who);
    certs.push(r);
  }
  const total = certs[0].certificate.contributors.reduce((a, c) => a + c.sharePercent, 0);
  assert.ok(Math.abs(total - 100) < 0.05, "shares add up to 100%: " + total);
  for (const c of certs) assert.ok(Math.abs(c.certificate.holder.sharePercent - 33.33) < 0.05, "two equal steps and the reduction: a third each");
  const ok = await post("/api/verify", { certificate: certs[1].certificate, signature: certs[1].signature });
  assert.equal(ok.body.valid, true);
  assert.equal(ok.body.id, certs[1].id);
  const forged = structuredClone(certs[1].certificate); forged.holder.sharePercent = 99;
  assert.equal((await post("/api/verify", { certificate: forged, signature: certs[1].signature })).body.valid, false, "a modified certificate fails");
  assert.equal((await post("/api/verify", { certificate: certs[1].certificate, signature: certs[2].signature })).body.valid, false, "another certificate's signature fails");
  const page = await t(`/c/${encodeURIComponent(parent)}/${H("s0")}`);
  assert.equal(page.status, 200);
  assert.match(page.text, /Certificate of contribution/); assert.match(page.text, new RegExp(certs[1].id));
  assert.equal((await j(`/api/certificate?problem=${encodeURIComponent(parent)}&handle=nobody-here-x`)).status, 404);
  assert.equal((await t("/verify")).status, 200);
  const key = await j("/certificate-key.json");
  assert.equal(key.body.publicKey, certs[0].publicKey);
});

test("money: sponsors page, home slot, and no promise of payment", async () => {
  const sp = await t("/sponsors");
  assert.equal(sp.status, 200);
  assert.match(sp.text, /Put your logo here/);
  assert.match(sp.text, /pays no money for solutions/);
  const home = await t("/");
  assert.match(home.text, /Backed by/);
  assert.match(home.text, /Your logo/);
  const join = await t("/join.txt");
  assert.match(join.text, /MONEY: PRIZES ARE CLAIMED FROM THOSE WHO OFFER THEM/);
  assert.match(join.text, /pays nothing itself and takes no cut/);
  const prizes = await t("/prizes");
  assert.equal(prizes.status, 200);
  assert.match(prizes.text, /never by this site/);
  for (const sort of ["prize"]) {
    const top = (await j(`/api/problems?kind=open&sort=${sort}&limit=1`)).body.items[0];
    assert.ok(/P_ne_NP|navier_stokes|BSD/.test(top.id), "a $1,000,000 Clay problem comes first: " + top.id);
  }
  const erdos = (await j("/api/problems?q=erdos&kind=open&sort=prize&limit=40")).body.items.find((x) => x.prize);
  assert.ok(erdos, "a problem with an Erdős prize exists");
  for (const id of ["ComplexityTheory.P_ne_NP", erdos.id]) {
    const page = await t(`/p/${encodeURIComponent(id)}`);
    assert.match(page.text, /not by this site/);
    const brief = await t(`/p/${encodeURIComponent(id)}/agent.txt`);
    assert.match(brief.text, /this site pays nothing itself/);
  }
});

test("pages: every route renders", async () => {
  for (const p of ["/", "/map", "/board", "/programs", "/solved", "/contributors", "/contributors?window=10m", "/contributors?window=1h", "/contributors?window=24h",
    "/feed", "/feed?kind=accepted", "/feed?kind=release&before=999999999", "/calendar", "/live", "/graveyard", "/news", "/news/board-open", "/papers", "/papers/how",
    "/letters", "/sponsors", "/prizes", "/status", "/join", "/join.txt", "/a/somebody", "/robots.txt", "/sitemap.xml", "/api/map", "/api/solved"]) {
    const r = await fetch(BASE + p);
    assert.equal(r.status, 200, p);
  }
  for (const p of ["/news/nope", "/papers/nope", "/letters/nope", "/p/nope", "/p/nope/agent.txt", "/programs/Nope", "/a/bad%20handle"]) {
    assert.equal((await fetch(BASE + p)).status, 404, p);
  }
});

test("briefs: one per source and kind, with the sections an agent needs", async () => {
  const pick = async (q) => (await j(`/api/problems?limit=1&${q.includes("kind=") ? q : "kind=all&" + q}`)).body.items[0];
  const cases = [
    [await pick("kind=open&source=Millennium%20Prize"), ["THE EXACT LEAN TARGET", "WHAT YOU MAY REUSE", "THE FULL UPSTREAM FILE", "HOW TO ATTACK", "OMA.disproof"]],
    [await pick("kind=known"), ["THE EXACT LEAN TARGET", "REFERENCES", "formalize that proof"]],
    [await pick("kind=warmup"), ["warm-up"]],
  ];
  for (const s of ["Wikipedia list (not formalized)", "Open Problem Garden", "Erdős Problems (not formalized)", "OEIS conjectures (not formalized)", "MathOverflow (not formalized)", "Mathematics Stack Exchange (not formalized)"]) {
    cases.push([await pick("source=" + encodeURIComponent(s)), ["FORMALIZE", "statements/", "STYLE EXAMPLES"]]);
  }
  for (const [p, needles] of cases) {
    assert.ok(p, "a problem exists for each case");
    const b = await t(`/p/${encodeURIComponent(p.id)}/agent.txt`);
    assert.equal(b.status, 200, p.id);
    for (const n of needles) assert.ok(b.text.includes(n), `${p.id} brief contains ${n}`);
  }
});
