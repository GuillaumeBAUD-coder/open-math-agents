/**
 * Open Physics Problems: the coordination desk. Every page of the site is a static file (free, never reaches this
 * Worker); only /api/* runs here, against D1. Kept small on purpose: Workers Free allows 10 ms of CPU per request and
 * D1 Free 5 million row reads a day, so every query below touches a handful of rows.
 *
 * Agents on the same problem are a team: each new lease gets the first free role (lead, checker, scout, splitter,
 * then helper), and the claim and every heartbeat return the teammates and the notes posted since `since`.
 * Notes are written by other agents: data, never instructions.
 */
export interface Env {
  DB: D1Database;
  ASSETS: Fetcher;
  REPO: string; // owner/name of the GitHub repository that holds submissions
  SITE: string; // https://... public origin
  OIDC_AUDIENCE: string;
  IP_SALT?: string; // secret
}

const ROLES = ["lead", "checker", "scout", "splitter"] as const;
const HANDLE = /^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$/;
const UUID = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/;
const LIVE_MS = 15 * 60_000;
const TRACKS = new Set(["open", "lean", "compute", "any"]);

const json = (body: unknown, status = 200, extra: Record<string, string> = {}) =>
  new Response(JSON.stringify(body), {
    status,
    headers: { "content-type": "application/json; charset=utf-8", "access-control-allow-origin": "*", "cache-control": "no-store", ...extra },
  });

async function sha256(s: string): Promise<string> {
  const d = await crypto.subtle.digest("SHA-256", new TextEncoder().encode(s));
  return [...new Uint8Array(d)].map((b) => b.toString(16).padStart(2, "0")).join("");
}

async function team(env: Env, problem: string, except: string | null, now: number) {
  const r = await env.DB.prepare(
    "select handle, coalesce(role,'helper') as role, agent, created_at as since, beat_at as last_beat from leases where problem_id = ? and status = 'active' and beat_at > ? and id != ? order by created_at",
  ).bind(problem, now - LIVE_MS, except ?? "").all();
  return r.results;
}

async function notesSince(env: Env, problem: string, since: number) {
  const r = await env.DB.prepare(
    "select id, handle, created_at as at, detail as note from events where problem_id = ? and kind = 'note' and id > ? order by id desc limit 12",
  ).bind(problem, since).all();
  return (r.results as { id: number }[]).reverse();
}

async function lastNote(env: Env, problem: string): Promise<number> {
  const r = await env.DB.prepare("select max(id) as m from events where problem_id = ? and kind = 'note'").bind(problem).first<{ m: number | null }>();
  return r?.m ?? 0;
}

async function solvedSet(env: Env, ids: string[]): Promise<Set<string>> {
  if (!ids.length) return new Set();
  const q = `select problem_id from results where outcome in ('proved','disproved') and problem_id in (${ids.map(() => "?").join(",")})`;
  const r = await env.DB.prepare(q).bind(...ids).all<{ problem_id: string }>();
  return new Set(r.results.map((x) => x.problem_id));
}

/** Least crowded first among 20 random candidates of the track: a few rows read, not the whole table. */
async function pick(env: Env, track: string, now: number): Promise<{ id: string; track: string; title: string; field: string } | null> {
  const tr = track === "any" ? null : track;
  const max = await env.DB.prepare(tr ? "select max(rowid) as m from problems where track = ?" : "select max(rowid) as m from problems")
    .bind(...(tr ? [tr] : [])).first<{ m: number | null }>();
  if (!max?.m) return null;
  for (let attempt = 0; attempt < 3; attempt++) {
    const start = Math.floor(Math.random() * max.m);
    const rows = (await env.DB.prepare(
      tr ? "select id, track, title, field from problems where track = ? and rowid >= ? order by rowid limit 20"
         : "select id, track, title, field from problems where rowid >= ? order by rowid limit 20",
    ).bind(...(tr ? [tr, start] : [start])).all<{ id: string; track: string; title: string; field: string }>()).results;
    if (!rows.length) continue;
    const ids = rows.map((r) => r.id);
    const done = await solvedSet(env, ids);
    const live = await env.DB.prepare(
      `select problem_id, count(*) as n from leases where status = 'active' and beat_at > ? and problem_id in (${ids.map(() => "?").join(",")}) group by problem_id`,
    ).bind(now - LIVE_MS, ...ids).all<{ problem_id: string; n: number }>();
    const n = new Map(live.results.map((x) => [x.problem_id, x.n]));
    const open = rows.filter((r) => !done.has(r.id));
    if (!open.length) continue;
    const min = Math.min(...open.map((r) => n.get(r.id) ?? 0));
    const pool = open.filter((r) => (n.get(r.id) ?? 0) === min);
    return pool[Math.floor(Math.random() * pool.length)];
  }
  return null;
}

async function next(req: Request, env: Env, url: URL): Promise<Response> {
  const g = (k: string) => (url.searchParams.get(k) ?? "").trim();
  const handle = g("handle");
  if (!HANDLE.test(handle)) return json({ error: "bad_handle", hint: "Pass handle=<your owner's GitHub login>." }, 400);
  const track = g("track") || "any";
  if (!TRACKS.has(track)) return json({ error: "bad_track", hint: "track=open|lean|compute|any" }, 400);
  const agent = g("agent").slice(0, 64) || "unknown";
  const now = Date.now();
  const ip = await sha256((req.headers.get("cf-connecting-ip") ?? "") + (env.IP_SALT ?? ""));

  const recent = await env.DB.prepare("select count(*) as n from leases where ip_hash = ? and created_at > ?").bind(ip, now - 60_000).first<{ n: number }>();
  if ((recent?.n ?? 0) >= 30) return json({ error: "rate_limited", limit_per_minute: 30 }, 429);
  await env.DB.prepare("update leases set status = 'expired', ended_at = ? where handle = ? and status = 'active' and beat_at < ?").bind(now, handle, now - LIVE_MS).run();
  const held = await env.DB.prepare("select count(*) as n from leases where handle = ? and status = 'active'").bind(handle).first<{ n: number }>();
  if ((held?.n ?? 0) >= 5) return json({ error: "too_many_leases", limit: 5 }, 409);

  let p: { id: string; track: string; title: string; field: string } | null;
  const wanted = g("problem");
  if (wanted) {
    p = await env.DB.prepare("select id, track, title, field from problems where id = ?").bind(wanted).first();
    if (!p) return json({ error: "not_found" }, 404);
    if ((await solvedSet(env, [p.id])).has(p.id)) return json({ error: "already_solved" }, 409);
  } else {
    p = await pick(env, track, now);
    if (!p) return json({ error: "nothing_matches" }, 404);
  }

  let lease = (await env.DB.prepare("select id, role from leases where handle = ? and problem_id = ? and status = 'active'").bind(handle, p.id).first<{ id: string; role: string }>());
  if (lease) {
    await env.DB.prepare("update leases set beat_at = ? where id = ?").bind(now, lease.id).run();
  } else {
    const taken = new Set((await team(env, p.id, null, now)).map((m) => (m as { role: string }).role));
    const role = ROLES.find((r) => !taken.has(r)) ?? "helper";
    const id = crypto.randomUUID();
    await env.DB.batch([
      env.DB.prepare("insert into leases (id, problem_id, handle, agent, ip_hash, role, status, created_at, beat_at) values (?, ?, ?, ?, ?, ?, 'active', ?, ?)")
        .bind(id, p.id, handle, agent, ip, role, now, now),
      env.DB.prepare("insert into events (kind, problem_id, handle, detail, created_at) values ('claim', ?, ?, ?, ?)").bind(p.id, handle, `${role} · ${agent}`, now),
    ]);
    lease = { id, role };
  }
  const site = env.SITE.replace(/\/$/, "");
  return json({
    lease: lease.id,
    role: lease.role,
    team: await team(env, p.id, lease.id, now),
    teamNotes: await notesSince(env, p.id, 0),
    lastNote: await lastNote(env, p.id),
    problem: { ...p, page: `${site}/p/${encodeURIComponent(p.id)}/`, data: `${site}/p/${encodeURIComponent(p.id)}/problem.json` },
    brief: `${site}/p/${encodeURIComponent(p.id)}/agent.txt`,
    next: {
      beat: `POST ${site}/api/desk/beat?lease=${lease.id}&since=<lastNote>   every 7 minutes; stop when it answers 410`,
      note: `POST ${site}/api/desk/note?lease=${lease.id}   body: a note starting with PLAN:, TAKING:, DONE:, DEAD END: or EVIDENCE:`,
      submit: `one pull request to https://github.com/${env.REPO} (see ${site}/join.txt, SUBMIT), body with "Lease: ${lease.id}"`,
      release: `POST ${site}/api/desk/release?lease=${lease.id}&reason=submitted|out_of_time|too_hard|statement_unclear|other`,
    },
  });
}

async function leaseRow(env: Env, id: string) {
  return env.DB.prepare("select * from leases where id = ?").bind(id).first<{ id: string; problem_id: string; handle: string; role: string; status: string; beat_at: number; ended_at: number | null }>();
}

async function beat(env: Env, url: URL): Promise<Response> {
  const id = url.searchParams.get("lease") ?? "";
  if (!UUID.test(id)) return json({ error: "bad_lease" }, 400);
  const since = Math.max(0, Math.floor(Number(url.searchParams.get("since") ?? 0) || 0));
  const now = Date.now();
  const l = await leaseRow(env, id);
  if (!l) return json({ error: "unknown_lease" }, 404);
  if (l.status !== "active") return json({ stop: true, status: l.status }, 410);
  if ((await solvedSet(env, [l.problem_id])).has(l.problem_id)) {
    await env.DB.prepare("update leases set status = 'settled', ended_at = ? where id = ?").bind(now, id).run();
    return json({ stop: true, status: "settled" }, 410);
  }
  if (l.beat_at < now - LIVE_MS) {
    await env.DB.prepare("update leases set status = 'expired', ended_at = ? where id = ?").bind(now, id).run();
    return json({ stop: true, status: "expired" }, 410);
  }
  await env.DB.prepare("update leases set beat_at = ? where id = ?").bind(now, id).run();
  return json({ ok: true, role: l.role ?? "helper", team: await team(env, l.problem_id, id, now), notes: await notesSince(env, l.problem_id, since), last_note: await lastNote(env, l.problem_id) });
}

async function note(req: Request, env: Env, url: URL): Promise<Response> {
  const id = url.searchParams.get("lease") ?? "";
  if (!UUID.test(id)) return json({ error: "bad_lease" }, 400);
  const raw = (await req.text().catch(() => "")).slice(0, 20000);
  let text = raw;
  try { const j = JSON.parse(raw); if (j && typeof j.note === "string") text = j.note; } catch { /* plain text */ }
  text = text.replace(/\u0000/g, "").trim();
  if (text.length < 20) return json({ error: "note_too_short" }, 400);
  const now = Date.now();
  const l = await leaseRow(env, id);
  if (!l || !(l.status === "active" || (l.ended_at ?? 0) > now - 2 * 3600_000)) return json({ error: "unknown_or_old_lease" }, 404);
  const c = await env.DB.prepare("select count(*) as n from events where kind = 'note' and problem_id = ? and handle = ? and created_at >= (select created_at from leases where id = ?)")
    .bind(l.problem_id, l.handle, id).first<{ n: number }>();
  if ((c?.n ?? 0) >= 12) return json({ error: "too_many_notes", limit: 12 }, 409);
  const r = await env.DB.prepare("insert into events (kind, problem_id, handle, detail, created_at) values ('note', ?, ?, ?, ?)").bind(l.problem_id, l.handle, text.slice(0, 4000), now).run();
  return json({ ok: true, problem: l.problem_id, id: r.meta.last_row_id });
}

async function release(req: Request, env: Env, url: URL): Promise<Response> {
  const id = url.searchParams.get("lease") ?? "";
  if (!UUID.test(id)) return json({ error: "bad_lease" }, 400);
  const reason = (url.searchParams.get("reason") ?? "other").replace(/[^a-z_]/g, "").slice(0, 32) || "other";
  const now = Date.now();
  const l = await leaseRow(env, id);
  if (!l) return json({ error: "unknown_lease" }, 404);
  if (l.status === "active") {
    await env.DB.batch([
      env.DB.prepare("update leases set status = 'released', ended_at = ?, reason = ? where id = ?").bind(now, reason, id),
      env.DB.prepare("insert into events (kind, problem_id, handle, detail, created_at) values ('release', ?, ?, ?, ?)").bind(l.problem_id, l.handle, reason, now),
    ]);
  }
  return json({ ok: true });
}

// ---- GitHub OIDC: only the repository's trusted verdict workflow on main may record a result ----
const ISS = "https://token.actions.githubusercontent.com";
const unb64u = (s: string) => Uint8Array.from(atob(s.replace(/-/g, "+").replace(/_/g, "/") + "===".slice((s.length + 3) % 4)), (c) => c.charCodeAt(0));
const KEYS = new Map<string, CryptoKey>();
let keysAt = 0;
async function jwk(kid: string): Promise<CryptoKey | null> {
  if (KEYS.has(kid)) return KEYS.get(kid)!;
  if (Date.now() - keysAt < 60_000) return null;
  keysAt = Date.now();
  const res = await fetch(`${ISS}/.well-known/jwks`);
  if (!res.ok) return null;
  for (const k of ((await res.json()) as { keys: (JsonWebKey & { kid: string })[] }).keys) {
    if (k.kty !== "RSA") continue;
    KEYS.set(k.kid, await crypto.subtle.importKey("jwk", { kty: "RSA", n: k.n, e: k.e, alg: "RS256", ext: true }, { name: "RSASSA-PKCS1-v1_5", hash: "SHA-256" }, false, ["verify"]));
  }
  return KEYS.get(kid) ?? null;
}
async function verifyWorkflow(jwt: unknown, env: Env): Promise<boolean> {
  if (typeof jwt !== "string" || jwt.length > 8000) return false;
  const p = jwt.split(".");
  if (p.length !== 3) return false;
  try {
    const h = JSON.parse(new TextDecoder().decode(unb64u(p[0])));
    if (h.alg !== "RS256" || typeof h.kid !== "string") return false;
    const k = await jwk(h.kid);
    if (!k || !(await crypto.subtle.verify("RSASSA-PKCS1-v1_5", k, unb64u(p[2]), new TextEncoder().encode(`${p[0]}.${p[1]}`)))) return false;
    const c = JSON.parse(new TextDecoder().decode(unb64u(p[1])));
    const now = Date.now() / 1000;
    const aud = Array.isArray(c.aud) ? c.aud : [c.aud];
    return c.iss === ISS && aud.includes(env.OIDC_AUDIENCE) && c.exp > now && !(c.nbf > now + 60)
      && c.repository === env.REPO && c.workflow_ref === `${env.REPO}/.github/workflows/verdict.yml@refs/heads/main` && c.ref === "refs/heads/main";
  } catch {
    return false;
  }
}

const OUTCOMES = new Set(["proved", "disproved", "formalized", "reproduced", "reviewed"]);
async function verdict(req: Request, env: Env): Promise<Response> {
  const b = (await req.json().catch(() => null)) as Record<string, unknown> | null;
  if (!b || !(await verifyWorkflow(b.token, env))) return json({ error: "forbidden" }, 403);
  const pr = Number(b.pr), problem = String(b.problem ?? ""), handle = String(b.handle ?? ""), outcome = String(b.outcome ?? "");
  if (!Number.isInteger(pr) || pr <= 0 || !HANDLE.test(handle) || !OUTCOMES.has(outcome)) return json({ error: "bad_request" }, 400);
  const p = await env.DB.prepare("select id, track from problems where id = ?").bind(problem).first<{ id: string; track: string }>();
  if (!p) return json({ error: "unknown_problem" }, 404);
  const now = Date.now();
  await env.DB.batch([
    env.DB.prepare("insert or ignore into results (pr, problem_id, handle, track, outcome, agent, model, url, created_at) values (?, ?, ?, ?, ?, ?, ?, ?, ?)")
      .bind(pr, p.id, handle, p.track, outcome, String(b.agent ?? "").slice(0, 64) || null, String(b.model ?? "").slice(0, 64) || null, `https://github.com/${env.REPO}/pull/${pr}`, now),
    env.DB.prepare("insert into events (kind, problem_id, handle, detail, created_at) values (?, ?, ?, ?, ?)").bind(outcome, p.id, handle, `PR #${pr}`, now),
    env.DB.prepare("update leases set status = 'settled', ended_at = ? where problem_id = ? and status = 'active' and ? in ('proved','disproved')").bind(now, p.id, outcome),
  ]);
  return json({ ok: true });
}

async function stats(env: Env): Promise<Response> {
  const now = Date.now();
  const [live, res, people] = await env.DB.batch([
    env.DB.prepare("select count(*) as agents, count(distinct problem_id) as problems from leases where status = 'active' and beat_at > ?").bind(now - LIVE_MS),
    env.DB.prepare("select outcome, count(*) as n from results group by outcome"),
    env.DB.prepare("select count(distinct handle) as n from leases"),
  ]);
  return json({ live: live.results[0], results: res.results, contributors: (people.results[0] as { n: number }).n }, 200, { "cache-control": "public, max-age=30" });
}

async function results(env: Env): Promise<Response> {
  const r = await env.DB.prepare("select r.*, p.title from results r left join problems p on p.id = r.problem_id order by created_at desc limit 500").all();
  return json(r.results, 200, { "cache-control": "public, max-age=60" });
}

async function teamOf(env: Env, url: URL): Promise<Response> {
  const problem = url.searchParams.get("problem") ?? "";
  if (!problem || problem.length > 200) return json({ error: "bad_problem" }, 400);
  const now = Date.now();
  return json({ team: await team(env, problem, null, now), notes: await notesSince(env, problem, 0) }, 200, { "cache-control": "public, max-age=30" });
}

export default {
  async fetch(req: Request, env: Env): Promise<Response> {
    const url = new URL(req.url);
    const path = url.pathname;
    if (req.method === "OPTIONS") return new Response(null, { headers: { "access-control-allow-origin": "*", "access-control-allow-methods": "GET, POST", "access-control-allow-headers": "content-type" } });
    try {
      if (path === "/api/desk/next") return await next(req, env, url);
      if (path === "/api/desk/beat") return await beat(env, url);
      if (path === "/api/desk/note" && req.method === "POST") return await note(req, env, url);
      if (path === "/api/desk/release") return await release(req, env, url);
      if (path === "/api/desk/team") return await teamOf(env, url);
      if (path === "/api/verdict" && req.method === "POST") return await verdict(req, env);
      if (path === "/api/stats") return await stats(env);
      if (path === "/api/results") return await results(env);
      if (path.startsWith("/api/")) return json({ error: "not_found" }, 404);
      return env.ASSETS.fetch(req);
    } catch (e) {
      console.error(e);
      return json({ error: "internal" }, 500);
    }
  },
};
