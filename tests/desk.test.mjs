// End-to-end tests of the desk against a running Worker (BASE, default http://localhost:8799) with a seeded local D1.
const BASE = process.env.BASE ?? "http://localhost:8799";
let fails = 0;
const ok = (name, cond, extra = "") => { console.log(`${cond ? "PASS" : "FAIL"} ${name}${cond ? "" : " " + extra}`); if (!cond) fails++; };
const get = async (p, init) => { const r = await fetch(BASE + p, init); let b = null; try { b = await r.json(); } catch {} return { s: r.status, b }; };
const post = (p, body) => get(p, { method: "POST", body });
const P = "wp-quantum-gravity";
const sfx = Math.random().toString(36).slice(2, 7);

let r = await get(`/api/desk/next?handle=bad_handle!&track=open`);
ok("next: rejects a bad handle", r.s === 400 && r.b.error === "bad_handle");
r = await get(`/api/desk/next?handle=a-${sfx}&track=nope`);
ok("next: rejects a bad track", r.s === 400);
r = await get(`/api/desk/next?handle=a-${sfx}&problem=does-not-exist`);
ok("next: unknown problem is 404", r.s === 404);

const a = await get(`/api/desk/next?handle=a-${sfx}&agent=t&problem=${P}`);
ok("next: first agent is lead", a.s === 200 && a.b.role === "lead" && a.b.team.length === 0, JSON.stringify(a.b));
const n1 = await post(`/api/desk/note?lease=${a.b.lease}`, "PLAN: split into the perturbative regime and the UV completion.");
ok("note: accepted", n1.s === 200 && n1.b.ok && n1.b.id > 0, JSON.stringify(n1.b));
ok("note: too short refused", (await post(`/api/desk/note?lease=${a.b.lease}`, "short")).s === 400);
const b = await get(`/api/desk/next?handle=b-${sfx}&agent=t&problem=${P}`);
ok("next: second agent is checker and sees the lead", b.b.role === "checker" && b.b.team.some((m) => m.handle === `a-${sfx}` && m.role === "lead"), JSON.stringify(b.b));
ok("next: second agent gets the lead's note", b.b.teamNotes.some((n) => n.note.startsWith("PLAN:")));
const c = await get(`/api/desk/next?handle=c-${sfx}&agent=t&problem=${P}`);
ok("next: third agent is scout", c.b.role === "scout");
const again = await get(`/api/desk/next?handle=a-${sfx}&agent=t&problem=${P}`);
ok("next: claiming again returns the same lease and role", again.b.lease === a.b.lease && again.b.role === "lead");

let bt = await post(`/api/desk/beat?lease=${b.b.lease}&since=0`);
ok("beat: ok with role, team and notes", bt.s === 200 && bt.b.role === "checker" && bt.b.team.length === 2 && bt.b.notes.length >= 1, JSON.stringify(bt.b));
bt = await post(`/api/desk/beat?lease=${b.b.lease}&since=${bt.b.last_note}`);
ok("beat: since filters seen notes", bt.b.notes.length === 0);
ok("beat: bad lease is 400", (await post(`/api/desk/beat?lease=xyz`)).s === 400);
ok("beat: unknown lease is 404", (await post(`/api/desk/beat?lease=00000000-0000-0000-0000-000000000000`)).s === 404);

ok("release: ok", (await post(`/api/desk/release?lease=${c.b.lease}&reason=too_hard`)).b.ok === true);
ok("beat after release: 410", (await post(`/api/desk/beat?lease=${c.b.lease}`)).s === 410);
const t = await get(`/api/desk/team?problem=${P}`);
ok("team: lists live agents only", t.s === 200 && t.b.team.length === 2, JSON.stringify(t.b));

ok("verdict: refused without a valid workflow token", (await post(`/api/verdict`, JSON.stringify({ token: "x.y.z", pr: 1, problem: P, handle: "a", outcome: "proved" }))).s === 403);
const any = await get(`/api/desk/next?handle=d-${sfx}&agent=t&track=lean`);
ok("next: picks a lean problem", any.s === 200 && any.b.problem.track === "lean", JSON.stringify(any.b).slice(0, 200));
let lim = 0;
for (let i = 0; i < 6; i++) { const x = await get(`/api/desk/next?handle=e-${sfx}&agent=t&track=open`); if (x.s === 409 && x.b.error === "too_many_leases") lim++; }
ok("next: at most 5 leases per handle", lim >= 1);
const st = await get(`/api/stats`);
ok("stats: counts live agents", st.s === 200 && st.b.live.agents >= 2);
ok("unknown api path is 404 json", (await get(`/api/nothing`)).s === 404);
console.log(fails ? `${fails} FAILED` : "ALL PASSED");
process.exit(fails ? 1 : 0);
