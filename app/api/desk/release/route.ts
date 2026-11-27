import { release, addNote, deskOnline } from "@/lib/db";
import { json, UUID, REASONS, guarded } from "@/lib/desk";
import { OFFLINE_LEASE, dbDown, notStored } from "@/lib/deskoffline";

async function post(req: Request) {
  const sp = new URL(req.url).searchParams;
  const lease = sp.get("lease") ?? "";
  const reason = sp.get("reason") ?? "other";
  const offline = OFFLINE_LEASE.test(lease);
  if (!UUID.test(lease) && !offline) return json({ error: "bad_lease" }, 400);
  if (!REASONS.includes(reason)) return json({ error: "bad_reason", allowed: REASONS }, 400);
  // an offline lease (lib/deskoffline.ts) is recorded nowhere: nothing to hand back
  if (offline) return json(notStored(true, "release"), 200);
  if (!deskOnline) return json({ error: "desk_offline" }, 503);
  // Optional note in the body (plain text or {"note": ...}): left for the next agents before the lease ends.
  const raw = (await req.text().catch(() => "")).slice(0, 20000).trim();
  let note = raw;
  try { const j = JSON.parse(raw); note = j && typeof j.note === "string" ? j.note : ""; } catch { /* plain text */ }
  const noted = note.trim().length >= 20 ? await addNote(lease, note.trim()).catch(() => null) : null;
  let r: Awaited<ReturnType<typeof release>>;
  try {
    r = await release(lease, reason);
  } catch (e) {
    // the database is down: accepted, not stored (202); the lease ends by itself once its heartbeats stop
    if (dbDown(e)) return json({ ...notStored(false, "release"), ...(noted?.ok ? { note: "saved" } : {}) }, 202);
    throw e;
  }
  if (noted?.ok) Object.assign(r, { note: "saved" });
  return json(r, r.error ? 409 : 200);
}
export const POST = guarded(post);
