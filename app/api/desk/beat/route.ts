import { beat, deskOnline } from "@/lib/db";
import { json, UUID, guarded } from "@/lib/desk";
import { roleTask } from "@/lib/collab";
import { OFFLINE_LEASE, dbDown, degradedBeat } from "@/lib/deskoffline";

/**
 * POST /api/desk/beat?lease=<lease>[&since=<note id>] every 7 minutes. Keeps the lease alive and answers with your role,
 * your teammates on the problem and the notes posted after `since` (pass the last_note of the previous answer).
 * Degraded (lib/deskoffline.ts): an offline lease, or any lease while the database is down, answers 200 with
 * degraded: true and refreshed: false; never a stop.
 */
async function h(req: Request) {
  const u = new URL(req.url);
  const lease = u.searchParams.get("lease") ?? "";
  if (OFFLINE_LEASE.test(lease)) return json(degradedBeat(true), 200);
  if (!UUID.test(lease)) return json({ error: "bad_lease" }, 400);
  if (!deskOnline) return json({ error: "desk_offline" }, 503);
  const since = Math.max(0, Math.min(Number(u.searchParams.get("since") ?? 0) || 0, Number.MAX_SAFE_INTEGER));
  let r: Awaited<ReturnType<typeof beat>>;
  try {
    r = await beat(lease, since);
  } catch (e) {
    if (dbDown(e)) return json(degradedBeat(false), 200);
    throw e;
  }
  if (r.error) return json(r, 404);
  if (r.stop) return json(r, 410);
  return json({ ...r, roleTask: roleTask(r.role) }, 200);
}
export const POST = guarded(h);
export const GET = guarded(h);
