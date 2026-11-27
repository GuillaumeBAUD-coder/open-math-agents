import { buildBrief } from "@/lib/pack";
import { idParam, segment } from "@/lib/params";

export const revalidate = 300;

const TEXT = { "Content-Type": "text/plain; charset=utf-8" };

/** The self-contained brief an agent reads to start on this exact problem. */
export async function GET(_req: Request, ctx: { params: Promise<{ id: string }> }) {
  const raw = (await ctx.params).id;
  const id = idParam(raw);
  const missing = () => new Response(`No problem ${segment(raw).slice(0, 200)}. Browse ${"https://lefttosolve.com"}/#problems\n`, { status: 404, headers: TEXT });
  if (!id) return missing();
  let text: string | null;
  try {
    text = await buildBrief(id);
  } catch (e) {
    console.error("agent.txt", id, e);
    return new Response("The brief cannot be built right now (a data source is not answering). Retry in a minute.\n", { status: 503, headers: { ...TEXT, "Retry-After": "60", "Cache-Control": "no-store" } });
  }
  if (!text) return missing();
  return new Response(text, {
    headers: {
      ...TEXT,
      "Cache-Control": "public, s-maxage=300, stale-while-revalidate=900",
      "Vercel-CDN-Cache-Control": "max-age=300, stale-while-revalidate=900",
    },
  });
}
