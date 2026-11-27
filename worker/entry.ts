/**
 * Worker entry: vinext's handler, plus a page cache in the Cache API of each data centre (free, not billed; unlike
 * Workers Cache, which bills every request). Only plain GET page requests are cached (no API, no RSC navigation
 * request, no authorization), only when vinext marks the page cacheable (s-maxage), fresh for at most that long and
 * then served stale while it is re-rendered in the background (see staleFor).
 * A cached page costs about a millisecond of CPU instead of a full render.
 */
import handler from "vinext/server/fetch-handler";
import clientAssets from "virtual:vite-rsc/assets-manifest";
export * from "vinext/server/fetch-handler";

type ExecutionContext = { waitUntil(p: Promise<unknown>): void; passThroughOnException?(): void };
type Handler = { fetch(req: Request, env: unknown, ctx: ExecutionContext): Promise<Response> };
const inner = handler as unknown as Handler;
const SKIP = /^\/(api|_next|__|cdn-cgi)(\/|$)/;
const ORIGIN = "https://lefttosolve.com";
// Fingerprint of the client build: every script and stylesheet a page links to (hashed file names). It is part of the
// cache key, because a deploy that changes those files removes the old ones (404): a page stored before it would load
// no script and possibly no styles. A deploy that leaves them as they were (catalogue, proofs) keeps the stored pages.
const BUILD = (() => {
  const s = JSON.stringify(clientAssets);
  let h = 2166136261;
  for (let i = 0; i < s.length; i++) h = Math.imul(h ^ s.charCodeAt(i), 16777619) >>> 0;
  return h.toString(36);
})();
const NO_CACHE_HEADERS = ["rsc", "next-router-state-tree", "next-router-prefetch", "next-router-segment-prefetch", "next-url", "next-action",
  "x-vinext-interception-context", "x-vinext-interception-id", "x-vinext-mounted-slots", "x-vinext-rsc-render-mode",
  "x-vinext-rsc-state-fingerprint", "authorization", "x-oma-secret"];

// The revalidate of each ISR route (app/**/page.tsx): vinext marks a page's first render in an isolate no-store, but
// it is the same page; storing it at once saves every other isolate of the data centre a render.
const ROUTE_TTL: [RegExp, number][] = [
  [/^\/$/, 60], [/^\/solved(\/(known|warmup|step))?$/, 60], [/^\/live$/, 30], [/^\/feed$/, 30], [/^\/board$/, 120],
  [/^\/p\/[^/]+\/agent\.txt$/, 300], [/^\/p\/[^/]+$/, 120], [/^\/a\/[^/]+$/, 120],
  [/^\/(contributors|graveyard|prizes|programs)(\/[^/]+)?$/, 300], [/^\/(calendar|c\/[^/]+\/[^/]+)$/, 600],
];
const routeTtl = (path: string) => ROUTE_TTL.find(([re]) => re.test(path))?.[1] ?? 0;

// Crawlers (search engines, AI crawlers, SEO tools) read the same pages over and over and do not need live counts to
// the minute: they get their own copy of each page, kept 6 hours. People always get the normal copy (at most a minute
// or two old), so nothing changes for them; the crawlers stop costing a full render per visit.
const CRAWLER = /(?<!cu)bot\b|bot\/|crawler|spider|slurp|bytespider|petalbot|facebookexternalhit|ia_archiver|semrush|ahrefs|gptbot|claudebot|perplexity|ccbot|amazonbot|applebot|elevenlabs/i;
const CRAWLER_TTL = 6 * 3600;

function eligible(req: Request, url: URL): boolean {
  if (req.method !== "GET" || SKIP.test(url.pathname) || url.searchParams.has("_rsc")) return false;
  const h = req.headers;
  // Every header vinext varies its response on (its Vary list), plus actions and credentials: a request carrying any
  // of them is rendered for itself and never stored, so nobody can plant a variant in the shared copy.
  for (const k of NO_CACHE_HEADERS) if (h.has(k)) return false;
  return true;
}

function secure(res: Response): Response {
  const type = res.headers.get("content-type") ?? "";
  if (!type.startsWith("text/html")) return res;
  const r = new Response(res.body, res);
  // No framing by other sites (clickjacking) and no full URLs leaked to other sites in Referer.
  r.headers.set("x-frame-options", "SAMEORIGIN");
  r.headers.set("content-security-policy", "frame-ancestors 'self'");
  r.headers.set("referrer-policy", "strict-origin-when-cross-origin");
  return r;
}

export default {
  async fetch(req: Request, env: unknown, ctx: ExecutionContext): Promise<Response> {
    // Last resort: nothing the site answers is a 500. vinext turns an exception a route did not catch into an empty
    // 500; here it becomes a 503 with Retry-After (agents' tools and webhooks retry it), logged. Every other status,
    // and every successful answer, passes through unchanged.
    let res: Response;
    try {
      res = await route(req, env, ctx);
    } catch (e) {
      console.error("worker: uncaught", req.method, new URL(req.url).pathname, e);
      return unavailable(req);
    }
    if (res.status === 500) {
      console.error("worker: 500 answered as 503", req.method, new URL(req.url).pathname);
      ctx.waitUntil(Promise.resolve(res.body?.cancel()).catch(() => undefined));
      return unavailable(req);
    }
    return secure(res);
  },
};

const DOWN_HTML = `<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Left to Solve · back in a moment</title><style>body{font:16px/1.5 system-ui,sans-serif;max-width:560px;margin:15vh auto;padding:0 16px;color:#111;background:#fff}
@media (prefers-color-scheme:dark){body{color:#eee;background:#111}a{color:#9cf}}</style></head>
<body><h1>Back in a moment</h1><p>This page could not be built just now: one of the site's data sources is not answering.
Nothing is lost. Reload in half a minute, or go to the <a href="/">home page</a>.</p></body></html>`;

/** 503 with Retry-After: JSON for the API, a short page for browsers, plain text for agents and everything else. */
function unavailable(req: Request): Response {
  const path = new URL(req.url).pathname;
  const headers: Record<string, string> = { "Retry-After": "30", "Cache-Control": "no-store", "Access-Control-Allow-Origin": "*" };
  const head = req.method === "HEAD";
  if (path.startsWith("/api/")) {
    return new Response(head ? null : JSON.stringify({ error: "temporarily_unavailable", hint: "Retry in 30 seconds." }), { status: 503, headers: { ...headers, "Content-Type": "application/json" } });
  }
  const html = (req.headers.get("accept") ?? "").includes("text/html") && !req.headers.has("rsc") && !path.endsWith(".txt");
  if (html) return new Response(head ? null : DOWN_HTML, { status: 503, headers: { ...headers, "Content-Type": "text/html; charset=utf-8" } });
  return new Response(head ? null : "Temporarily unavailable: retry in 30 seconds.\n", { status: 503, headers: { ...headers, "Content-Type": "text/plain; charset=utf-8" } });
}

// Pages that read nothing but their query string (no cookies, no headers): vinext renders them as dynamic (private,
// no-store), yet one URL is one page for everybody, so they are stored like the others under their route's TTL (the
// key includes the query). A page added here must never read cookies() or headers().
const SEARCH_ONLY = /^\/(contributors|feed)$/;

// Stale-while-revalidate, as Next's ISR does: a stored page is fresh for its TTL; after that, for a while longer, it
// is still served at once (x-page-cache: STALE) while one background render per isolate replaces it. The next visitor
// gets the new copy; nobody waits for a full render because the copy just expired. Past the stale window the entry is
// gone and the page is rendered while the visitor waits, as before.
const FRESH_UNTIL = "x-page-cache-fresh-until";
const staleFor = (ttl: number) => Math.min(3600, Math.max(300, ttl * 10));
const refreshing = new Set<string>();

function store(req: Request, url: URL, res: Response, bot: boolean, key: Request, cache: Cache, ctx: ExecutionContext): boolean {
  const m = /s-maxage=(\d+)/.exec(res.headers.get("cache-control") ?? "")
    ?? ((res.headers.get("x-vinext-cache") === "MISS" || SEARCH_ONLY.test(url.pathname)) && routeTtl(url.pathname) ? ["", String(routeTtl(url.pathname))] : null);
  const type = res.headers.get("content-type") ?? "";
  const vary = (res.headers.get("vary") ?? "").toLowerCase().split(",").map((v) => v.trim()).filter(Boolean);
  const variant = vary.includes("*") || vary.some((v) => v !== "accept-encoding" && req.headers.has(v));
  if (res.status !== 200 || !m || variant || res.headers.has("set-cookie") || !/^text\/(html|plain)/.test(type)) return false;
  const ttl = bot ? CRAWLER_TTL : Math.min(Number(m[1]), 600);
  if (!(ttl > 0)) return false;
  const copy = new Response(res.clone().body, res);
  copy.headers.set("cache-control", `public, max-age=${ttl + staleFor(ttl)}`);
  copy.headers.set(FRESH_UNTIL, String(Date.now() + ttl * 1000));
  copy.headers.delete("vary");
  copy.headers.delete("x-page-cache");
  ctx.waitUntil(cache.put(key, copy).catch(() => undefined));
  return true;
}

async function route(req: Request, env: unknown, ctx: ExecutionContext): Promise<Response> {
  {
    const url = new URL(req.url);
    const cache = (globalThis as unknown as { caches?: { default?: Cache } }).caches?.default;
    if (!cache || !eligible(req, url)) return inner.fetch(req, env, ctx);
    const bot = CRAWLER.test(req.headers.get("user-agent") ?? "");
    const key = new Request(`${ORIGIN}/${bot ? "__html_bot" : "__html"}/${BUILD}${url.pathname}${url.search}`);
    const hit = await cache.match(key).catch(() => undefined);
    if (hit) {
      const until = Number(hit.headers.get(FRESH_UNTIL) ?? 0);
      const stale = until > 0 && Date.now() > until;
      if (stale && !refreshing.has(key.url)) {
        refreshing.add(key.url);
        const again = new Request(req.url, { method: "GET", headers: req.headers });
        ctx.waitUntil(inner.fetch(again, env, ctx)
          .then((res) => { store(again, url, res, bot, key, cache, ctx); return res.body?.cancel(); })
          .catch(() => undefined)
          .finally(() => refreshing.delete(key.url)));
      }
      const r = new Response(hit.body, hit);
      r.headers.set("cache-control", "public, max-age=0, must-revalidate");
      r.headers.set("x-page-cache", stale ? "STALE" : "HIT");
      r.headers.delete(FRESH_UNTIL);
      return r;
    }
    const res = await inner.fetch(req, env, ctx);
    store(req, url, res, bot, key, cache, ctx);
    return res;
  }
}
