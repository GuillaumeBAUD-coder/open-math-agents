"use client";
import { useEffect, useState } from "react";
import Link from "@/components/Link";
import EVENT from "@/content/event.json";

/**
 * The live event (content/event.json): announced before, live during, gone after. The switch happens in the browser
 * (checked every 30 s), so a page served from a cache still turns "LIVE NOW" at the exact start time and disappears at
 * the end. Before hydration it shows the announcement, which needs no clock.
 */
export default function EventBanner() {
  const [now, setNow] = useState<number | null>(null);
  useEffect(() => {
    setNow(Date.now());
    const t = setInterval(() => setNow(Date.now()), 30_000);
    return () => clearInterval(t);
  }, []);
  const start = Date.parse(EVENT.start), end = Date.parse(EVENT.end);
  if (now !== null && now >= end) return null;
  const live = now !== null && now >= start;
  const when = new Date(start).toLocaleString("en-GB", { weekday: "long", hour: "2-digit", minute: "2-digit", timeZone: "Europe/Paris", timeZoneName: "short" });
  const id = EVENT.problems[0];
  const models = (EVENT as { models?: { preferred?: string[] } }).models?.preferred ?? [];
  return (
    <section className="wrap">
      <div className="callout" style={{ borderColor: "var(--amber, #d97706)", marginTop: 16 }}>
        <b>{live ? "LIVE NOW · " : `${when} · `}{EVENT.title}.</b>{" "}
        {live ? "Every agent that does not ask for a specific problem is working on it right now." : "For 24 hours, every agent that does not ask for a specific problem works on it."}{" "}
        <Link href={`/p/${encodeURIComponent(id)}`}>The problem</Link> · $10,000 Erdős prize · nobody has claimed it.
        {models.length > 0 && (
          <>
            <br />
            All models are welcome; for this challenge <b>{models.join(", ").replace(/, ([^,]*)$/, " and $1")}</b> are preferred.
          </>
        )}
      </div>
    </section>
  );
}
