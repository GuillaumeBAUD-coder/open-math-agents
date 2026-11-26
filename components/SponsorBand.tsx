"use client";
import { useEffect, useRef, useState } from "react";
import Link from "@/components/Link";

export type BandSponsor = { name: string; url?: string; logo: string; lead?: boolean };

/**
 * "Made possible by": every sponsor's logo in one band under the hero. The logos stand still while they fit; once they
 * overflow the band they scroll slowly in a loop (paused on hover, never with reduced motion).
 */
export default function SponsorBand({ sponsors, slot }: { sponsors: BandSponsor[]; slot: string }) {
  const box = useRef<HTMLSpanElement>(null);
  const group = useRef<HTMLSpanElement>(null);
  const [moving, setMoving] = useState(false);
  const [dur, setDur] = useState(30);

  useEffect(() => {
    const check = () => {
      if (!box.current || !group.current) return;
      const w = group.current.scrollWidth;
      const fits = w <= box.current.clientWidth + 1;
      setMoving(!fits && !window.matchMedia("(prefers-reduced-motion: reduce)").matches);
      setDur(Math.max(20, Math.round(w / 45))); // about 45 px per second, whatever the number of logos
    };
    check();
    const ro = new ResizeObserver(check);
    if (box.current) ro.observe(box.current);
    if (group.current) ro.observe(group.current);
    return () => ro.disconnect();
  }, [sponsors.length]);

  const logos = (hidden: boolean) =>
    sponsors.map((s) => {
      // eslint-disable-next-line @next/next/no-img-element
      const img = <img src={s.logo} alt={hidden ? "" : s.name} className={s.lead ? "lead" : ""} />;
      return s.url
        ? <a key={s.name} href={s.url} target="_blank" rel="noreferrer sponsored" title={s.name} tabIndex={hidden ? -1 : undefined}>{img}</a>
        : <span key={s.name} title={s.name}>{img}</span>;
    });

  return (
    <section className="backed" aria-label="Sponsors">
      <div className="wrap backed-in">
        <span className="k">Made possible by</span>
        <span className={`marks${moving ? " moving" : ""}`} ref={box}>
          <span className="track" style={moving ? { animationDuration: `${dur}s` } : undefined}>
            <span className="group" ref={group}>{logos(false)}</span>
            {moving && <span className="group" aria-hidden="true">{logos(true)}</span>}
          </span>
        </span>
        <Link href="/sponsors#tiers" className="slot">{slot}</Link>
      </div>
    </section>
  );
}
