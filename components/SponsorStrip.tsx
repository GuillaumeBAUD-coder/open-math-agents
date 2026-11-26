import sponsorsRaw from "@/content/sponsors.json";
import tiersRaw from "@/content/sponsor_tiers.json";
import Link from "@/components/Link";

export type Sponsor = { name: string; url?: string; logo?: string; tier: "backer" | "supporter" | "sponsor" | "lead"; since?: string; message?: string };
export type Tier = { id: string; name: string; price: number; period: string; perks: string[] };

export function readSponsors(): Sponsor[] {
  return sponsorsRaw as Sponsor[];
}
export function readTiers(): { currency: string; tiers: Tier[] } {
  return tiersRaw as { currency: string; tiers: Tier[] };
}
/** Payment page for a tier: NEXT_PUBLIC_SPONSOR_URL_<ID>, else NEXT_PUBLIC_SPONSOR_URL, else the sponsors page. */
export function tierUrl(id: string) {
  return process.env[`NEXT_PUBLIC_SPONSOR_URL_${id.toUpperCase()}`] ?? process.env.NEXT_PUBLIC_SPONSOR_URL ?? "/sponsors#tiers";
}
const fmt = (n: number, c: string) => n.toLocaleString("en-US", { style: "currency", currency: c, maximumFractionDigits: 0 });

/** "Backed by" strip for the home page: logos of lead sponsors and sponsors, then a "your logo" slot. */
export default function SponsorStrip() {
  const sponsors = readSponsors().filter((s) => (s.tier === "sponsor" || s.tier === "lead") && s.logo);
  const { currency, tiers } = readTiers();
  const logoTier = tiers.filter((t) => t.perks.some((x) => /logo/i.test(x))).sort((a, b) => a.price - b.price)[0];
  const ordered = [...sponsors.filter((s) => s.tier === "lead"), ...sponsors.filter((s) => s.tier === "sponsor")];
  return (
    <div className="sponsors">
      <span className="k">Backed by</span>
      {ordered.map((s) => (
        <a key={s.name} href={s.url ?? "/sponsors"} target={s.url ? "_blank" : undefined} rel="noreferrer sponsored" title={s.name} className={s.tier === "lead" ? "lead" : ""}>
          {/* eslint-disable-next-line @next/next/no-img-element */}
          <img src={s.logo} alt={s.name} />
        </a>
      ))}
      <Link href="/sponsors" className="slot">+ Your logo and website{logoTier ? ` · from ${fmt(logoTier.price, currency)}` : ""} →</Link>
    </div>
  );
}
