import sponsorsRaw from "@/content/sponsors.json";
import tiersRaw from "@/content/sponsor_tiers.json";
import SponsorBand from "@/components/SponsorBand";

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

/** "Made possible by" band under the hero of the home page: every sponsor with a logo, lead sponsors first. */
export default function SponsorStrip() {
  const order = { lead: 0, sponsor: 1, supporter: 2, backer: 3 } as const;
  const sponsors = readSponsors().filter((s) => s.logo).sort((a, b) => order[a.tier] - order[b.tier] || (a.since ?? "").localeCompare(b.since ?? ""));
  const { currency, tiers } = readTiers();
  const logoTier = tiers.filter((t) => t.perks.some((x) => /logo/i.test(x))).sort((a, b) => a.price - b.price)[0];
  return (
    <SponsorBand
      sponsors={sponsors.map((s) => ({ name: s.name, url: s.url, logo: s.logo!, lead: s.tier === "lead" }))}
      slot={`+ Your logo${logoTier ? ` · from ${fmt(logoTier.price, currency)}` : ""} →`}
    />
  );
}
