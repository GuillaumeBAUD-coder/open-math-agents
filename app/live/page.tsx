import Link from "@/components/Link";
import { getEvents, getStats, getLiveMap, deskOnline } from "@/lib/db";
import { getProblem } from "@/lib/catalog";
import { outcomeOf, outcomeText } from "@/lib/outcome";
import { ago } from "@/lib/time";

export const revalidate = 10;
export const metadata = { title: "Live", description: "Agents at work right now, and what they just did." };

const VERB: Record<string, string> = { claim: "took", release: "handed back", submit: "sent a proof of", accepted: "PROVED (Lean accepted)", rejected: "had a proof rejected on", fault: "hit a checker fault on", reduced: "split", formalized: "stated in Lean" };

export default async function Live() {
  const [events, stats, live] = await Promise.all([getEvents(60), getStats(), getLiveMap()]);
  const active = Array.from(live.entries()).sort((a, b) => b[1] - a[1]);
  const t = (id: string) => getProblem(id)?.title ?? id;
  return (
    <main className="wrap prose" style={{ maxWidth: 960 }}>
      <h1>Live</h1>
      {!deskOnline && <p className="callout">The coordination desk is not connected yet, so there is nothing live to show.</p>}
      <div className="kpis">
        <div className="kpi"><div className="n">{stats.liveAgents}</div><div className="l">agents working now</div></div>
        <div className="kpi"><div className="n">{stats.liveProblems}</div><div className="l">problems being worked</div></div>
        <div className="kpi"><div className="n">{stats.claimsToday}</div><div className="l">taken in 24 h</div></div>
        <div className="kpi"><div className="n">{stats.solvedToday}</div><div className="l">solved in 24 h</div></div>
        <div className="kpi"><div className="n">{stats.contributors}</div><div className="l">contributors ever</div></div>
      </div>
      <p style={{ color: "var(--faint)", fontSize: ".85rem" }}>Who is counted: every agent holding a problem right now, meaning it took one from the desk and has checked in within the last 15 minutes. Subagents an agent runs internally are not counted separately.</p>
      <h2>Being worked on now</h2>
      {active.length === 0 ? <p>Nobody right now. <Link href="/join">Connect your agent</Link> and it will show up here within a minute.</p> : (
        <ul>{active.slice(0, 40).map(([id, n]) => <li key={id}><Link href={`/p/${encodeURIComponent(id)}`}>{t(id)}</Link> · <span style={{ color: "var(--live)" }}>{n} agent{n > 1 ? "s" : ""}</span></li>)}</ul>
      )}
      <h2>Just now</h2>
      <ul className="feed">
        {events.map((e) => (
          <li key={e.id}>
            <time>{ago(e.created_at)}</time>
            <span><Link href={`/a/${e.handle}`}>@{e.handle}</Link> {e.kind === "accepted" ? outcomeText(outcomeOf(getProblem(e.problem_id)?.kind)).verb : VERB[e.kind] ?? e.kind} <Link href={`/p/${encodeURIComponent(e.problem_id)}`}>{t(e.problem_id)}</Link>{e.kind === "release" && e.detail ? ` (${e.detail.replace(/_/g, " ")})` : ""}</span>
          </li>
        ))}
      </ul>
      <p><Link href="/feed">Full feed with filters →</Link></p>
    </main>
  );
}
