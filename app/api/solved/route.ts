import { NextResponse } from "next/server";
import { getSolvedForExport, type Solved } from "@/lib/db";
import { getProblem, getFullMany } from "@/lib/catalog";
import { json } from "@/lib/desk";
import { outcomeOf, outcomeCounts, variantNote } from "@/lib/outcome";
import { parseStep } from "@/lib/steps";

export async function GET() {
  let rows: Solved[];
  try {
    rows = await getSolvedForExport();
  } catch (error) {
    console.error("Solved export read failed", error);
    return json({ error: "solved_list_unavailable" }, 503);
  }
  const state = new Map((await getFullMany(rows.map((r) => r.problem_id)).catch(() => [])).map((f) => [f.id, f.erdosState]));
  const solved = rows.map((row) => {
    const p = getProblem(row.problem_id);
    const step = p ? null : parseStep(row.problem_id);
    const title = p?.title ?? (step ? `Step H${step.k} of ${getProblem(step.parent)?.title ?? step.parent}` : row.problem_id);
    return {
      ...row, title, step: step !== null, pr_url: row.pr_url.replace(/#closed$/, ""),
      outcome: outcomeOf(p?.kind), variantOf: p ? variantNote(p.id, p.title, state.get(p.id)) : null,
    };
  });
  return NextResponse.json(
    {
      creditPolicy: "Solver of record = the GitHub account that authored the merged pull request (the owner of the agent). Agent and model are recorded as declared in the pull request.",
      outcomes: "open = an open problem solved (a new result); known = a result already proved in the literature, now formalized in Lean; warmup = an exercise; step = one hypothesis of a reduction",
      count: solved.length,
      byOutcome: outcomeCounts(solved.map((row) => row.outcome)),
      solved,
    },
    { headers: { "Cache-Control": "public, s-maxage=60", "Vercel-CDN-Cache-Control": "max-age=60", "Access-Control-Allow-Origin": "*" } },
  );
}
