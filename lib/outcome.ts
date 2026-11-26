/**
 * What a checked proof on this site actually means, said the same way on every page. A Lean proof of a result that the
 * literature already settled is a real contribution (a machine-checked proof), but it is not the solution of an open
 * problem, and a warm-up is neither. Erdős "variants" are special cases of a problem whose main question may still be
 * open. Nothing here may suggest otherwise. Client-safe: no server imports.
 */
export type Outcome = "open" | "known" | "warmup" | "step";

export function outcomeOf(kind: string | undefined | null): Outcome {
  // An "unformalized" problem stated here and then proved is an open problem; anything unknown is a reduction step.
  return kind === "open" || kind === "unformalized" ? "open" : kind === "known" ? "known" : kind === "warmup" ? "warmup" : "step";
}

const TEXT: Record<Outcome, { badge: string; refuted: string; verb: string; short: string; explain: string; section: string }> = {
  open: {
    badge: "Open problem solved", refuted: "Open problem refuted", verb: "SOLVED AN OPEN PROBLEM:", short: "open problem solved",
    explain: "An open problem: nobody had a proof before. This is a new result.",
    section: "Open problems solved",
  },
  known: {
    badge: "Known result · now proved in Lean", refuted: "Known result · now refuted in Lean", verb: "formalized in Lean (already-known result)",
    short: "known result, formalized",
    explain: "This result was already proved in the mathematical literature. What is new is the machine-checked Lean proof: useful, but not the solution of an open problem.",
    section: "Known results formalized in Lean",
  },
  warmup: {
    badge: "Warm-up done", refuted: "Warm-up done", verb: "did the warm-up", short: "warm-up",
    explain: "A warm-up exercise, there to learn the submission format. Not a research problem.",
    section: "Warm-ups",
  },
  step: {
    badge: "Step proved", refuted: "Step refuted", verb: "proved a step of a reduction:", short: "reduction step",
    explain: "One hypothesis of a reduction. The problem it belongs to is solved only once every step is proved.",
    section: "Steps of reductions",
  },
};

export const outcomeText = (o: Outcome) => TEXT[o];
export const outcomeBadge = (kind: string | undefined | null, polarity?: string | null) => {
  const t = TEXT[outcomeOf(kind)];
  return polarity === "disproof" ? t.refuted : t.badge;
};

/** Erdős problems status values (erdosproblems.com) that mean the main question is still open. */
const OPEN_STATES = new Set(["open", "falsifiable", "decidable", "verifiable", "not provable", "not disprovable", "independent"]);

/**
 * For a variant or special case (formal-conjectures ".variants." ids): which problem it belongs to and whether that
 * problem is still open. Null for problems that are not variants.
 */
export function variantOf(id: string, title: string, erdosState?: string | null): { parent: string; stillOpen: boolean | null } | null {
  if (!/\.variants?\./.test(id)) return null;
  const parent = title.split(" — ")[0].trim() || id.split(".")[0];
  return { parent, stillOpen: erdosState ? OPEN_STATES.has(erdosState.toLowerCase()) : null };
}

export function variantNote(id: string, title: string, erdosState?: string | null): string | null {
  const v = variantOf(id, title, erdosState);
  if (!v) return null;
  return v.stillOpen === true
    ? `A variant (special case) of ${v.parent}. ${v.parent} itself is still open: proving this variant does not solve it.`
    : v.stillOpen === false
      ? `A variant (special case) of ${v.parent}, which is already settled.`
      : `A variant (special case) of ${v.parent}: proving it does not by itself settle ${v.parent}.`;
}

/** Counts by outcome, for summaries ("0 open problems solved · 23 known results formalized · …"). */
export function outcomeCounts(kinds: (string | undefined | null)[]) {
  const c: Record<Outcome, number> = { open: 0, known: 0, warmup: 0, step: 0 };
  for (const k of kinds) c[outcomeOf(k)]++;
  return c;
}

export function outcomeSummary(c: Record<Outcome, number>) {
  const parts = [
    `${c.open} open problem${c.open === 1 ? "" : "s"} solved`,
    c.known ? `${c.known} known result${c.known === 1 ? "" : "s"} formalized in Lean` : null,
    c.warmup ? `${c.warmup} warm-up${c.warmup === 1 ? "" : "s"}` : null,
    c.step ? `${c.step} reduction step${c.step === 1 ? "" : "s"}` : null,
  ].filter(Boolean);
  return parts.join(" · ");
}
