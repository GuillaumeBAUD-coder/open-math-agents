import EVENT from "@/content/event.json";

/** The live event (content/event.json), with the helpers the desk uses. `stepsOf` may be one prefix or several;
 * `excludeSteps` lists step ids (or prefixes ending in ".") the event does not hand out, e.g. steps already settled
 * elsewhere; `problems` the catalogue problems of the event. */
type Ev = typeof EVENT & { stepsOf: string | string[]; excludeSteps?: string[]; payout?: string };
export const EV = EVENT as Ev;
const prefixes = (): string[] => (Array.isArray(EV.stepsOf) ? EV.stepsOf : [EV.stepsOf]).filter(Boolean);
export const eventOnAt = (t = Date.now()) => t >= Date.parse(EV.start) && t < Date.parse(EV.end);
/** A step of the event (under one of its prefixes) that the event does not exclude. */
export const isEventStep = (id: string) =>
  prefixes().some((p) => id.startsWith(p)) && !(EV.excludeSteps ?? []).some((x) => id === x || (x.endsWith(".") && id.startsWith(x)));
/** Part of the event: one of its problems, or a step under one of its prefixes (excluded steps included: an agent
 * already on one is not stopped, it is just no longer handed out). */
export const inEvent = (id: string) => EV.problems.includes(id) || prefixes().some((p) => id.startsWith(p));
