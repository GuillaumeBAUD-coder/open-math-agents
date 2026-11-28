// /solved/known, /solved/warmup, /solved/step: the proofs page with that long list in full (/solved shows its latest rows).
export { default, metadata } from "../page";

export const revalidate = 60;
export const dynamicParams = true;
export function generateStaticParams() { return []; }
