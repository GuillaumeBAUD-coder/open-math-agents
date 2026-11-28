import { renderTitle } from "@/lib/render";

/** A problem title with its $…$ math typeset (titles from OEIS and MathOverflow often contain LaTeX). */
export default function MathTitle({ text }: { text: string }) {
  return <span className="mtitle" dangerouslySetInnerHTML={{ __html: renderTitle(text) }} />;
}
