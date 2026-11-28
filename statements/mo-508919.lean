import Mathlib

/-!
# Integer solution to (3x-1)y^2 + x z^2 = x^3-2

Source: https://mathoverflow.net/questions/508919
Credit: @Hyvok

Question (Bogdan Grechuk, MathOverflow, 2026-03-10): Do there exist integers `x, y, z`
satisfying `(3x - 1) y^2 + x z^2 = x^3 - 2`?
The asker notes this is one of the two shortest (by his length measure) cubic equations whose
integer solvability is open, after `7x^3 + 2y^3 = 3z^2 + 1` was settled; he found no solution with
`|y|` up to `3 * 10^9` and could not prove insolubility.

What the thread says (as of 2026-11): no answers. Comments establish necessary conditions:
`x` must be even (F. Petrov), in fact `x ≡ 34 (mod 48)` (B. Grechuk); every odd prime dividing
`x` is `±1 (mod 8)`. The variety has rational points, e.g. `(4/3, 1/3, 1/6)` (C. Wuthrich), so a
naive obstruction is unlikely. Heuristics (W. Sawin, Aurel) suggest the expected number of
solutions with `|x| ≤ X` grows slowly (like a power of `log X`), so a solution, if any, may be
huge. T. Browning reduced to Pell equations indexed by `k` and searched `k ≤ 10^7`; Vepir
extended this to `|k| ≤ 10^11` and sieved `|x| ≤ 10^15`, finding no solution. A claimed
non-existence proof posted in the comments (figshare preprint, 2026-04) was pointed out by the
asker to contain an error. The problem is open.

## Formalization notes

* Variables `x y z : ℤ`, no positivity or nontriviality conditions (the question asks for any
  integer solution).
* The question is a yes/no question with unknown answer. Extensive computations (no solution with
  `|x| ≤ 10^15`) are the only evidence, so we formalize the NON-EXISTENCE direction:
  there are no integers `x, y, z` with `(3x - 1) y^2 + x z^2 = x^3 - 2`. A disproof of `main`
  (an explicit integer solution) would answer the question in the affirmative.
* Sanity checks (scratch, not part of this file): exhaustive search over `|x| ≤ 30000` (all `y`,
  `z`) finds nothing; for every modulus `m ≤ 400` the congruence has a solution mod `m`, so there
  is no small-modulus congruence obstruction.
-/

namespace OMA.S_mo_508919

/-- There are no integers `x, y, z` with `(3x - 1) y^2 + x z^2 = x^3 - 2`. -/
theorem main : ¬ ∃ x y z : ℤ, (3 * x - 1) * y ^ 2 + x * z ^ 2 = x ^ 3 - 2 := by
  sorry

end OMA.S_mo_508919
