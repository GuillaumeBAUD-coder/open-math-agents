import Mathlib

/-!
# OEIS A269659: length-6 arrays with no adjacent pair x, x+1 repeated

Source: https://oeis.org/A269659
Credit: Sudharsan Rajendiran

A269659(n) is the number of length-6 arrays with entries in `0..n` with no adjacent pair `x, x+1`
repeated (row 6 of A269656): the pattern `x, x + 1` (as two consecutive entries) does not occur at
two different positions. Colin Barker conjectured (Jan 2019) the g.f.
`2x(21 + 166x + 158x^2 + 17x^4 - 2x^5)/(1 - x)^7` and the matching order-7 recurrence. The entry
has offset `1`, so we state the g.f. for `Σ_(n≥1) a(n) x^n` (the coefficient of `x^0` is `0`), as
an identity of formal power series over `ℚ`.

Conventions: an array is `v : Fin 6 → ℕ` with entries `≤ n`, read as the list `List.ofFn v`;
`adjUp` lists the values `x` of the adjacent pairs `x, x + 1` and the condition is `Nodup`.
-/

namespace OMA.S_oeis_a269659

/-- The values `x` such that `x, x + 1` occur as adjacent entries of a list, one per occurrence,
in order. -/
def adjUp : List ℕ → List ℕ
  | a :: b :: t => (if b = a + 1 then [a] else []) ++ adjUp (b :: t)
  | _ => []

/-- A269659(n): the number of length-6 arrays with entries in `0..n` with no adjacent pair `x, x+1`
repeated, i.e. no pattern `x, x + 1` occurs at two different positions. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 6 => Finset.range (n + 1)).filter
    (fun v => (adjUp (List.ofFn v)).Nodup)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      2 * X * (21 + 166 * X + 158 * X ^ 2 + 17 * X ^ 4 - 2 * X ^ 5) := by
  sorry

end OMA.S_oeis_a269659
