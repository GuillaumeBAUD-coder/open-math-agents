import Mathlib

/-!
# OEIS A200892: 9-element arrays in 0..n with no interior peak

Source: https://oeis.org/A200892
Credit: Sudharsan Rajendiran

A200892(n) is the number of arrays `x(0..8)` of 9 elements in `0..n` without any interior element greater than both neighbours (no strict peak `x(i-1) < x(i) > x(i+1)`). Colin Barker conjectured (Oct 2017) the g.f. `x(200 + 2059x + 2760x^2 - 3509x^3 - 1714x^4 + 288x^5 + 208x^6 - 45x^7 + 10x^8 - x^9)/(1 - x)^10` and the matching order-10 linear recurrence. The entry has offset `1`; the definition also gives `a(0) = 1` (the constant array), which the g.f. does not describe, so we state the g.f. as an identity of formal power series over `ℚ` for the series with constant coefficient `0` and coefficients `a(n)`, `n ≥ 1`.

Conventions: an array is `v : Fin 9 → ℕ` with entries `≤ n`, read as the list `List.ofFn v`; `ok` checks every interior entry against its two neighbours.
-/

namespace OMA.S_oeis_a200892

/-- `ok l`: no interior entry of `l` is greater than both of its neighbours. -/
def ok : List ℕ → Bool
  | a :: b :: c :: t => !(decide (a < b) && decide (c < b)) && ok (b :: c :: t)
  | _ => true

/-- A200892(n): the number of arrays `x(0..8)` of 9 elements in `0..n` without any interior element
greater than both neighbours. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 9 => Finset.range (n + 1)).filter (fun v => ok (List.ofFn v))).card

open PowerSeries in
/-- Barker's g.f. for the sequence with offset `1` (the definition also gives `a 0 = 1`, which the
g.f. does not describe, so the constant coefficient is taken to be `0`). -/
theorem main :
    (PowerSeries.mk fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 10 =
      X * (200 + 2059 * X + 2760 * X ^ 2 - 3509 * X ^ 3 - 1714 * X ^ 4 + 288 * X ^ 5 + 208 * X ^ 6 - 45 * X ^ 7 + 10 * X ^ 8 - X ^ 9) := by
  sorry

end OMA.S_oeis_a200892
