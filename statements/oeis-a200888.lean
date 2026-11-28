import Mathlib

/-!
# OEIS A200888: 5-element arrays in 0..n with no interior peak

Source: https://oeis.org/A200888
Credit: Sudharsan Rajendiran

A200888(n) is the number of arrays `x(0..4)` of 5 elements in `0..n` without any interior element greater than both neighbours (no strict peak `x(i-1) < x(i) > x(i+1)`). Colin Barker conjectured (Oct 2017) the g.f. `x(21 - 5x + 11x^2 - 16x^3 + 6x^4 - x^5)/(1 - x)^6` and the matching order-6 linear recurrence. The entry has offset `1`; the definition also gives `a(0) = 1` (the constant array), which the g.f. does not describe, so we state the g.f. as an identity of formal power series over `ℚ` for the series with constant coefficient `0` and coefficients `a(n)`, `n ≥ 1`.

Conventions: an array is `v : Fin 5 → ℕ` with entries `≤ n`, read as the list `List.ofFn v`; `ok` checks every interior entry against its two neighbours.
-/

namespace OMA.S_oeis_a200888

/-- `ok l`: no interior entry of `l` is greater than both of its neighbours. -/
def ok : List ℕ → Bool
  | a :: b :: c :: t => !(decide (a < b) && decide (c < b)) && ok (b :: c :: t)
  | _ => true

/-- A200888(n): the number of arrays `x(0..4)` of 5 elements in `0..n` without any interior element
greater than both neighbours. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 5 => Finset.range (n + 1)).filter (fun v => ok (List.ofFn v))).card

open PowerSeries in
/-- Barker's g.f. for the sequence with offset `1` (the definition also gives `a 0 = 1`, which the
g.f. does not describe, so the constant coefficient is taken to be `0`). -/
theorem main :
    (PowerSeries.mk fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
      X * (21 - 5 * X + 11 * X ^ 2 - 16 * X ^ 3 + 6 * X ^ 4 - X ^ 5) := by
  sorry

end OMA.S_oeis_a200888
