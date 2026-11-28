import Mathlib

/-!
# OEIS A200891: 8-element arrays in 0..n with no interior peak

Source: https://oeis.org/A200891
Credit: Sudharsan Rajendiran

A200891(n) is the number of arrays `x(0..7)` of 8 elements in `0..n` without any interior element greater than both neighbours (no strict peak `x(i-1) < x(i) > x(i+1)`). Colin Barker conjectured (Oct 2017) the g.f. `x(114 + 665x + 357x^2 - 953x^3 - 37x^4 - 47x^5 + 37x^6 - 9x^7 + x^8)/(1 - x)^9` and the matching order-9 linear recurrence. The entry has offset `1`; the definition also gives `a(0) = 1` (the constant array), which the g.f. does not describe, so we state the g.f. as an identity of formal power series over `ℚ` for the series with constant coefficient `0` and coefficients `a(n)`, `n ≥ 1`.

Conventions: an array is `v : Fin 8 → ℕ` with entries `≤ n`, read as the list `List.ofFn v`; `ok` checks every interior entry against its two neighbours.
-/

namespace OMA.S_oeis_a200891

/-- `ok l`: no interior entry of `l` is greater than both of its neighbours. -/
def ok : List ℕ → Bool
  | a :: b :: c :: t => !(decide (a < b) && decide (c < b)) && ok (b :: c :: t)
  | _ => true

/-- A200891(n): the number of arrays `x(0..7)` of 8 elements in `0..n` without any interior element
greater than both neighbours. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 8 => Finset.range (n + 1)).filter (fun v => ok (List.ofFn v))).card

open PowerSeries in
/-- Barker's g.f. for the sequence with offset `1` (the definition also gives `a 0 = 1`, which the
g.f. does not describe, so the constant coefficient is taken to be `0`). -/
theorem main :
    (PowerSeries.mk fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (114 + 665 * X + 357 * X ^ 2 - 953 * X ^ 3 - 37 * X ^ 4 - 47 * X ^ 5 + 37 * X ^ 6 - 9 * X ^ 7 + X ^ 8) := by
  sorry

end OMA.S_oeis_a200891
