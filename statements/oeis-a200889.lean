import Mathlib

/-!
# OEIS A200889: 6-element arrays in 0..n with no interior peak

Source: https://oeis.org/A200889
Credit: Sudharsan Rajendiran

A200889(n) is the number of arrays `x(0..5)` of 6 elements in `0..n` without any interior element greater than both neighbours (no strict peak `x(i-1) < x(i) > x(i+1)`). Colin Barker conjectured (Oct 2017) the g.f. `x(37 + 33x + x^2 - 54x^3 + 21x^4 - 7x^5 + x^6)/(1 - x)^7` and the matching order-7 linear recurrence. The entry has offset `1`; the definition also gives `a(0) = 1` (the constant array), which the g.f. does not describe, so we state the g.f. as an identity of formal power series over `ℚ` for the series with constant coefficient `0` and coefficients `a(n)`, `n ≥ 1`.

Conventions: an array is `v : Fin 6 → ℕ` with entries `≤ n`, read as the list `List.ofFn v`; `ok` checks every interior entry against its two neighbours.
-/

namespace OMA.S_oeis_a200889

/-- `ok l`: no interior entry of `l` is greater than both of its neighbours. -/
def ok : List ℕ → Bool
  | a :: b :: c :: t => !(decide (a < b) && decide (c < b)) && ok (b :: c :: t)
  | _ => true

/-- A200889(n): the number of arrays `x(0..5)` of 6 elements in `0..n` without any interior element
greater than both neighbours. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 6 => Finset.range (n + 1)).filter (fun v => ok (List.ofFn v))).card

open PowerSeries in
/-- Barker's g.f. for the sequence with offset `1` (the definition also gives `a 0 = 1`, which the
g.f. does not describe, so the constant coefficient is taken to be `0`). -/
theorem main :
    (PowerSeries.mk fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (37 + 33 * X + X ^ 2 - 54 * X ^ 3 + 21 * X ^ 4 - 7 * X ^ 5 + X ^ 6) := by
  sorry

end OMA.S_oeis_a200889
