import Mathlib

/-!
# OEIS A200839: length-4 arrays with no two consecutive increases or decreases

Source: https://oeis.org/A200839
Credit: Sudharsan Rajendiran

A200839(n) is the number of 0..n arrays x(0..3) of 4 elements without any two consecutive increases or two consecutive decreases, i.e. with
no three consecutive entries strictly increasing or strictly decreasing. Colin Barker conjectured (Oct 14 2017) the g.f.
`x(16 - 11x + 9x^2 - 5x^3 + x^4)/(1 - x)^5`, and the matching order-5 linear recurrence. The entry has offset `1`, so we state the g.f. for `Σ_(n≥1) a(n) x^n` (the coefficient of `x^0` is `0`; the definition itself gives `a(0) = 1`, the all-zero array), as an identity of formal power series over `ℚ`.

Conventions: an array is `v : Fin 4 → ℕ` with entries `≤ n`, read as the list `List.ofFn v`;
`ok` checks every window of three consecutive entries.
-/

namespace OMA.S_oeis_a200839

/-- `ok l`: no three consecutive entries of `l` are strictly increasing or strictly decreasing. -/
def ok : List ℕ → Bool
  | a :: b :: c :: t => !((decide (a < b) && decide (b < c)) || (decide (b < a) && decide (c < b))) && ok (b :: c :: t)
  | _ => true

/-- A200839(n): the number of 0..n arrays `x(0..3)` of 4 elements without any two consecutive increases or two consecutive decreases, i.e. no three consecutive
entries are strictly increasing or strictly decreasing. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 4 => Finset.range (n + 1)).filter (fun v => ok (List.ofFn v))).card

open PowerSeries in
/-- Barker's g.f. `x(16 - 11X + 9X^2 - 5X^3 + X^4)/(1 - x)^5` for `Σ_(n ≥ 1) a(n) x^n` (the entry has offset `1`;
the constant term is `0`, while the definition gives `a 0 = 1`). -/
theorem main :
    (PowerSeries.mk fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (16 - 11 * X + 9 * X ^ 2 - 5 * X ^ 3 + X ^ 4) := by
  sorry

end OMA.S_oeis_a200839
