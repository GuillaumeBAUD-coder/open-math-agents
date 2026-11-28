import Mathlib

/-!
# OEIS A200786: length-4 arrays with no two consecutive increases

Source: https://oeis.org/A200786
Credit: Sudharsan Rajendiran

A200786(n) is the number of 0..n arrays x(0..3) of 4 elements without any two consecutive increases, i.e. with
no three consecutive entries strictly increasing. Colin Barker conjectured (Oct 15 2017) the g.f.
`x(16 - 5x + 10x^2 - 5x^3 + x^4)/(1 - x)^5`, a(n) = (24 + 106n + 151n^2 + 86n^3 + 17n^4)/24, and the matching order-5 linear recurrence. The entry has offset `1`, so we state the g.f. for `Σ_(n≥1) a(n) x^n` (the coefficient of `x^0` is `0`; the definition itself gives `a(0) = 1`, the all-zero array), as an identity of formal power series over `ℚ`.

Conventions: an array is `v : Fin 4 → ℕ` with entries `≤ n`, read as the list `List.ofFn v`;
`ok` checks every window of three consecutive entries.
-/

namespace OMA.S_oeis_a200786

/-- `ok l`: no three consecutive entries of `l` are strictly increasing. -/
def ok : List ℕ → Bool
  | a :: b :: c :: t => !(decide (a < b) && decide (b < c)) && ok (b :: c :: t)
  | _ => true

/-- A200786(n): the number of 0..n arrays `x(0..3)` of 4 elements without any two consecutive increases, i.e. no three consecutive entries are strictly increasing. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 4 => Finset.range (n + 1)).filter (fun v => ok (List.ofFn v))).card

open PowerSeries in
/-- Barker's g.f. `x(16 - 5X + 10X^2 - 5X^3 + X^4)/(1 - x)^5` for `Σ_(n ≥ 1) a(n) x^n` (the entry has offset `1`;
the constant term is `0`, while the definition gives `a 0 = 1`). -/
theorem main :
    (PowerSeries.mk fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (16 - 5 * X + 10 * X ^ 2 - 5 * X ^ 3 + X ^ 4) := by
  sorry

end OMA.S_oeis_a200786
