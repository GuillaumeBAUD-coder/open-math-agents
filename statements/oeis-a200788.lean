import Mathlib

/-!
# OEIS A200788: length-6 arrays with no two consecutive increases

Source: https://oeis.org/A200788
Credit: Sudharsan Rajendiran

A200788(n) is the number of 0..n arrays x(0..5) of 6 elements without any two consecutive increases, i.e. with
no three consecutive entries strictly increasing. Colin Barker conjectured (Oct 15 2017) the g.f.
`x(64 + 174x + 126x^2 - 30x^3 + 21x^4 - 7x^5 + x^6)/(1 - x)^7`, and the matching order-7 linear recurrence. The entry has offset `1`, so we state the g.f. for `Σ_(n≥1) a(n) x^n` (the coefficient of `x^0` is `0`; the definition itself gives `a(0) = 1`, the all-zero array), as an identity of formal power series over `ℚ`.

Conventions: an array is `v : Fin 6 → ℕ` with entries `≤ n`, read as the list `List.ofFn v`;
`ok` checks every window of three consecutive entries.
-/

namespace OMA.S_oeis_a200788

/-- `ok l`: no three consecutive entries of `l` are strictly increasing. -/
def ok : List ℕ → Bool
  | a :: b :: c :: t => !(decide (a < b) && decide (b < c)) && ok (b :: c :: t)
  | _ => true

/-- A200788(n): the number of 0..n arrays `x(0..5)` of 6 elements without any two consecutive increases, i.e. no three consecutive entries are strictly increasing. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 6 => Finset.range (n + 1)).filter (fun v => ok (List.ofFn v))).card

open PowerSeries in
/-- Barker's g.f. `x(64 + 174X + 126X^2 - 30X^3 + 21X^4 - 7X^5 + X^6)/(1 - x)^7` for `Σ_(n ≥ 1) a(n) x^n` (the entry has offset `1`;
the constant term is `0`, while the definition gives `a 0 = 1`). -/
theorem main :
    (PowerSeries.mk fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (64 + 174 * X + 126 * X ^ 2 - 30 * X ^ 3 + 21 * X ^ 4 - 7 * X ^ 5 + X ^ 6) := by
  sorry

end OMA.S_oeis_a200788
