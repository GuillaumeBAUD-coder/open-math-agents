import Mathlib

/-!
# A183634: Number of (n+1) X 2 0..3 arrays with every 2 x 2 subblock summing to 6

Source: https://oeis.org/A183634
Credit: @ivillar

Status: known result: the entry records that Colin Barker's formulas below were proved by
Christian Krause (Jun 20 2026).

R. H. Hardin's sequence (offset 1, data 44, 136, 452, 1576, 5684, ...). An array is a map
x : Fin (n+1) → Fin 2 → Fin 4 (row i, column j, value in 0..3); its 2 X 2 subblocks are formed by
rows i, i+1, and the four entries of each must sum to 6.

Formulas of the entry (Colin Barker, Feb 27 2018):
a(n) = 10*a(n-1) - 35*a(n-2) + 50*a(n-3) - 24*a(n-4) (stated for n ≥ 5, all indices at least the
offset 1, over ℤ);
G.f.: 4*x*(11 - 76*x + 158*x^2 - 96*x^3) / ((1 - x)*(1 - 2*x)*(1 - 3*x)*(1 - 4*x)) (of
Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = 2 + 2^(2+n) + 2*3^(1+n) + 4^(1+n) (n ≥ 1).
-/

namespace OMA.S_oeis_a183634

/-- The subblock formed by rows u, v sums to 6. -/
def BlockOK (u v : Fin 2 → Fin 4) : Prop := (u 0 : ℕ) + u 1 + v 0 + v 1 = 6

/-- a(n): the number of such (n+1) X 2 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 2 → Fin 4 // ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)}

/-- The g.f. 4*x*(11 - 76*x + 158*x^2 - 96*x^3) / ((1 - x)*(1 - 2*x)*(1 - 3*x)*(1 - 4*x)). -/
noncomputable def G : PowerSeries ℚ :=
  (4 * PowerSeries.X * (11 - 76 * PowerSeries.X + 158 * PowerSeries.X ^ 2 - 96 * PowerSeries.X ^ 3)) *
    ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) * (1 - 4 * PowerSeries.X))⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 5 ≤ n →
      (a n : ℤ) = 10 * a (n - 1) - 35 * a (n - 2) + 50 * a (n - 3) - 24 * a (n - 4)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → a n = 2 + 2 ^ (2 + n) + 2 * 3 ^ (1 + n) + 4 ^ (1 + n)) := by
  sorry

end OMA.S_oeis_a183634
