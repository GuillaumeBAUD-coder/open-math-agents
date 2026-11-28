import Mathlib

/-!
# A183690: Number of (n+1) X 2 0..2 arrays with every 2 X 2 subblock nonsingular

Source: https://oeis.org/A183690
Credit: @ivillar

R. H. Hardin's sequence (offset 1, data 50, 314, 1970, 12362, 77570, ...). An array is a map
x : Fin (n+1) → Fin 2 → Fin 3 (row i, column j, value in 0..2); its 2 X 2 subblocks are formed
by rows i, i+1, and the subblock [[p, q], [r, s]] is nonsingular when its determinant p*s - q*r
(an integer) is nonzero.

Conjectures (Colin Barker, Apr 04 2018), together with the empirical recurrence of the entry:
a(n) = 5*a(n-1) + 8*a(n-2) (stated for n ≥ 3, all indices at least the offset 1);
G.f.: 2*x*(25 + 32*x) / (1 - 5*x - 8*x^2) (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = (2^(1-n)*((5-sqrt(57))^n*(-15+2*sqrt(57)) + (5+sqrt(57))^n*(15+2*sqrt(57)))) / sqrt(57) (n ≥ 1, over ℝ).
-/

namespace OMA.S_oeis_a183690

/-- The subblock formed by rows u, v is nonsingular. -/
def BlockOK (u v : Fin 2 → Fin 3) : Prop := (u 0 : ℤ) * (v 1 : ℤ) - (u 1 : ℤ) * (v 0 : ℤ) ≠ 0

/-- a(n): the number of (n+1) X 2 arrays over 0..2 all of whose 2 X 2 subblocks are nonsingular. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 2 → Fin 3 // ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)}

/-- The conjectured g.f. 2*x*(25 + 32*x) / (1 - 5*x - 8*x^2). -/
noncomputable def G : PowerSeries ℚ :=
  (2 * PowerSeries.X * (25 + 32 * PowerSeries.X)) * (1 - 5 * PowerSeries.X - 8 * PowerSeries.X ^ 2)⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n → a n = 5 * a (n - 1) + 8 * a (n - 2)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = (2 : ℝ) ^ ((1 : ℤ) - n) * ((5 - Real.sqrt 57) ^ n * (-15 + 2 * Real.sqrt 57) +
        (5 + Real.sqrt 57) ^ n * (15 + 2 * Real.sqrt 57)) / Real.sqrt 57) := by
  sorry

end OMA.S_oeis_a183690
