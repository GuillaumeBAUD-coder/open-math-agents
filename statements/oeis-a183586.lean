import Mathlib

/-!
# A183586: 1/24 the number of (n+1) X 2 0..3 arrays with every 2 X 2 subblock containing exactly three distinct values

Source: https://oeis.org/A183586
Credit: @ivillar

R. H. Hardin's sequence (offset 1, data 6, 56, 520, 4832, 44896, ...). An array is a map
x : Fin (n+1) → Fin 2 → Fin 4 (row i, column j, value in 0..3); its 2 X 2 subblocks are formed by
rows i, i+1, and each must contain exactly three distinct values. a(n) is 1/24 of the number N(n) of
such arrays.

Conjectures (Colin Barker, Mar 29 2018), together with the empirical recurrence of the entry:
a(n) = 8*a(n-1) + 12*a(n-2) (stated for n ≥ 3, all indices at least the offset 1);
G.f.: 2*x*(3 + 4*x) / (1 - 8*x - 12*x^2) (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = ((4-2*sqrt(7))^n*(-5+2* sqrt(7)) + (2*(2+sqrt(7)))^n*(5+2*sqrt(7))) / (6*sqrt(7)) (n ≥ 1,
over ℝ).
-/

namespace OMA.S_oeis_a183586

/-- The subblock formed by rows u, v contains exactly three distinct values. -/
def BlockOK (u v : Fin 2 → Fin 4) : Prop := ({u 0, u 1, v 0, v 1} : Finset (Fin 4)).card = 3

/-- N(n): the number of such (n+1) X 2 arrays. -/
noncomputable def N (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 2 → Fin 4 // ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)}

/-- a(n) = N(n)/24. -/
noncomputable def a (n : ℕ) : ℕ := N n / 24

/-- The conjectured g.f. 2*x*(3 + 4*x) / (1 - 8*x - 12*x^2). -/
noncomputable def G : PowerSeries ℚ :=
  (2 * PowerSeries.X * (3 + 4 * PowerSeries.X)) * (1 - 8 * PowerSeries.X - 12 * PowerSeries.X ^ 2)⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n → a n = 8 * a (n - 1) + 12 * a (n - 2)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = ((4 - 2 * Real.sqrt 7) ^ n * (-5 + 2 * Real.sqrt 7) +
      (2 * (2 + Real.sqrt 7)) ^ n * (5 + 2 * Real.sqrt 7)) / (6 * Real.sqrt 7)) := by
  sorry

end OMA.S_oeis_a183586
