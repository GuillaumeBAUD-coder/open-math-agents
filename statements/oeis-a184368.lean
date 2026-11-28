import Mathlib

/-!
# A184368: 1/3 the number of (n+1) X 2 0..2 arrays with every 2 X 2 subblock having at least two equal elements connected horizontally or vertically

Source: https://oeis.org/A184368
Credit: @ivillar

R. H. Hardin's sequence (offset 1, data 21, 153, 1107, 8019, 58077, ...). An array is a map
x : Fin (n+1) → Fin 2 → Fin 3 (row i, column j, value in 0..2); its 2 X 2 subblocks are formed by
rows i, i+1. In the subblock [[p, q], [r, s]] the horizontally or vertically connected pairs are
(p, q), (r, s), (p, r), (q, s), and at least one of them must be an equal pair. a(n) is one third of
the number N(n) of such arrays.

Conjectures (Colin Barker, Feb 27 2018), together with the empirical recurrence of the entry:
a(n) = 6*a(n-1) + 9*a(n-2) (stated for n ≥ 3, all indices at least the offset 1);
G.f.: 3*x*(7 + 9*x) / (1 - 6*x - 9*x^2) (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = ((3-3*sqrt(2))^n*(-4+3*sqrt(2)) + (3*(1+sqrt(2)))^n*(4+3*sqrt(2))) / (2*sqrt(2)) (n ≥ 1, over ℝ).
-/

namespace OMA.S_oeis_a184368

/-- The subblock formed by rows u, v has an equal horizontally or vertically connected pair. -/
def BlockOK (u v : Fin 2 → Fin 3) : Prop := u 0 = u 1 ∨ v 0 = v 1 ∨ u 0 = v 0 ∨ u 1 = v 1

/-- N(n): the number of such (n+1) X 2 arrays. -/
noncomputable def N (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 2 → Fin 3 // ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)}

/-- a(n) = N(n)/3. -/
noncomputable def a (n : ℕ) : ℕ := N n / 3

/-- The conjectured g.f. 3*x*(7 + 9*x) / (1 - 6*x - 9*x^2). -/
noncomputable def G : PowerSeries ℚ :=
  (3 * PowerSeries.X * (7 + 9 * PowerSeries.X)) * (1 - 6 * PowerSeries.X - 9 * PowerSeries.X ^ 2)⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n → a n = 6 * a (n - 1) + 9 * a (n - 2)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = ((3 - 3 * Real.sqrt 2) ^ n * (-4 + 3 * Real.sqrt 2) +
      (3 * (1 + Real.sqrt 2)) ^ n * (4 + 3 * Real.sqrt 2)) / (2 * Real.sqrt 2)) := by
  sorry

end OMA.S_oeis_a184368
