import Mathlib

/-!
# A184688: 1/3 the number of n X 3 0..2 arrays with no element equal both to the element above and to the element to its left

Source: https://oeis.org/A184688
Credit: @ivillar

R. H. Hardin's sequence (offset 1, data 9, 192, 4080, 86688, 1841856, ...). An array is a map
x : Fin n → Fin 3 → Fin 3 (row i, column j, value in 0..2). The element x(i,j) with i ≥ 1 and
j ≥ 1 has an element above, x(i-1,j), and an element to its left, x(i,j-1); it must not equal both.
a(n) is one third of the number N(n) of such arrays.

Conjectures (Colin Barker, Apr 14 2018), together with the empirical recurrence of the entry:
a(n) = 22*a(n-1) - 16*a(n-2) (stated for n ≥ 3, all indices at least the offset 1, over ℤ);
G.f.: 3*x*(3 - 2*x) / (1 - 22*x + 16*x^2) (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = ((105-13*sqrt(105))*(11-sqrt(105))^n + (11+sqrt(105))^n*(105+13*sqrt(105))) / 560 (n ≥ 1,
over ℝ).
-/

namespace OMA.S_oeis_a184688

/-- No element equals both the element above it and the element to its left. -/
def Good {n : ℕ} (x : Fin n → Fin 3 → Fin 3) : Prop :=
  ∀ (i i' : Fin n) (j j' : Fin 3), (i : ℕ) = i' + 1 → (j : ℕ) = j' + 1 →
    ¬(x i j = x i' j ∧ x i j = x i j')

/-- N(n): the number of such n X 3 arrays. -/
noncomputable def N (n : ℕ) : ℕ := Nat.card {x : Fin n → Fin 3 → Fin 3 // Good x}

/-- a(n) = N(n)/3. -/
noncomputable def a (n : ℕ) : ℕ := N n / 3

/-- The conjectured g.f. 3*x*(3 - 2*x) / (1 - 22*x + 16*x^2). -/
noncomputable def G : PowerSeries ℚ :=
  (3 * PowerSeries.X * (3 - 2 * PowerSeries.X)) * (1 - 22 * PowerSeries.X + 16 * PowerSeries.X ^ 2)⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 22 * a (n - 1) - 16 * a (n - 2)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = ((105 - 13 * Real.sqrt 105) * (11 - Real.sqrt 105) ^ n +
      (11 + Real.sqrt 105) ^ n * (105 + 13 * Real.sqrt 105)) / 560) := by
  sorry

end OMA.S_oeis_a184688
