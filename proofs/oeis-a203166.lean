import OMAStatements.S_oeis_a203166
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: products (n+5) = (120p, 120e+274p) gives a(n+10) = 240a(n+5) - 14400a(n); the power series identity follows coefficientwise.

namespace OMA.P_oeis_a203166
open OMA.S_oeis_a203166 PowerSeries

lemma products_add5 (n : ℕ) :
    products (n+5) = (120 * (products n).1, 120 * (products n).2 + 274 * (products n).1) := by
  simp only [products]
  rcases (by omega : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4)
    with h | h | h | h | h <;>
  · have e1 : (n+1) % 5 = (n % 5 + 1) % 5 := by omega
    have e2 : (n+2) % 5 = (n % 5 + 2) % 5 := by omega
    have e3 : (n+3) % 5 = (n % 5 + 3) % 5 := by omega
    have e4 : (n+4) % 5 = (n % 5 + 4) % 5 := by omega
    simp only [digit, e1, e2, e3, e4, h]
    ext <;> simp only <;> ring

lemma rec10 (m : ℕ) : a (m+10) = 240 * a (m+5) - 14400 * a m := by
  unfold a
  rw [show m + 10 = (m+5)+5 from rfl, products_add5 (m+5), products_add5 m]
  simp only
  ring

lemma vals : a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 11 ∧ a 4 = 50 ∧ a 5 = 274 ∧
    a 6 = 394 ∧ a 7 = 908 ∧ a 8 = 2964 ∧ a 9 = 12576 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma part1 : ∀ n : ℕ, 10 < n → a n = 240 * a (n-5) - 14400 * a (n-10) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n-10, by omega⟩
  rw [rec10]
  congr 2

lemma part2 : ((1 - C 120 * X^5 : ℤ⟦X⟧)^2 * mk a = X^1 + C 3 * X^2 + C 11 * X^3 + C 50 * X^4 +
    C 274 * X^5 + C 154 * X^6 + C 188 * X^7 + C 324 * X^8 + C 576 * X^9) := by
  have hsq : (1 - C 120 * X^5 : ℤ⟦X⟧)^2 = 1 - C 240 * X^5 + C 14400 * X^10 := by
    have h6 : (C 240 : ℤ⟦X⟧) = 2 * C 120 := by
      rw [show (240:ℤ) = 2 * 120 by norm_num, map_mul, map_ofNat]
    have h9 : (C 14400 : ℤ⟦X⟧) = C 120 * C 120 := by
      rw [← map_mul]; norm_num
    rw [h6, h9]; ring
  rw [hsq]
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := vals
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
    coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  match n with
  | 0 => simp [v0]
  | 1 => simp [v1]
  | 2 => simp [v2]
  | 3 => simp [v3]
  | 4 => simp [v4]
  | 5 => simp [v5, v0]
  | 6 => simp [v6, v1]
  | 7 => simp [v7, v2]
  | 8 => simp [v8, v3]
  | 9 => simp [v9, v4]
  | m + 10 =>
    have h1 : 5 ≤ m + 10 := by omega
    have h2 : 10 ≤ m + 10 := by omega
    simp only [h1, h2, if_true, show m + 10 - 5 = m + 5 by omega,
      show m + 10 - 10 = m by omega, rec10]
    have : ¬ (m + 10 = 1) := by omega
    have : ¬ (m + 10 = 2) := by omega
    have : ¬ (m + 10 = 3) := by omega
    have : ¬ (m + 10 = 4) := by omega
    have : ¬ (m + 10 = 5) := by omega
    have : ¬ (m + 10 = 6) := by omega
    have : ¬ (m + 10 = 7) := by omega
    have : ¬ (m + 10 = 8) := by omega
    have : ¬ (m + 10 = 9) := by omega
    simp [*]

end OMA.P_oeis_a203166

theorem OMA.solution : type_of% @OMA.S_oeis_a203166.main :=
  ⟨OMA.P_oeis_a203166.part1, OMA.P_oeis_a203166.part2⟩
