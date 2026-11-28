import OMAStatements.S_oeis_a203231
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: products (n+2) = (3p, 3e+4p) gives a(n+4) = 6a(n+2) - 9a(n); the power series identity follows coefficientwise.

namespace OMA.P_oeis_a203231
open OMA.S_oeis_a203231 PowerSeries

lemma digit_pair (n : ℕ) : digit n * digit (n+1) = 3 ∧ digit n + digit (n+1) = 4 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have h1 : (n+1) % 2 = 1 := by omega
    simp [digit, h, h1]
  · have h1 : (n+1) % 2 = 0 := by omega
    simp [digit, h, h1]

lemma products_add2 (n : ℕ) :
    products (n+2) = (3 * (products n).1, 3 * (products n).2 + 4 * (products n).1) := by
  obtain ⟨h1, h2⟩ := digit_pair n
  have e : products (n+2) = ((products n).1 * digit n * digit (n+1),
      ((products n).2 * digit n + (products n).1) * digit (n+1) + (products n).1 * digit n) := by
    simp only [products]
  rw [e]
  ext
  · simp only; rw [mul_assoc, h1]; ring
  · simp only
    have : digit (n+1) = 4 - digit n := by linarith
    rw [this] at h1 ⊢
    linear_combination (products n).2 * h1

lemma rec4 (m : ℕ) : a (m+4) = 6 * a (m+2) - 9 * a m := by
  unfold a
  rw [show m + 4 = (m+2)+2 from rfl, products_add2 (m+2), products_add2 m]
  simp only
  ring

lemma part1 : ∀ n : ℕ, 4 < n → a n = 6 * a (n-2) - 9 * a (n-4) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n-4, by omega⟩
  rw [rec4]
  congr 2

lemma part2 : ((1 - C 3 * X^2 : ℤ⟦X⟧)^2 * mk a = X^1 + C 4 * X^2 + C 9 * X^3) := by
  have hsq : (1 - C 3 * X^2 : ℤ⟦X⟧)^2 = 1 - C 6 * X^2 + C 9 * X^4 := by
    have h6 : (C 6 : ℤ⟦X⟧) = 2 * C 3 := by
      rw [show (6:ℤ) = 2 * 3 by norm_num, map_mul, map_ofNat]
    have h9 : (C 9 : ℤ⟦X⟧) = C 3 * C 3 := by
      rw [← map_mul]; norm_num
    rw [h6, h9]; ring
  rw [hsq]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
    coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  match n with
  | 0 => simp [a, products]
  | 1 => simp [a, products]
  | 2 => simp [a, products, digit]
  | 3 => simp [a, products, digit]
  | m + 4 =>
    have h1 : 2 ≤ m + 4 := by omega
    have h2 : 4 ≤ m + 4 := by omega
    simp only [h1, h2, if_true, show m + 4 - 2 = m + 2 by omega, show m + 4 - 4 = m by omega,
      rec4]
    have : ¬ (m + 4 = 1) := by omega
    have : ¬ (m + 4 = 2) := by omega
    have : ¬ (m + 4 = 3) := by omega
    simp [*]

end OMA.P_oeis_a203231

theorem OMA.solution : type_of% @OMA.S_oeis_a203231.main :=
  ⟨OMA.P_oeis_a203231.part1, OMA.P_oeis_a203231.part2⟩
