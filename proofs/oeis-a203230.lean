import OMAStatements.S_oeis_a203230
import Mathlib

open PowerSeries OMA.S_oeis_a203230 in
theorem OMA.solution : type_of% @OMA.S_oeis_a203230.main := by
  have hd : ∀ n, digit n * digit (n + 1) = 3 ∧ digit n + digit (n + 1) = 4 := by
    intro n
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [digit, h, Nat.add_mod]
  have step : ∀ n, products (n + 2) =
      (3 * (products n).1, 3 * (products n).2 + 4 * (products n).1) := by
    intro n
    obtain ⟨h1, h2⟩ := hd n
    simp only [products]
    refine Prod.ext ?_ ?_
    · simp only
      linear_combination (products n).1 * h1
    · simp only
      linear_combination (products n).2 * h1 + (products n).1 * h2
  have hrec : ∀ n, a (n + 4) = 6 * a (n + 2) - 9 * a n := by
    intro n
    simp only [a]
    rw [show n + 4 = n + 2 + 2 from rfl, step (n + 2), step n]
    simp only
    ring
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [hrec m, show m + 4 - 2 = m + 2 by omega, show m + 4 - 4 = m by omega]
  · rw [show (1 - C 3 * X ^ 2 : ℤ⟦X⟧) ^ 2 = 1 - C 6 * X ^ 2 + C 9 * X ^ 4 by
      rw [show (6 : ℤ) = 2 * 3 by norm_num, show (9 : ℤ) = 3 * 3 by norm_num, map_mul, map_mul]
      simp only [map_ofNat]
      ring]
    ext n
    simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
      coeff_X_pow_mul', coeff_mk, coeff_X_pow, coeff_X, pow_one]
    rcases n with _ | _ | _ | _ | m
    · simp [a, products, digit, coeff_X]
    · simp [a, products, digit, coeff_X]
    · simp [a, products, digit, coeff_X]
    · simp [a, products, digit, coeff_X]
    · rw [if_pos (by omega), if_pos (by omega), show m + 1 + 1 + 1 + 1 - 2 = m + 2 by omega,
        show m + 1 + 1 + 1 + 1 - 4 = m by omega, show m + 1 + 1 + 1 + 1 = m + 4 from rfl, hrec m]
      simp
