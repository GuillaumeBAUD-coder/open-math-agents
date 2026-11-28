import OMAStatements.S_oeis_a196279
import Mathlib

/-! Proof for OEIS A196279: `7 (n + 10) = 7n + 70` has the same last digit as `7n` and leading part larger by 7, so
`a(n + 10) = a(n) + 1`; the recurrence follows.
Credit: Sudharsan Rajendiran -/

namespace OMA.P196279
open OMA.S_oeis_a196279

lemma a_add_ten (n : ℕ) : a (n + 10) = a n + 1 := by
  unfold a
  have h1 : 7 * (n + 10) / 10 = 7 * n / 10 + 7 := by omega
  have h2 : 7 * (n + 10) % 10 = 7 * n % 10 := by omega
  rw [h1, h2]
  push_cast
  omega

end OMA.P196279

theorem OMA.P196279.old_main : ∀ n : ℕ, 11 ≤ n → OMA.S_oeis_a196279.a n = OMA.S_oeis_a196279.a (n - 1) + OMA.S_oeis_a196279.a (n - 10) - OMA.S_oeis_a196279.a (n - 11) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
  have e1 := OMA.P196279.a_add_ten (m + 1)
  have e0 := OMA.P196279.a_add_ten m
  simp only [show m + 11 - 1 = m + 10 by omega, show m + 11 - 10 = m + 1 by omega,
    show m + 11 - 11 = m by omega, show m + 1 + 10 = m + 11 by omega] at *
  linarith

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a196279.main := by
  refine ⟨OMA.P196279.old_main, ?_⟩
  have hD : ((1 + X) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X - 1) ^ 2 :
      PowerSeries ℤ) = 1 - X ^ 1 - X ^ 10 + X ^ 11 := by ring
  have hN : (X * (-2 + X - 2 * X ^ 3 + X ^ 4 - 2 * X ^ 6 + X ^ 7 + X ^ 9 + X ^ 2 + X ^ 5 + X ^ 8) :
      PowerSeries ℤ) = -(C (2 : ℤ) * X ^ 1) + X ^ 2 + X ^ 3 - C (2 : ℤ) * X ^ 4 + X ^ 5 + X ^ 6
        - C (2 : ℤ) * X ^ 7 + X ^ 8 + X ^ 9 + X ^ 10 := by simp only [map_ofNat]; ring
  rw [hD, hN]
  ext m
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, map_neg, coeff_mk, coeff_mul_X_pow',
    coeff_one, coeff_C_mul, coeff_X_pow, coeff_C]
  rcases Nat.lt_or_ge m 11 with hm | hm
  · interval_cases m <;> decide
  · rw [OMA.P196279.old_main m hm]
    simp only [if_pos (show 1 ≤ m by omega), if_pos (show 4 ≤ m by omega), if_pos (show 7 ≤ m by omega), if_pos (show 10 ≤ m by omega), if_pos (show 11 ≤ m by omega), show ¬ (m - 1 = 0) by omega, show ¬ (m - 4 = 0) by omega, show ¬ (m - 7 = 0) by omega, show ¬ (m = 0) by omega, show ¬ (m = 2) by omega, show ¬ (m = 3) by omega, show ¬ (m = 5) by omega, show ¬ (m = 6) by omega, show ¬ (m = 8) by omega, show ¬ (m = 9) by omega, show ¬ (m = 10) by omega, if_false]
    ring
