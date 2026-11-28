import OMAStatements.S_oeis_a114698
import Mathlib

open OMA.S_oeis_a114698 PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a114698.main := by
  have hlin : ∀ m : ℕ, a (m + 2) = 20 * ((m : ℤ) + 2) - 22 := by
    intro m
    simp [a]
  refine ⟨?_, ?_⟩
  · have hq : ∀ F : PowerSeries ℚ, F * (1 - X) ^ 2 = F - C (2 : ℚ) * (F * X ^ 1) + F * X ^ 2 := by
      intro F; simp only [map_ofNat]; ring
    have hr : (1 + 16 * X + 3 * X ^ 2 : PowerSeries ℚ) = 1 + C (16 : ℚ) * X ^ 1 + C (3 : ℚ) * X ^ 2 := by
      simp only [map_ofNat, pow_one]
    rw [hq, hr]
    ext n
    simp only [map_add, map_sub, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C_mul_X_pow,
      coeff_X_pow, coeff_one, coeff_C]
    rcases n with _ | _ | _ | m
    · simp [a]
    · simp [a]; norm_num
    · simp [a]; norm_num
    · have e1 : m + 1 + 1 + 1 - 1 = m + 2 := by omega
      have e2 : m + 1 + 1 + 1 - 2 = m + 1 := by omega
      simp only [e1, e2, show 1 ≤ m + 1 + 1 + 1 by omega, show 2 ≤ m + 1 + 1 + 1 by omega, if_true,
        show m + 1 + 1 + 1 ≠ 0 by omega, show m + 1 + 1 + 1 ≠ 1 by omega,
        show m + 1 + 1 + 1 ≠ 2 by omega, if_false]
      rw [show m + 1 + 1 + 1 + 1 = (m + 2) + 2 by ring, show m + 2 + 1 = (m + 1) + 2 by ring, hlin, hlin, hlin]
      push_cast; ring
  · intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    rw [show m + 3 + 1 = (m + 2) + 2 by ring, show m + 3 = (m + 1) + 2 by ring,
      show m + 1 + 2 - 1 = m + 2 by omega, hlin, hlin, hlin]
    push_cast; ring
