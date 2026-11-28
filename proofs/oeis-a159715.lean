import OMAStatements.S_oeis_a159715
import Mathlib

open OMA.S_oeis_a159715 PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a159715.main := by
  refine ⟨?_, ?_, ?_⟩
  · have hL : (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 3 * X) ^ 2 : PowerSeries ℚ) = PowerSeries.mk (fun n => (a n : ℚ)) - C (6 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1) + C (9 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2) := by
      (try simp only [map_ofNat, map_one, map_neg, one_mul, pow_one]) <;> ring
    have hR : (2 * X ^ 2 * (2 - 3 * X) : PowerSeries ℚ) = C (4 : ℚ) * X ^ 2 - C (6 : ℚ) * X ^ 3 := by
      (try simp only [map_ofNat, map_one, map_neg, one_mul, pow_one]) <;> ring
    rw [hL, hR]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk,
      coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
    rcases n with _ | _ | _ | _ | n
    · norm_num [a]
    · norm_num [a]
    · norm_num [a]
    · norm_num [a]
    · simp only [show n + 1 + 1 + 1 + 1 = n + 4 by omega]
      simp only [show n + 4 - 1 = n + 3 by omega, show n + 4 - 2 = n + 2 by omega]
      simp [a]; push_cast; ring
  · intro n hn
    simp only [a, show ¬ n < 2 by omega, if_false]
    ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simp only [a, show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show ¬ m + 4 < 2 by omega, show ¬ m + 3 < 2 by omega, show ¬ m + 2 < 2 by omega, if_false,
      show m + 4 - 2 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega, show m + 2 - 2 = m by omega]
    push_cast
    ring
