import OMAStatements.S_oeis_a335756
import Mathlib

open OMA.S_oeis_a335756 PowerSeries

theorem P335756.step3 (n : ℕ) : a (n + 3) = a n + (if n % 3 = 0 then 10 else 6) := by
  unfold a
  rw [show (n + 3) % 3 = n % 3 by omega, show (n + 3) / 3 = n / 3 + 1 by omega]
  split_ifs <;> push_cast <;> ring

theorem OMA.solution : type_of% @OMA.S_oeis_a335756.main := by
  refine ⟨?_, ?_⟩
  · have hL : (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X + X ^ 2) ^ 2) : PowerSeries ℚ) = PowerSeries.mk (fun n => (a n : ℚ)) - C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3) + (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 6) := by
      (try simp only [map_ofNat, map_one, map_neg, one_mul, pow_one]) <;> ring
    have hR : (2 * (1 + X ^ 2 + 4 * X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5) : PowerSeries ℚ) = C (2 : ℚ) + C (2 : ℚ) * X ^ 2 + C (8 : ℚ) * X ^ 3 + C (6 : ℚ) * X ^ 4 + C (4 : ℚ) * X ^ 5 := by
      (try simp only [map_ofNat, map_one, map_neg, one_mul, pow_one]) <;> ring
    rw [hL, hR]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk,
      coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
    rcases n with _ | _ | _ | _ | _ | _ | _ | n
    · norm_num [a]
    · norm_num [a]
    · norm_num [a]
    · norm_num [a]
    · norm_num [a]
    · norm_num [a]
    · norm_num [a]
    · have h1 := P335756.step3 (n + 1)
      have h2 := P335756.step3 (n + 4)
      rw [show (n + 4) % 3 = (n + 1) % 3 by omega, show n + 4 + 3 = n + 7 by omega] at h2
      rw [show n + 1 + 3 = n + 4 by omega] at h1
      have e1 : (a (n + 4) : ℚ) = a (n + 1) + ((if (n + 1) % 3 = 0 then 10 else 6 : ℤ) : ℚ) := by exact_mod_cast h1
      have e2 : (a (n + 7) : ℚ) = a (n + 4) + ((if (n + 1) % 3 = 0 then 10 else 6 : ℤ) : ℚ) := by exact_mod_cast h2
      rw [show n + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 7 by omega]
      simp only [show n + 7 - 1 = n + 6 by omega, show n + 7 - 2 = n + 5 by omega, show n + 7 - 3 = n + 4 by omega, show n + 7 - 4 = n + 3 by omega, show n + 7 - 5 = n + 2 by omega, show n + 7 - 6 = n + 1 by omega]
      norm_num
      linarith [e1, e2]
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [show m + 6 - 3 = m + 3 by omega, show m + 6 - 6 = m by omega]
    have h1 := P335756.step3 m
    have h2 := P335756.step3 (m + 3)
    rw [show (m + 3) % 3 = m % 3 by omega, show m + 3 + 3 = m + 6 by omega] at h2
    rw [h2, h1]
    ring
