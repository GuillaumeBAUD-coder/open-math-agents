import OMAStatements.S_oeis_a052731
import Mathlib

namespace OMA.S_oeis_a052731

noncomputable def M : PowerSeries ℚ := PowerSeries.mk (fun n => (motzkin n : ℚ))

lemma M_eq : M = 1 + PowerSeries.X * M + PowerSeries.X ^ 2 * M ^ 2 := by
  ext n
  rcases n with _ | _ | n
  · simp [M, motzkin]
  · simp [M, motzkin, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one, PowerSeries.coeff_X_pow_mul']
  · have h1 : PowerSeries.coeff (n + 2) (PowerSeries.X * M) = (motzkin (n + 1) : ℚ) := by
      rw [show n + 2 = (n + 1) + 1 from rfl, PowerSeries.coeff_succ_X_mul]; simp [M]
    have h2 : PowerSeries.coeff (n + 2) (PowerSeries.X ^ 2 * M ^ 2) =
        ∑ i : Fin (n + 1), (motzkin i : ℚ) * (motzkin (n - i) : ℚ) := by
      rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega), show n + 2 - 2 = n by omega, pow_two,
        PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        ]
      simp only [M, PowerSeries.coeff_mk]
      exact (Fin.sum_univ_eq_sum_range (fun i => (motzkin i : ℚ) * (motzkin (n - i) : ℚ)) (n + 1)).symm
    rw [map_add, map_add, h1, h2]
    simp only [PowerSeries.coeff_one]
    rw [if_neg (by omega)]
    simp only [M, PowerSeries.coeff_mk]
    rw [show n + 1 + 1 = n + 2 from rfl, motzkin]
    push_cast
    ring

end OMA.S_oeis_a052731

theorem OMA.solution : type_of% @OMA.S_oeis_a052731.main := by
  open OMA.S_oeis_a052731 in
  refine ⟨1 - PowerSeries.X - 2 * PowerSeries.X ^ 2 * M, by simp [M, motzkin, PowerSeries.coeff_zero_eq_constantCoeff_apply] , ?_, ?_⟩
  · have h := M_eq
    simp only [map_ofNat]
    linear_combination (-4 * PowerSeries.X ^ 2 : PowerSeries ℚ) * h
  · have h : expectedSeries = PowerSeries.X * (M - 1) - PowerSeries.X ^ 2 * M := by
      unfold expectedSeries
      ext n
      rcases n with _ | _ | n
      · simp [M, PowerSeries.coeff_X_pow_mul']
      · simp [M, PowerSeries.coeff_X_pow_mul', motzkin]
      · rw [map_sub, PowerSeries.coeff_X_pow_mul', if_pos (by omega), PowerSeries.coeff_X_pow_mul',
          if_pos (by omega), show n + 1 + 1 - 2 = n by omega, PowerSeries.coeff_mk]
        simp [M, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X, mul_sub]
    rw [h]
    simp only [map_ofNat]
    linear_combination 0
