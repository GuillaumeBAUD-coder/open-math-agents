import OMAStatements.S_oeis_a298024
import Mathlib

namespace OMA.S_oeis_a298024
open PowerSeries

lemma key : (1 - X - X ^ 3 + X ^ 4 : PowerSeries ℚ) * G =
    1 + 3 * X + 6 * X ^ 2 + 3 * X ^ 3 + X ^ 4 := by
  have h : ((1 - X) * (1 - X ^ 3) : PowerSeries ℚ) * ((1 - X) * (1 - X ^ 3))⁻¹ = 1 := by
    apply PowerSeries.mul_inv_cancel
    simp
  have e : (1 - X - X ^ 3 + X ^ 4 : PowerSeries ℚ) = (1 - X) * (1 - X ^ 3) := by ring
  unfold G
  rw [e, mul_comm (1 + 3 * X + 6 * X ^ 2 + 3 * X ^ 3 + X ^ 4 : PowerSeries ℚ), ← mul_assoc, h, one_mul]

end OMA.S_oeis_a298024

theorem OMA.solution : type_of% @OMA.S_oeis_a298024.main := by
  intro n hn
  have h := congrArg (PowerSeries.coeff (n + 0)) OMA.S_oeis_a298024.key
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have e1 : (1 - PowerSeries.X - PowerSeries.X ^ 3 + PowerSeries.X ^ 4 : PowerSeries ℚ) * OMA.S_oeis_a298024.G
      = OMA.S_oeis_a298024.G - PowerSeries.X ^ 1 * OMA.S_oeis_a298024.G - PowerSeries.X ^ 3 * OMA.S_oeis_a298024.G + PowerSeries.X ^ 4 * OMA.S_oeis_a298024.G := by ring
  rw [e1] at h
  have c1 := PowerSeries.coeff_X_pow_mul OMA.S_oeis_a298024.G 1 (m + 4)
  have c3 := PowerSeries.coeff_X_pow_mul OMA.S_oeis_a298024.G 3 (m + 2)
  have c4 := PowerSeries.coeff_X_pow_mul OMA.S_oeis_a298024.G 4 (m + 1)
  have e5 : m + 5 + 0 = m + 4 + 1 := rfl
  have z : PowerSeries.coeff (m + 5) (1 + 3 * PowerSeries.X + 6 * PowerSeries.X ^ 2 + 3 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4 : PowerSeries ℚ) = 0 := by
    have t : (1 + 3 * PowerSeries.X + 6 * PowerSeries.X ^ 2 + 3 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4 : PowerSeries ℚ)
        = 1 + PowerSeries.C (3:ℚ) * PowerSeries.X + PowerSeries.C (6:ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (3:ℚ) * PowerSeries.X ^ 3 + PowerSeries.X ^ 4 := by
      simp [map_ofNat]
    rw [t]
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
    simp
  rw [z] at h
  simp only [map_add, map_sub] at h
  have n1 : m + 4 + 1 = m + 5 := rfl
  have n3 : m + 2 + 3 = m + 5 := rfl
  have n4 : m + 1 + 4 = m + 5 := rfl
  rw [n1] at c1
  rw [n3] at c3
  rw [n4] at c4
  rw [add_zero, c1, c3, c4] at h
  show OMA.S_oeis_a298024.a (m+5) = OMA.S_oeis_a298024.a (m+5-1) + OMA.S_oeis_a298024.a (m+5-3) - OMA.S_oeis_a298024.a (m+5-4)
  have a1 : m + 5 - 1 = m + 4 := by omega
  have a3 : m + 5 - 3 = m + 2 := by omega
  have a4 : m + 5 - 4 = m + 1 := by omega
  rw [a1, a3, a4]
  unfold OMA.S_oeis_a298024.a
  linarith
