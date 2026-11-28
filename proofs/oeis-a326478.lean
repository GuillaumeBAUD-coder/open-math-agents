import OMAStatements.S_oeis_a326478
import Mathlib

namespace OMA.P_oeis_a326478

open PowerSeries

theorem inv_sq :
    (((X : PowerSeries ℚ) - 1) ^ 2)⁻¹ = mk fun j => ((j : ℚ) + 1) := by
  rw [eq_comm, PowerSeries.eq_inv_iff_mul_eq_one]
  · have h := mk_add_choose_mul_one_sub_pow_eq_one (S := ℚ) 1
    have e : ((X : PowerSeries ℚ) - 1) ^ 2 = (1 - X) ^ (1 + 1) := by ring
    rw [e]
    convert h using 3
    funext j
    simp [Nat.choose_one_right, add_comm]
  · simp

theorem main_proof :
    ∀ n : ℕ, 1 ≤ n →
      OMA.S_oeis_a326478.a (2 * n) =
        coeff n ((X : PowerSeries ℚ) * (2 * ((X - 1) ^ 2)⁻¹ - 1)) := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [coeff_succ_X_mul, inv_sq]
  have h2 : coeff j (2 * (mk fun j => ((j : ℚ) + 1)) - 1) = 2 * ((j : ℚ) + 1) - if j = 0 then 1 else 0 := by
    rw [map_sub, coeff_one, show (2 : PowerSeries ℚ) = C (2 : ℚ) from map_ofNat C 2 |>.symm,
      coeff_C_mul, coeff_mk]
  rw [h2]
  unfold OMA.S_oeis_a326478.a
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · norm_num [bernoulli_one]
  · have hB : bernoulli (2 * (j + 1) - 1) = 0 :=
      bernoulli_eq_zero_of_odd ⟨j, by omega⟩ (by omega)
    rw [hB]
    simp [hj.ne']

end OMA.P_oeis_a326478

open OMA.P_oeis_a326478 in
theorem OMA.solution : type_of% @OMA.S_oeis_a326478.main := main_proof
