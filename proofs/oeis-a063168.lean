import OMAStatements.S_oeis_a063168
import Mathlib

namespace OMA.S_oeis_a063168
open PowerSeries

lemma gf_aux (n : ℕ) : coeff n ((mk (fun n => (a n : ℚ))) * (1 - X) ^ 2) =
    (a n : ℚ) - 2 * (if 1 ≤ n then (a (n-1) : ℚ) else 0) + (if 2 ≤ n then (a (n-2) : ℚ) else 0) := by
  have h : (1 - X : PowerSeries ℚ) ^ 2 = 1 - C (2:ℚ) * X ^ 1 + X ^ 2 := by
    simp only [map_ofNat]; ring
  have e : (mk (fun n => (a n : ℚ))) * (1 - C (2:ℚ) * X ^ 1 + X ^ 2) =
      (mk (fun n => (a n : ℚ))) - C (2:ℚ) * ((mk (fun n => (a n : ℚ))) * X ^ 1)
        + (mk (fun n => (a n : ℚ))) * X ^ 2 := by ring
  rw [h, e, map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mul_X_pow']
  simp [coeff_mk]

lemma rhs_aux (n : ℕ) : coeff n (X * (X ^ 2 + 22 * X + 7) : PowerSeries ℚ) =
    (if n = 3 then 1 else 0) + 22 * (if n = 2 then 1 else 0) + 7 * (if n = 1 then 1 else 0) := by
  have h : (X * (X ^ 2 + 22 * X + 7) : PowerSeries ℚ) = X ^ 3 + C (22:ℚ) * X ^ 2 + C (7:ℚ) * X ^ 1 := by
    simp only [map_ofNat]; ring
  rw [h, map_add, map_add, coeff_C_mul, coeff_C_mul, coeff_X_pow, coeff_X_pow, coeff_X_pow]

end OMA.S_oeis_a063168

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a063168.main := by
  open OMA.S_oeis_a063168 in
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simp only [a]
    split_ifs <;> first | omega | (exfalso; omega)
  · ext n
    rw [gf_aux, rhs_aux]
    rcases n with _ | _ | _ | _ | n
    · simp [a]
    · simp [a]
    · simp [a]; norm_num
    · simp [a]; norm_num
    · simp [a]
      push_cast
      ring
