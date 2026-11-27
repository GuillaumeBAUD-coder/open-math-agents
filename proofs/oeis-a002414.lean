import OMAStatements.S_oeis_a002414
import Mathlib

-- Problem: oeis-a002414
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P002414
open OMA.S_oeis_a002414 PowerSeries

lemma cX (f : ℕ → ℚ) (k n : ℕ) : coeff n (mk f * X ^ k) = if k ≤ n then f (n - k) else 0 := by
  rw [coeff_mul_X_pow']; simp

theorem sol : type_of% @OMA.S_oeis_a002414.main := by
  have l : mk a * (1 - X) ^ 4 =
      mk a * X ^ 0 - C (4 : ℚ) * (mk a * X ^ 1) + C (6 : ℚ) * (mk a * X ^ 2) - C (4 : ℚ) * (mk a * X ^ 3) + mk a * X ^ 4 := by
    simp only [map_ofNat]; ring
  have r : (X : PowerSeries ℚ) * (1 + 5 * X) = X ^ 1 + C (5 : ℚ) * X ^ 2 := by simp only [map_ofNat]; ring
  rw [l, r]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, cX, coeff_X_pow]
  rcases n with _ | _ | _ | _ | n
  all_goals simp [a]
  all_goals norm_num
  all_goals ring


end OMA.P002414

theorem OMA.solution : type_of% @OMA.S_oeis_a002414.main := OMA.P002414.sol
