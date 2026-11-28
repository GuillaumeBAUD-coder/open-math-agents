import OMAStatements.S_oeis_a223906
import Mathlib

-- Proof of Colin Barker's conjecture in OEIS A223906 (statement by @ivillar).
-- Idea: the unsigned Stirling numbers of row 3 are 0, 2, 3, 1, so a(n) = 2*2^n + 3*3^n + 4^n;
-- the generating function is then checked coefficientwise after multiplying by its denominator.

namespace OMAA223906Helpers

open PowerSeries OMA.S_oeis_a223906

theorem a_eq (n : ℕ) : a n = 2 ^ (1 + n) + 3 ^ (1 + n) + 4 ^ n := by
  simp only [a, hatC, Finset.sum_range_succ, Finset.sum_range_zero]
  have h0 : Nat.stirlingFirst 3 0 = 0 := by decide
  have h1 : Nat.stirlingFirst 3 1 = 2 := by decide
  have h2 : Nat.stirlingFirst 3 2 = 3 := by decide
  have h3 : Nat.stirlingFirst 3 3 = 1 := by decide
  rw [h0, h1, h2, h3]
  simp only [zpow_neg, zpow_natCast, div_inv_eq_mul]
  push_cast
  ring

def g (n : ℕ) : ℚ := if n = 0 then 0 else 2 ^ (1 + n) + 3 ^ (1 + n) + 4 ^ n

theorem key : mk g * ((2 * X - 1) * (3 * X - 1) * (4 * X - 1)) =
    (-X * (144 * X ^ 2 - 102 * X + 17) : ℚ⟦X⟧) := by
  have e1 : mk g * ((2 * X - 1) * (3 * X - 1) * (4 * X - 1)) =
      C (24 : ℚ) * (mk g * X ^ 3) - C (26 : ℚ) * (mk g * X ^ 2) + C (9 : ℚ) * (mk g * X ^ 1) -
        mk g := by
    rw [map_ofNat C 24, map_ofNat C 26, map_ofNat C 9]
    ring
  have e2 : (-X * (144 * X ^ 2 - 102 * X + 17) : ℚ⟦X⟧) =
      C (102 : ℚ) * X ^ 2 - C (144 : ℚ) * X ^ 3 - C (17 : ℚ) * X ^ 1 := by
    rw [map_ofNat C 102, map_ofNat C 144, map_ofNat C 17]
    ring
  rw [e1, e2]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mk, coeff_mul_X_pow', coeff_C]
  rcases n with _ | _ | _ | _ | n
  · simp [g]
  · simp [g]; norm_num
  · simp [g]; norm_num
  · simp [g]; norm_num
  · simp only [show 3 ≤ n + 4 by omega, show 2 ≤ n + 4 by omega, show 1 ≤ n + 4 by omega,
      show n + 4 - 3 = n + 1 by omega, show n + 4 - 2 = n + 2 by omega,
      show n + 4 - 1 = n + 3 by omega, if_true, g,
      show ¬ (n + 4 = 0) by omega, show ¬ (n + 1 = 0) by omega, show ¬ (n + 2 = 0) by omega,
      show ¬ (n + 3 = 0) by omega, if_false]
    simp
    ring

end OMAA223906Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a223906.main := by
  refine ⟨fun n _ => OMAA223906Helpers.a_eq n, ?_⟩
  have hfun : (fun n => if n = 0 then 0 else OMA.S_oeis_a223906.a n) = OMAA223906Helpers.g := by
    funext n
    simp only [OMAA223906Helpers.g, OMAA223906Helpers.a_eq]
  rw [hfun, PowerSeries.eq_mul_inv_iff_mul_eq (by simp), OMAA223906Helpers.key]
