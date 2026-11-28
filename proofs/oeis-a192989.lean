import OMAStatements.S_oeis_a192989
import Mathlib

open OMA.S_oeis_a192989

namespace A192989Proof
open PowerSeries

theorem deriv_egf : d⁄dX ℚ egf = egf * (3 * (1 + X) ^ 2) := by
  have hg : HasSubst ((1 + X) ^ 3 - 1 : PowerSeries ℚ) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  unfold egf
  rw [derivative_subst hg, derivative_exp]
  congr 1
  rw [map_sub, derivative_one, sub_zero, derivative_pow, map_add, derivative_one, derivative_X]
  norm_num

theorem coeff_rec (m : ℕ) :
    coeff (m + 3) egf * (m + 3) =
      3 * coeff (m + 2) egf + 6 * coeff (m + 1) egf + 3 * coeff m egf := by
  have h := congrArg (coeff (m + 2)) deriv_egf
  rw [coeff_derivative] at h
  have e : egf * (3 * (1 + X) ^ 2) =
      (3:ℚ) • egf + (6:ℚ) • (X * egf) + (3:ℚ) • (X ^ 2 * egf) := by
    rw [smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul]
    simp only [map_ofNat]
    ring
  rw [e] at h
  simp only [map_add, coeff_smul, smul_eq_mul] at h
  rw [show m + 2 = (m + 1) + 1 by ring, coeff_succ_X_mul, show m + 1 + 1 = m + 2 by ring,
    coeff_X_pow_mul', if_pos (by omega)] at h
  simp only [Nat.add_sub_cancel] at h
  push_cast at h
  rw [show m + 1 + 1 + 1 = m + 3 by ring] at h
  linear_combination h

end A192989Proof

open A192989Proof PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a192989.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h := coeff_rec m
  simp only [a, show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  have f3 : ((m + 3).factorial : ℚ) = (m + 3) * (m + 2) * (m + 1) * m.factorial := by
    rw [show m + 3 = m + 2 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have f2 : ((m + 2).factorial : ℚ) = (m + 2) * (m + 1) * m.factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have f1 : ((m + 1).factorial : ℚ) = (m + 1) * m.factorial := by
    rw [Nat.factorial_succ]
    push_cast; ring
  rw [f3, f2, f1]
  push_cast
  linear_combination ((m : ℚ) + 2) * ((m : ℚ) + 1) * (Nat.factorial m : ℚ) * h
