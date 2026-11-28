import OMAStatements.S_oeis_a192989
import Mathlib

open OMA.S_oeis_a192989 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a192989.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have h : derivative ℚ egf = (3 + 6*X + 3*X^2) * egf := by
    rw [egf, derivative_subst (HasSubst.of_constantCoeff_zero' (by simp)), derivative_exp]
    simp [Derivation.leibniz, pow_succ]
    ring
  simp only [← map_ofNat (C (R := ℚ))] at h
  have c := congrArg (coeff (k+2)) h
  simp [add_mul, mul_assoc, pow_succ, coeff_derivative, a, Nat.factorial_succ] at c ⊢
  linear_combination (k.factorial * (k+1) * (k+2) : ℚ) * c
