import OMAStatements.S_oeis_a192745
import Mathlib

open Polynomial OMA.S_oeis_a192745 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192745.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have m : (X^2 - X - 1 : ℤ[X]).Monic := by monicity!
  have d (c : ℤ) : (C c : ℤ[X]) %ₘ (X^2-X-1) = C c :=
    (modByMonic_eq_self_iff m).2 (degree_C_le.trans_lt (by
      rw [show (X^2-X-1 : ℤ[X]).degree = 2 by compute_degree!]
      norm_num))
  have e : p (k+3) - C ((k:ℤ)+3) * p (k+2) + C ((k:ℤ)+1) * p (k+1) + C ((k:ℤ)+2) * p k =
      (X^2-X-1) * ((X - C ((k:ℤ)+2)) * p k + C ((k+1).factorial:ℤ)) +
        C (((k:ℤ)+2)*(k+1).factorial) := by
    simp [p, Nat.factorial_succ]
    ring
  have h := congrArg (fun f => (f %ₘ (X^2-X-1)).coeff 1) e
  simp only [← smul_eq_C_mul, add_modByMonic, sub_modByMonic, smul_modByMonic,
    self_mul_modByMonic m, d, coeff_add, coeff_sub, coeff_smul, coeff_C_succ, zero_add,
    smul_eq_mul] at h
  simp [a]
  linear_combination h
