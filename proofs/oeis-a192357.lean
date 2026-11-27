import OMAStatements.S_oeis_a192357
import Mathlib

open Polynomial

namespace OMA.A192357Aux

lemma hq : (X ^ 2 - X - 1 : ℚ[X]).Monic := by
  have : (X ^ 2 - X - 1 : ℚ[X]) = X ^ 2 - (X + 1) := by ring
  rw [this]
  apply Monic.sub_of_left (monic_X_pow 2)
  rw [degree_X_pow]
  compute_degree!

end OMA.A192357Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a192357.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simp only [OMA.S_oeis_a192357.a, show m + 4 - 1 = m + 3 by omega,
    show m + 5 - 2 - 1 = m + 2 by omega, show m + 5 - 3 - 1 = m + 1 by omega,
    show m + 5 - 4 - 1 = m by omega, show m + 5 - 1 = m + 4 by omega]
  open OMA.S_oeis_a192357 in
  have key : ((p (m + 4) - ((2 : ℚ) • p (m + 3) + (19 : ℚ) • p (m + 2) - (20 : ℚ) • p (m + 1)
      - (55 : ℚ) • p m)) %ₘ (X ^ 2 - X - 1)) = 0 := by
    rw [modByMonic_eq_zero_iff_dvd OMA.A192357Aux.hq]
    refine ⟨C (1 / 2) * ((X + C 3) ^ m * (X ^ 2 + 11 * X + 29)
      + (X - C 3) ^ m * (X ^ 2 - 13 * X + 41)), ?_⟩
    simp only [p, smul_eq_C_mul]
    simp only [map_ofNat] at *
    ring
  have h1 := congrArg (fun P => Polynomial.coeff P 0) key
  simp only [sub_modByMonic, add_modByMonic, smul_modByMonic, coeff_sub, coeff_add,
    coeff_smul, coeff_zero, smul_eq_mul] at h1
  linarith
