import OMAStatements.S_oeis_a192473

/-!
Proof of OEIS A192473: both X and X^2 annihilate T^4 - 4*T^3 + 3*T^2 + 2*T - 1
modulo m = X^2 - X - 1, so the recurrence combination of p(k+5), ..., p(k+1) minus 1
is divisible by m. Taking the coefficient of X after %ₘ m gives the recurrence.
-/

open Polynomial in
theorem OMA.solution : type_of% @OMA.S_oeis_a192473.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  let m : ℤ[X] := X ^ 2 - X - 1
  have hm : m.Monic := by
    dsimp [m]
    rw [sub_sub]
    refine (monic_X_pow 2).sub_of_left ?_
    compute_degree!
  have hm_deg : m.degree = 2 := by
    dsimp [m]
    rw [sub_sub, degree_sub_eq_left_of_degree_lt]
    · simp
    · compute_degree!
  let F : ℤ[X] :=
    OMA.S_oeis_a192473.p (k + 5) -
      (4 : ℤ) • OMA.S_oeis_a192473.p (k + 4) +
      (3 : ℤ) • OMA.S_oeis_a192473.p (k + 3) +
      (2 : ℤ) • OMA.S_oeis_a192473.p (k + 2) -
      OMA.S_oeis_a192473.p (k + 1) - 1
  have hdvd : m ∣ F := by
    refine ⟨X ^ (k + 1) * (X ^ 2 - 3 * X + 1) +
        X ^ (2 * k + 4) * (X ^ 4 - X ^ 2 - 1) * (X ^ 2 + X - 1), ?_⟩
    dsimp [F, OMA.S_oeis_a192473.p, m]
    have hsmul (r : ℤ) (g : ℤ[X]) : r • g = C r * g := smul_eq_C_mul r
    rw [hsmul, hsmul, hsmul]
    have hC4 : (C (4 : ℤ) : ℤ[X]) = 4 := map_ofNat C 4
    have hC3 : (C (3 : ℤ) : ℤ[X]) = 3 := map_ofNat C 3
    have hC2 : (C (2 : ℤ) : ℤ[X]) = 2 := map_ofNat C 2
    rw [hC4, hC3, hC2]
    rw [show 2 * (k + 5) + 2 = (2 * k + 4) + 8 by omega,
      show 2 * (k + 4) + 2 = (2 * k + 4) + 6 by omega,
      show 2 * (k + 3) + 2 = (2 * k + 4) + 4 by omega,
      show 2 * (k + 2) + 2 = (2 * k + 4) + 2 by omega,
      show 2 * (k + 1) + 2 = 2 * k + 4 by omega]
    ring
  have hmod : modByMonicHom m F = 0 := (mem_ker_modByMonic hm).mpr hdvd
  have h1mod : (1 : ℤ[X]) %ₘ m = 1 := by
    rw [modByMonic_eq_self_iff hm, degree_one, hm_deg]
    decide
  have hcoeff := congrArg (fun g : ℤ[X] => g.coeff 1) hmod
  dsimp [F] at hcoeff
  simp only [map_add, map_sub, map_smul, modByMonicHom_apply, h1mod, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul, coeff_one] at hcoeff
  norm_num at hcoeff
  have ha0 : OMA.S_oeis_a192473.a (k + 5) = (OMA.S_oeis_a192473.p (k + 5) %ₘ m).coeff 1 := rfl
  have ha1 : OMA.S_oeis_a192473.a (k + 5 - 1) = (OMA.S_oeis_a192473.p (k + 4) %ₘ m).coeff 1 := rfl
  have ha2 : OMA.S_oeis_a192473.a (k + 5 - 2) = (OMA.S_oeis_a192473.p (k + 3) %ₘ m).coeff 1 := rfl
  have ha3 : OMA.S_oeis_a192473.a (k + 5 - 3) = (OMA.S_oeis_a192473.p (k + 2) %ₘ m).coeff 1 := rfl
  have ha4 : OMA.S_oeis_a192473.a (k + 5 - 4) = (OMA.S_oeis_a192473.p (k + 1) %ₘ m).coeff 1 := rfl
  rw [ha0, ha1, ha2, ha3, ha4]
  linarith
