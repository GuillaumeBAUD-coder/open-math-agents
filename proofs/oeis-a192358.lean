import OMAStatements.S_oeis_a192358

/-!
Proof of Colin Barker's recurrence for Clark Kimberling's OEIS A192358.
Both shifts of X satisfy the same quartic modulo X² − X − 1. Taking the
linear coefficient of the reduced polynomial therefore gives the recurrence.
Lean proof by KoaOkano, assisted by OpenAI Codex.
-/

open Polynomial OMA.S_oeis_a192358

private noncomputable abbrev modulus : ℚ[X] := X ^ 2 - X - 1

private noncomputable def difference (k : ℕ) : ℚ[X] :=
  p (k + 4) - 2 • p (k + 3) - 19 • p (k + 2) + 20 • p (k + 1) + 55 • p k

private theorem modulus_dvd_difference (k : ℕ) : modulus ∣ difference k := by
  refine ⟨C (1 / 2) * ((X + 3) ^ k * (X ^ 2 + 11 * X + 29) +
    (X - 3) ^ k * (X ^ 2 - 13 * X + 41)), ?_⟩
  simp only [difference, p, modulus, pow_add, nsmul_eq_mul, Nat.cast_ofNat,
    map_ofNat]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a192358.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have hm : modulus.Monic := by unfold modulus; monicity!
  have hz : modByMonicHom modulus (difference k) = 0 :=
    (modByMonic_eq_zero_iff_dvd hm).2 (modulus_dvd_difference k)
  have h := congrArg (lcoeff ℚ 1) hz
  simp only [difference, map_add, map_sub, map_nsmul, map_zero] at h
  simp only [modByMonicHom_apply, lcoeff_apply, nsmul_eq_mul, Nat.cast_ofNat] at h
  unfold a
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega,
    show k + 4 - 1 = k + 3 by omega, show k + 3 - 1 = k + 2 by omega,
    show k + 2 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega]
  change (p (k + 4) %ₘ modulus).coeff 1 = _
  linarith
