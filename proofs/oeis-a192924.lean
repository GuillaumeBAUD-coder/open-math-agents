import OMAStatements.S_oeis_a192924

/-!
Proof of R. J. Mathar's recurrence for Clark Kimberling's OEIS A192924.
Substituting the polynomial recursion leaves (X⁴ − 3X² + 1) times an
earlier term. This vanishes modulo X² − X − 1.
Lean proof by KoaOkano, assisted by OpenAI Codex.
-/

open Polynomial OMA.S_oeis_a192924

private noncomputable abbrev modulus : ℤ[X] := X^2 - X - 1

private noncomputable def difference (k : ℕ) : ℤ[X] :=
  let n : ℤ := k + 4
  p (k+4) + (2*(-n+1)) • p (k+3) + (n^2-3*n-1) • p (k+2) +
    (3*(n-2)) • p (k+1) + p k

private theorem divides_difference (k : ℕ) : modulus ∣ difference k := by
  refine ⟨(X^2 + X - 1) * p k, ?_⟩
  simp only [difference, modulus, p, smul_eq_C_mul, Nat.cast_add, Nat.cast_ofNat,
    map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_ofNat, map_natCast]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a192924.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k+4 := ⟨n-4, by omega⟩
  have hm : modulus.Monic := by unfold modulus; monicity!
  have hz : modByMonicHom modulus (difference k) = 0 :=
    (modByMonic_eq_zero_iff_dvd hm).2 (divides_difference k)
  have h := congrArg (lcoeff ℤ 0) hz
  simp only [difference, map_add, map_smul, map_zero, modByMonicHom_apply,
    lcoeff_apply, smul_eq_mul] at h
  unfold a
  simpa only [show k+4-1=k+3 by omega, show k+4-2=k+2 by omega,
    show k+4-3=k+1 by omega, show k+4-4=k by omega, Nat.cast_add, Nat.cast_ofNat] using h
