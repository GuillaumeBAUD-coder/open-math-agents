import OMAReductions.R_Mersenne_squarefree_mersenne_of_prime_R1

-- Step Mersenne.squarefree_mersenne_of_prime.R1.H1
-- Credit: @caa1982

theorem OMA.solution : OMA.R_Mersenne_squarefree_mersenne_of_prime_R1.H1 := by
  intro q p hq hp hsq
  haveI := Fact.mk hp
  have hp_dvd : p ∣ mersenne q := dvd_trans (dvd_pow_self p (by decide : 2 ≠ 0)) hsq
  have hord : orderOf (2 : ZMod p) = q :=
    OMA.R_Mersenne_squarefree_mersenne_of_prime_R1.orderOf_two_eq hq hp hp_dvd
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h2dvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2dvd
    subst hp2
    have hq_pos : 1 ≤ q := hq.one_le
    have heven : 2 ∣ 2 ^ q := dvd_pow_self 2 (by omega)
    have h1 : 2 ∣ 2 ^ q - 1 := hp_dvd
    have := Nat.dvd_sub heven h1
    have hge : 1 ≤ 2 ^ q := Nat.one_le_two_pow
    rw [show 2 ^ q - (2 ^ q - 1) = 1 by omega] at this
    omega
  have hflt : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hqdvd : q ∣ p - 1 := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hflt
  obtain ⟨k, hk⟩ := hqdvd
  have hmodq : 2 ^ q ≡ 1 [MOD p ^ 2] :=
    (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mpr hsq |>.symm
  have hmod : 2 ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
    rw [hk, pow_mul]
    simpa using hmodq.pow k
  exact ⟨hp, (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mp hmod.symm⟩
