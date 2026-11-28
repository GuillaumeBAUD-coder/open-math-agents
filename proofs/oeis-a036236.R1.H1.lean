import OMAReductions.R_oeis_a036236_R1

-- Step oeis-a036236.R1.H1: hypothesis H1 of reduction oeis-a036236.R1
-- Credit: @lettucrisp
-- H1 := ∀ j : ℕ, 1 ≤ j → {k : ℕ | 0 < k ∧ 2 ^ k % k = 2 ^ j}.Infinite

private lemma exists_prime_gt_and_modEq_one (n B : ℕ) (hn : 0 < n) :
    ∃ p, B < p ∧ p.Prime ∧ p ≡ 1 [MOD n] := by
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hn) with rfl | hn1
  · obtain ⟨p, hpB, hp⟩ := Nat.exists_infinite_primes (B + 1)
    exact ⟨p, by omega, hp, Nat.modEq_one⟩
  set M := (max B n + 2).factorial
  set q := n * M
  have hM2 : 2 ≤ M := by
    have h2 : 2 ≤ max B n + 2 := by omega
    calc 2 = (2 : ℕ).factorial := by decide
      _ ≤ (max B n + 2).factorial := Nat.factorial_le h2
  have hq2 : 2 ≤ q := by
    dsimp [q]
    nlinarith
  set val : ℤ := (Polynomial.cyclotomic n ℤ).eval (q : ℤ)
  set N := val.natAbs
  have hN1 : 1 < N := by
    have := Polynomial.sub_one_lt_natAbs_cyclotomic_eval hn1 (by omega : q ≠ 1)
    omega
  obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd hN1.ne'
  have : Fact p.Prime := ⟨hp⟩
  have hp_eval : (val : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.natCast_dvd.mpr hpN
  have hmap : (val : ZMod p) =
      (Polynomial.cyclotomic n (ZMod p)).eval ((q : ℤ) : ZMod p) := by
    dsimp [val]
    have h := Polynomial.eval_map_apply (p := Polynomial.cyclotomic n ℤ) (Int.castRingHom (ZMod p)) (q : ℤ)
    simpa [Polynomial.map_cyclotomic] using h.symm
  have hpnq : ¬ p ∣ q := by
    intro hpq
    have hq0 : ((q : ℤ) : ZMod p) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast hpq
    rw [hmap, hq0, ← Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.cyclotomic_coeff_zero (ZMod p) hn1] at hp_eval
    exact one_ne_zero hp_eval
  have hpB : B < p := by
    by_contra hle
    have hle' : p ≤ max B n + 2 := by omega
    exact hpnq (dvd_mul_of_dvd_right (Nat.dvd_factorial hp.pos hle') n)
  have hpn : ¬ p ∣ n := fun h => hpnq (dvd_mul_of_dvd_left h M)
  have : NeZero (n : ZMod p) := ⟨fun h => hpn ((ZMod.natCast_eq_zero_iff n p).mp h)⟩
  have hroot : (Polynomial.cyclotomic n (ZMod p)).IsRoot ((q : ℤ) : ZMod p) := by
    rw [Polynomial.IsRoot.def]
    exact hmap.symm.trans hp_eval
  have hprim : IsPrimitiveRoot ((q : ℤ) : ZMod p) n :=
    (Polynomial.isRoot_cyclotomic_iff).mp hroot
  have hqne : ((q : ℤ) : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    exact hpnq (Int.natCast_dvd_natCast.mp h)
  have hflt : ((q : ℤ) : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hqne
  have hdvd : n ∣ p - 1 := by
    rw [hprim.eq_orderOf]
    exact orderOf_dvd_of_pow_eq_one hflt
  exact ⟨p, hpB, hp, ((Nat.modEq_iff_dvd' hp.one_le).mpr hdvd).symm⟩

theorem OMA.solution : OMA.R_oeis_a036236_R1.H1 := by
  intro j hj
  apply Set.infinite_of_forall_exists_gt
  intro B
  set v := j.factorization 2
  have h2vd : 2 ^ v ∣ j := Nat.ordProj_dvd j 2
  set m := j / 2 ^ v
  have hjm : 2 ^ v * m = j := Nat.mul_div_cancel' h2vd
  have hm_pos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0, mul_zero] at hjm; omega
    · exact hmpos
  have h2ndm : ¬ 2 ∣ m := Nat.not_dvd_ordCompl Nat.prime_two (by omega : j ≠ 0)
  have h2m : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2ndm
  have h2vm : Nat.Coprime (2 ^ v) m := h2m.pow_left v
  have hvj : v ≤ j := by
    have h1 : v < 2 ^ v := Nat.lt_two_pow_self
    have h2 : 2 ^ v ≤ j := Nat.le_of_dvd (by omega) h2vd
    omega
  set N := m.totient
  have hN : 0 < N := Nat.totient_pos.mpr hm_pos
  obtain ⟨p, hp_gt, hp, hp_mod⟩ := exists_prime_gt_and_modEq_one N (max B (max j (2 ^ j))) hN
  have hpB : B < p := lt_of_le_of_lt (le_max_left _ _) hp_gt
  have hpj : j < p := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hp_gt
  have hp2j : 2 ^ j < p := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hp_gt
  set k := j * p
  have hk_pos : 0 < k := Nat.mul_pos (by omega) hp.pos
  have hkB : B < k := lt_of_lt_of_le hpB (Nat.le_mul_of_pos_left p (by omega))
  have hk2j : 2 ^ j < k := lt_of_lt_of_le hp2j (Nat.le_mul_of_pos_left p (by omega))
  have hmod_2v : 2 ^ k ≡ 2 ^ j [MOD 2 ^ v] := by
    have hd1 : 2 ^ v ∣ 2 ^ k := Nat.pow_dvd_pow 2 (hvj.trans (Nat.le_mul_of_pos_right j hp.pos))
    have hd2 : 2 ^ v ∣ 2 ^ j := Nat.pow_dvd_pow 2 hvj
    rw [Nat.ModEq, Nat.mod_eq_zero_of_dvd hd1, Nat.mod_eq_zero_of_dvd hd2]
  have hmod_m : 2 ^ k ≡ 2 ^ j [MOD m] := by
    obtain ⟨r, hr⟩ := (Nat.modEq_iff_dvd' hp.one_le).mp hp_mod.symm
    have hkp : k = j + N * (j * r) := by
      have hp1 : p = 1 + N * r := by omega
      dsimp [k]
      rw [hp1]
      ring
    rw [hkp, pow_add, pow_mul]
    have htot : 2 ^ N ≡ 1 [MOD m] := Nat.ModEq.pow_totient h2m
    have hpow : (2 ^ N) ^ (j * r) ≡ 1 ^ (j * r) [MOD m] := htot.pow (j * r)
    simpa [one_pow, mul_one] using hpow.mul_left (2 ^ j)
  have hmod_j : 2 ^ k ≡ 2 ^ j [MOD j] := by
    have h := (Nat.modEq_and_modEq_iff_modEq_mul h2vm).mp ⟨hmod_2v, hmod_m⟩
    rwa [hjm] at h
  have hmod_p : 2 ^ k ≡ 2 ^ j [MOD p] := by
    have : Fact p.Prime := ⟨hp⟩
    rw [← ZMod.natCast_eq_natCast_iff]
    dsimp [k]
    rw [pow_mul]
    push_cast
    exact ZMod.pow_card ((2 : ZMod p) ^ j)
  have hjp : Nat.Coprime j p := by
    refine (hp.coprime_iff_not_dvd.mpr ?_).symm
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hmod_k : 2 ^ k ≡ 2 ^ j [MOD k] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hjp).mp ⟨hmod_j, hmod_p⟩
  refine ⟨k, ⟨hk_pos, ?_⟩, hkB⟩
  rw [show 2 ^ k % k = 2 ^ j % k from hmod_k, Nat.mod_eq_of_lt hk2j]
