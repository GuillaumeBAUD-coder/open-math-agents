import OMAReductions.R_OeisA262781_conjecture_2_R1

-- Step OeisA262781.conjecture_2.R1.H1
-- Credit: @caa1982

private lemma totient_sq_eq (m : ℕ) : Nat.totient (m ^ 2) = m * Nat.totient m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · have h := Nat.totient_gcd_mul_totient_mul m m
    rw [Nat.gcd_self, ← sq] at h
    have hpos : 0 < Nat.totient m := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)
    have h' : Nat.totient m * Nat.totient (m ^ 2) = Nat.totient m * (m * Nat.totient m) := by
      linarith
    exact Nat.eq_of_mul_eq_mul_left hpos h'

private lemma odd_le_totient_sq (m : ℕ) (hm : Odd m) : m ≤ Nat.totient m ^ 2 := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases hm1 : m ≤ 1
    · obtain ⟨k, rfl⟩ := hm
      have : k = 0 := by omega
      subst this
      simp
    have hgt1 : 1 < m := by omega
    let p := m.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hp_odd : Odd p := hm.of_dvd_nat (Nat.minFac_dvd m)
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      obtain ⟨r, hr⟩ := hp_odd
      omega
    let k := m.factorization p
    have hk : 1 ≤ k := (hp.dvd_iff_one_le_factorization (by omega)).mp (Nat.minFac_dvd m)
    let u := m / p ^ k
    have hpk_dvd : p ^ k ∣ m := Nat.ordProj_dvd m p
    have hm_eq : p ^ k * u = m := Nat.mul_div_cancel' hpk_dvd
    have hcop : (p ^ k).Coprime u := (Nat.coprime_ordCompl hp (by omega)).pow_left k
    have hu_odd : Odd u := hm.of_dvd_nat ⟨p ^ k, by rw [mul_comm, hm_eq]⟩
    have hu_lt : u < m := by
      have hpk1 : 1 < p ^ k := one_lt_pow₀ hp.one_lt (by omega)
      have hu_pos : 0 < u := Nat.pos_of_ne_zero fun hu0 => by
        rw [hu0, mul_zero] at hm_eq
        omega
      nlinarith
    have hpk_le : p ^ k ≤ Nat.totient (p ^ k) ^ 2 := by
      rw [Nat.totient_prime_pow hp (by omega)]
      have h1 : p ^ k = p ^ (k - 1) * p := by
        rw [← pow_succ, Nat.sub_add_cancel hk]
      have h2 : p ≤ (p - 1) ^ 2 := by
        obtain ⟨r, hr⟩ : ∃ r, p = r + 3 := ⟨p - 3, by omega⟩
        rw [hr, show r + 3 - 1 = r + 2 by omega]
        nlinarith
      have h3 : 1 ≤ p ^ (k - 1) := Nat.one_le_pow _ _ hp.pos
      calc p ^ k = p ^ (k - 1) * p := h1
        _ ≤ p ^ (k - 1) * (p ^ (k - 1) * (p - 1) ^ 2) := by
          apply Nat.mul_le_mul_left
          nlinarith
        _ = (p ^ (k - 1) * (p - 1)) ^ 2 := by ring
    have hu_le : u ≤ Nat.totient u ^ 2 := ih u hu_lt hu_odd
    rw [← hm_eq, Nat.totient_mul hcop, mul_pow]
    exact Nat.mul_le_mul hpk_le hu_le

private lemma le_two_mul_totient_sq (m : ℕ) (hm : 0 < m) : m ≤ 2 * Nat.totient m ^ 2 := by
  let k := m.factorization 2
  let u := m / 2 ^ k
  have h2k_dvd : 2 ^ k ∣ m := Nat.ordProj_dvd m 2
  have hm_eq : 2 ^ k * u = m := Nat.mul_div_cancel' h2k_dvd
  have hcop : (2 ^ k).Coprime u := (Nat.coprime_ordCompl Nat.prime_two hm.ne').pow_left k
  have hu_odd : Odd u := by
    rw [Nat.odd_iff]
    by_contra h
    have h2u : 2 ∣ u := Nat.dvd_of_mod_eq_zero (by omega)
    have h2_cop : Nat.Coprime 2 u := by
      have : ¬ 2 ∣ u := Nat.not_dvd_ordCompl Nat.prime_two hm.ne'
      exact (Nat.prime_two.coprime_iff_not_dvd).mpr this
    exact (Nat.prime_two.coprime_iff_not_dvd.mp h2_cop) h2u
  have h2k_le : 2 ^ k ≤ 2 * Nat.totient (2 ^ k) ^ 2 := by
    cases k with
    | zero => norm_num
    | succ r =>
      rw [Nat.totient_prime_pow_succ Nat.prime_two r]
      have h1 : 1 ≤ 2 ^ r := Nat.one_le_pow _ _ (by omega)
      rw [pow_succ]
      nlinarith
  have hu_le : u ≤ Nat.totient u ^ 2 := odd_le_totient_sq u hu_odd
  rw [← hm_eq, Nat.totient_mul hcop, mul_pow]
  calc 2 ^ k * u ≤ (2 * Nat.totient (2 ^ k) ^ 2) * Nat.totient u ^ 2 :=
        Nat.mul_le_mul h2k_le hu_le
    _ = 2 * (Nat.totient (2 ^ k) ^ 2 * Nat.totient u ^ 2) := by ring

private lemma totient_sq_gt_649_of_ge_95 (m : ℕ) (hm : 95 ≤ m) :
    649 < Nat.totient (m ^ 2) := by
  rw [totient_sq_eq]
  have h1 := le_two_mul_totient_sq m (by omega)
  have h2 : m ^ 3 ≤ 2 * (m * Nat.totient m) ^ 2 := by
    have : m ^ 2 * m ≤ m ^ 2 * (2 * Nat.totient m ^ 2) := Nat.mul_le_mul_left _ h1
    nlinarith
  have h3 : 95 ^ 3 ≤ m ^ 3 := Nat.pow_le_pow_left hm 3
  nlinarith

private lemma totient_sq_gt_649_mid :
    ∀ m ∈ Finset.Icc 43 94, 649 < m * Nat.totient m := by decide +kernel

private lemma totient_sq_gt_649 (m : ℕ) (hm : 43 ≤ m) : 649 < Nat.totient (m ^ 2) := by
  by_cases h95 : 95 ≤ m
  · exact totient_sq_gt_649_of_ge_95 m h95
  · rw [totient_sq_eq]
    exact totient_sq_gt_649_mid m (Finset.mem_Icc.mpr ⟨hm, by omega⟩)

private def phiSqTbl (m : ℕ) : ℕ :=
  match m with
  | 1 => 1 | 2 => 2 | 3 => 6 | 4 => 8 | 5 => 20 | 6 => 12 | 7 => 42 | 8 => 32
  | 9 => 54 | 10 => 40 | 11 => 110 | 12 => 48 | 13 => 156 | 14 => 84 | 15 => 120 | 16 => 128
  | 17 => 272 | 18 => 108 | 19 => 342 | 20 => 160 | 21 => 252 | 22 => 220 | 23 => 506 | 24 => 192
  | 25 => 500 | 26 => 312 | 27 => 486 | 28 => 336 | 29 => 812 | 30 => 240 | 31 => 930 | 32 => 512
  | 33 => 660 | 34 => 544 | 35 => 840 | 36 => 432 | 37 => 1332 | 38 => 684 | 39 => 936 | 40 => 640
  | 41 => 1640 | 42 => 504 | _ => 0

private lemma phiSqTbl_eq : ∀ m ∈ Finset.Icc 1 42, m * Nat.totient m = phiSqTbl m := by
  decide +kernel

private def aFast (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (min (n + 1) 26),
    ∑ y ∈ Finset.Ico 1 (min (n + 1) 43),
      ∑ z ∈ Finset.Ico y (min (n + 1) 43),
        if (y.Prime ∨ z.Prime) ∧ x ^ 2 + phiSqTbl y + phiSqTbl z = n then 1 else 0

private lemma a_eq_aFast {n : ℕ} (hn : n ≤ 649) : OeisA262781.a n = aFast n := by
  unfold OeisA262781.a aFast
  rw [← Finset.sum_subset (Finset.range_mono (Nat.min_le_left _ _))]
  · apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.sum_subset (Finset.Ico_subset_Ico_right (Nat.min_le_left _ _))]
    · apply Finset.sum_congr rfl
      intro y hy
      have hy_bounds : 1 ≤ y ∧ y ≤ 42 := by
        simp only [Finset.mem_Ico] at hy
        omega
      rw [← Finset.sum_subset (Finset.Ico_subset_Ico_right (Nat.min_le_left _ _))]
      · apply Finset.sum_congr rfl
        intro z hz
        have hz_bounds : 1 ≤ z ∧ z ≤ 42 := by
          simp only [Finset.mem_Ico] at hz
          omega
        rw [totient_sq_eq y, totient_sq_eq z,
          phiSqTbl_eq y (Finset.mem_Icc.mpr hy_bounds),
          phiSqTbl_eq z (Finset.mem_Icc.mpr hz_bounds)]
      · intro z hz hzn
        have hz43 : 43 ≤ z := by
          simp only [Finset.mem_Ico] at hz hzn
          omega
        have hgt := totient_sq_gt_649 z hz43
        simp only [ite_eq_right_iff]
        intro hcond
        omega
    · intro y hy hyn
      have hy43 : 43 ≤ y := by
        simp only [Finset.mem_Ico] at hy hyn
        omega
      apply Finset.sum_eq_zero
      intro z _
      have hgt := totient_sq_gt_649 y hy43
      simp only [ite_eq_right_iff]
      intro hcond
      omega
  · intro x hx hxn
    have hx26 : 26 ≤ x := by
      simp only [Finset.mem_range] at hx hxn
      omega
    apply Finset.sum_eq_zero
    intro y _
    apply Finset.sum_eq_zero
    intro z _
    have hx2 : 676 ≤ x ^ 2 := by nlinarith
    simp only [ite_eq_right_iff]
    intro hcond
    omega

private lemma hFast :
    ∀ n ∈ ({3, 5, 9, 10, 17, 20, 24, 25, 31, 36, 45, 73, 80, 101, 136, 145, 388, 649} : Finset ℕ),
      aFast n = 1 := by decide +kernel

theorem OMA.solution : OMA.R_OeisA262781_conjecture_2_R1.H1 := by
  intro n hn
  have hle : n ≤ 649 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    omega
  rw [a_eq_aFast hle]
  exact hFast n hn
