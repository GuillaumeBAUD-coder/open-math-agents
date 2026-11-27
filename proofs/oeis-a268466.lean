import OMAStatements.S_oeis_a268466

-- Complete proof of OEIS A268466 along powers of two n = 2^k
-- Author: Paul Roulleau (@Solfanbtc) via Antigravity NEON-SWARM FACTORY v3

open OMA.S_oeis_a268466

private lemma geom_sum_mod_two (m : ℕ) (hm : m % 2 = 1) (j : ℕ) :
    (∑ i ∈ Finset.range j, m ^ i) % 2 = j % 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih]
    have hpow : m ^ j % 2 = 1 := by
      rw [Nat.pow_mod, hm, one_pow]
      decide
    rw [hpow]
    omega

private lemma geom_sum_mul_add_one (m : ℕ) (hm : 1 ≤ m) (j : ℕ) :
    (m - 1) * (∑ i ∈ Finset.range j, m ^ i) + 1 = m ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, mul_add, add_right_comm, ih, pow_succ']
    calc
      m ^ j + (m - 1) * m ^ j = (1 + (m - 1)) * m ^ j := by ring
      _ = m * m ^ j := by rw [add_comm, Nat.sub_add_cancel hm]

private lemma two_pow_dvd_sub_one (k m : ℕ) (hk : 1 ≤ k) (hm1 : 1 < m)
    (hmod : m ^ m ≡ 1 [MOD 2 ^ k]) : 2 ^ k ∣ (m - 1) := by
  have hm_odd : m % 2 = 1 := by
    by_contra hne
    have hm_even : 2 ∣ m := by omega
    have h2_pow : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
    have hmod2 : m ^ m ≡ 1 [MOD 2] := hmod.of_dvd h2_pow
    have hdvd_pow : 2 ∣ m ^ m := dvd_pow hm_even (by omega)
    have h0 : m ^ m % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd_pow
    rw [Nat.ModEq, h0] at hmod2
    norm_num at hmod2
  have hpow_ge : 1 ≤ m ^ m := Nat.one_le_pow m m (by omega)
  have hdvd_sub : 2 ^ k ∣ (m ^ m - 1) :=
    (Nat.modEq_iff_dvd' hpow_ge).mp hmod.symm
  have hfac : m ^ m - 1 = (m - 1) * (∑ i ∈ Finset.range m, m ^ i) := by
    have h := geom_sum_mul_add_one m (by omega) m
    omega
  rw [hfac] at hdvd_sub
  have hsum_odd : (∑ i ∈ Finset.range m, m ^ i) % 2 = 1 := by
    rw [geom_sum_mod_two m hm_odd m, hm_odd]
  have hcop2 : Nat.Coprime 2 (∑ i ∈ Finset.range m, m ^ i) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
  have hcop : Nat.Coprime (2 ^ k) (∑ i ∈ Finset.range m, m ^ i) :=
    hcop2.pow_left k
  exact hcop.dvd_of_dvd_mul_right hdvd_sub

private lemma a_two_pow (k : ℕ) (hk : 1 ≤ k) : a (2 ^ k) = 2 ^ k + 1 := by
  unfold a
  have hmem : 2 ^ k + 1 ∈ {m : ℕ | 1 < m ∧ m ^ m ≡ 1 [MOD 2 ^ k]} := by
    refine ⟨?_, ?_⟩
    · have h2 : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
      omega
    · have hbase : 2 ^ k + 1 ≡ 1 [MOD 2 ^ k] := by
        rw [Nat.ModEq, Nat.add_mod_left]
      simpa using hbase.pow (2 ^ k + 1)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  refine le_csInf ⟨2 ^ k + 1, hmem⟩ ?_
  rintro m ⟨hm1, hmod⟩
  have hdvd := two_pow_dvd_sub_one k m hk hm1 hmod
  have hle : 2 ^ k ≤ m - 1 := Nat.le_of_dvd (by omega) hdvd
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a268466.main := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro N
  refine ⟨2 ^ (N + 1), ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have h2 : 2 ^ 1 ≤ 2 ^ (N + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · rw [a_two_pow (N + 1) (by omega)]
      have hev : Even (2 ^ (N + 1)) := even_two.pow_of_ne_zero (by omega)
      rw [hev.neg_one_pow]
      push_cast
      ring
  · exact lt_trans (Nat.lt_succ_self N) Nat.lt_two_pow_self
