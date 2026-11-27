import OMAStatements.S_oeis_a387064

open Finset

namespace OMA.Proof_oeis_a387064

private lemma not_pow_dvd_choose_of_lt {p k r j : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    (hr : r < p ^ k) (hjr : j ≤ r) : ¬ p ^ k ∣ Nat.choose r j := by
  have : Fact p.Prime := ⟨hp⟩
  have hlog : Nat.log p r < k := Nat.log_lt_of_lt_pow' (by omega) hr
  have hval := padicValNat_choose (p := p) hjr hlog
  have hlt : padicValNat p (Nat.choose r j) < k := by
    rw [hval]
    calc ((Ico 1 k).filter fun i => p ^ i ≤ j % p ^ i + (r - j) % p ^ i).card
        ≤ (Ico 1 k).card := card_filter_le _ _
      _ = k - 1 := Nat.card_Ico 1 k
      _ < k := by omega
  rw [padicValNat_dvd_iff_le (Nat.choose_pos hjr).ne']
  omega

private lemma pow_dvd_choose_pow_iff {p k j : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    (hj : j ≤ p ^ k) : p ^ k ∣ Nat.choose (p ^ k) j ↔ ¬ p ∣ j := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hj0 : j = 0
  · subst hj0
    simp [hp.ne_one]
    omega
  by_cases hjn : j = p ^ k
  · subst hjn
    simp [hp.ne_one]
  have hlog : Nat.log p (p ^ k) < k + 1 := by
    rw [Nat.log_pow hp.one_lt]
    omega
  have hval := padicValNat_choose (p := p) hj hlog
  rw [padicValNat_dvd_iff_le (Nat.choose_pos hj).ne', hval]
  constructor
  · intro hle hdvd
    have hnot : 1 ∉ (Ico 1 (k + 1)).filter fun i =>
        p ^ i ≤ j % p ^ i + (p ^ k - j) % p ^ i := by
      simp only [mem_filter, mem_Ico, pow_one, not_and, not_le]
      intro _
      have h1 : j % p = 0 := Nat.mod_eq_zero_of_dvd hdvd
      have hpk : p ∣ p ^ k := dvd_pow_self p (by omega)
      have h2 : (p ^ k - j) % p = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_sub hpk hdvd)
      rw [h1, h2]
      exact hp.pos
    have hssub : ((Ico 1 (k + 1)).filter fun i =>
        p ^ i ≤ j % p ^ i + (p ^ k - j) % p ^ i) ⊂ Ico 1 (k + 1) := by
      rw [ssubset_iff_of_subset (filter_subset _ _)]
      exact ⟨1, mem_Ico.mpr ⟨le_rfl, by omega⟩, hnot⟩
    have hlt := card_lt_card hssub
    rw [Nat.card_Ico 1 (k + 1)] at hlt
    omega
  · intro hndvd
    have hall : (Ico 1 (k + 1)).filter (fun i =>
        p ^ i ≤ j % p ^ i + (p ^ k - j) % p ^ i) = Ico 1 (k + 1) := by
      rw [filter_eq_self]
      intro i hi
      rw [mem_Ico] at hi
      have hpi_dvd : p ^ i ∣ p ^ k := Nat.pow_dvd_pow p (Nat.lt_succ_iff.mp hi.2)
      have hsum_mod : (j % p ^ i + (p ^ k - j) % p ^ i) % p ^ i = 0 := by
        rw [← Nat.add_mod, Nat.add_sub_of_le hj]
        exact Nat.mod_eq_zero_of_dvd hpi_dvd
      have hsum_dvd : p ^ i ∣ j % p ^ i + (p ^ k - j) % p ^ i :=
        Nat.dvd_of_mod_eq_zero hsum_mod
      have hj_ndvd : ¬ p ^ i ∣ j := fun h =>
        hndvd (dvd_trans (dvd_pow_self p (by omega)) h)
      have hj_mod_pos : 0 < j % p ^ i :=
        Nat.pos_of_ne_zero (mt Nat.dvd_of_mod_eq_zero hj_ndvd)
      exact Nat.le_of_dvd (Nat.add_pos_left hj_mod_pos _) hsum_dvd
    rw [hall, Nat.card_Ico 1 (k + 1)]
    omega

end OMA.Proof_oeis_a387064

theorem OMA.solution : type_of% @OMA.S_oeis_a387064.main := by
  intro p k hp hk
  rw [OMA.S_oeis_a387064.a, Finset.sum_range_succ]
  have hzero : ∑ r ∈ Finset.range (p ^ k),
      ((Finset.range (r + 1)).filter fun j => p ^ k ∣ Nat.choose r j).card = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [Finset.mem_range] at hr
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j hj
    rw [Finset.mem_range] at hj
    exact OMA.Proof_oeis_a387064.not_pow_dvd_choose_of_lt hp hk hr (Nat.lt_succ_iff.mp hj)
  rw [hzero, zero_add]
  have hcongr : (Finset.range (p ^ k + 1)).filter (fun j => p ^ k ∣ Nat.choose (p ^ k) j) =
      (Finset.range (p ^ k)).filter (fun j => ¬ p ∣ j) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hj, hdvd⟩
      have hjle : j ≤ p ^ k := Nat.lt_succ_iff.mp hj
      have hndvd := (OMA.Proof_oeis_a387064.pow_dvd_choose_pow_iff hp hk hjle).mp hdvd
      refine ⟨lt_of_le_of_ne hjle ?_, hndvd⟩
      rintro rfl
      exact hndvd (dvd_pow_self p (by omega))
    · rintro ⟨hj, hndvd⟩
      refine ⟨Nat.lt_succ_of_lt hj, ?_⟩
      exact (OMA.Proof_oeis_a387064.pow_dvd_choose_pow_iff hp hk hj.le).mpr hndvd
  rw [hcongr]
  have hdiv : (Finset.range (p ^ k)).filter (fun j => p ∣ j) =
      (Finset.range (p ^ (k - 1))).image (fun m => p * m) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hj, m, rfl⟩
      refine ⟨m, ?_, rfl⟩
      have hpk : p * m < p * p ^ (k - 1) := by
        simpa only [← pow_succ', Nat.sub_add_cancel hk] using hj
      exact Nat.lt_of_mul_lt_mul_left hpk
    · rintro ⟨m, hm, rfl⟩
      refine ⟨?_, m, rfl⟩
      calc p * m < p * p ^ (k - 1) := Nat.mul_lt_mul_of_pos_left hm hp.pos
        _ = p ^ k := by rw [← pow_succ', Nat.sub_add_cancel hk]
  have hcard_div : ((Finset.range (p ^ k)).filter fun j => p ∣ j).card = p ^ (k - 1) := by
    rw [hdiv, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hp.pos h),
      Finset.card_range]
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.range (p ^ k)) (fun j => p ∣ j)
  rw [Finset.card_range, hcard_div] at hsplit
  have hpow : p ^ (k - 1) + (p - 1) * p ^ (k - 1) = p ^ k := by
    calc p ^ (k - 1) + (p - 1) * p ^ (k - 1)
        = (1 + (p - 1)) * p ^ (k - 1) := by rw [Nat.add_mul, one_mul]
      _ = p * p ^ (k - 1) := by rw [Nat.add_sub_of_le hp.one_lt.le]
      _ = p ^ k := by rw [← pow_succ', Nat.sub_add_cancel hk]
  omega
