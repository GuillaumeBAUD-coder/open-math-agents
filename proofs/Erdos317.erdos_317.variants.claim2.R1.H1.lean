import OMAReductions.R_Erdos317_erdos_317_variants_claim2_R1

-- Step Erdos317.erdos_317.variants.claim2.R1.H1: hypothesis H1 of reduction Erdos317.erdos_317.variants.claim2.R1
-- Credit: @volskew90
-- Take u the least prime power above n; every k in (n, u) is not a prime power, so it splits
-- into two coprime factors below k and divides lcm(1, ..., k - 1): the lcm never grows.

open Finset

private lemma dvd_lcm_pred {k : ℕ} (hk : 2 ≤ k) (hnp : ¬ IsPrimePow k) :
    k ∣ (Icc 1 (k - 1)).lcm id := by
  have hk0 : k ≠ 0 := by omega
  have hp : (Nat.minFac k).Prime := Nat.minFac_prime (by omega)
  set p := Nat.minFac k
  have hab := Nat.ordProj_mul_ordCompl_eq_self k p
  have hcop : Nat.Coprime (ordProj[p] k) (ordCompl[p] k) := (Nat.coprime_ordCompl hp hk0).pow_left _
  have he : 0 < k.factorization p := hp.factorization_pos_of_dvd hk0 (Nat.minFac_dvd k)
  have ha1 : 1 < ordProj[p] k := Nat.one_lt_pow he.ne' hp.one_lt
  have hb0 : ordCompl[p] k ≠ 0 := right_ne_zero_of_mul (hab ▸ hk0)
  have hb1 : 1 < ordCompl[p] k :=
    Nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨hb0, fun hb =>
      hnp ⟨p, k.factorization p, hp.prime, he, by rw [hb, mul_one] at hab; exact hab⟩⟩
  have halt : ordProj[p] k < k := by
    have := lt_mul_of_one_lt_right (zero_lt_one.trans ha1) hb1
    rwa [hab] at this
  have hblt : ordCompl[p] k < k := by
    have := lt_mul_of_one_lt_left (zero_lt_one.trans hb1) ha1
    rwa [hab] at this
  have hda := dvd_lcm (s := Icc 1 (k - 1)) (f := id) (mem_Icc.2 ⟨ha1.le, Nat.le_sub_one_of_lt halt⟩)
  have hdb := dvd_lcm (s := Icc 1 (k - 1)) (f := id) (mem_Icc.2 ⟨hb1.le, Nat.le_sub_one_of_lt hblt⟩)
  have := hcop.mul_dvd_of_dvd_of_dvd hda hdb
  rwa [hab] at this

theorem OMA.solution : OMA.R_Erdos317_erdos_317_variants_claim2_R1.H1 := by
  intro n hn
  have hex : ∃ u, n < u ∧ IsPrimePow u :=
    ⟨2 ^ (n + 1), Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)),
      2, n + 1, Nat.prime_two.prime, by omega, rfl⟩
  have hu := Nat.find_spec hex
  refine ⟨Nat.find hex, hu.1, hu.2, ?_⟩
  have step : ∀ m, n ≤ m → m < Nat.find hex → (Icc 1 m).lcm id = (Icc 1 n).lcm id := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => intro _; rfl
    | succ m hm ih =>
      intro hmu
      have hnp : ¬ IsPrimePow (m + 1) := fun h => Nat.find_min hex hmu ⟨by omega, h⟩
      have hdvd := dvd_lcm_pred (by omega) hnp
      rw [Nat.add_sub_cancel] at hdvd
      have hins : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by ext x; simp; omega
      rw [hins, lcm_insert, ← ih (by omega)]
      exact Nat.dvd_antisymm (lcm_dvd hdvd dvd_rfl) (dvd_lcm_right _ _)
  exact (step (Nat.find hex - 1) (by omega) (by omega)).symm
