import FormalConjectures.ErdosProblems.«999»

open MeasureTheory Filter Set Finset in
theorem OMA.solution : type_of% @Erdos999.erdos_999.variants.easy_direction := by
  intro f hf hae hsum
  let A (q : ℕ) : Set ℝ :=
    {x | x ∈ Icc (0 : ℝ) 1 ∧ 0 < q ∧ ∃ p : ℤ, Int.gcd p q = 1 ∧ |x - (p : ℝ) / q| < f q / q}
  have hev : ∀ᶠ q : ℕ in atTop, f q / q < 1 / 2 := by
    filter_upwards [(tendsto_order.1 hsum.tendsto_atTop_zero).2 (1 / 2) (by norm_num),
      eventually_ge_atTop 1] with q hq hq1
    have h1 : (1 : ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq1
    have := le_mul_of_one_le_left (div_nonneg (hf q) (Nat.cast_nonneg q)) h1
    rw [← mul_div_assoc] at this; linarith
  obtain ⟨Q0, hQ0⟩ := eventually_atTop.1 hev
  let mass (q : ℕ) : ℝ := 6 * ((Nat.totient q : ℝ) * f q / q)
  have hmb (q : ℕ) (hq : Q0 ≤ q) : volume (A q) ≤ ENNReal.ofReal (mass q) := by
    by_cases hq0 : q = 0
    · subst hq0; rw [show A 0 = ∅ by ext x; simp [A], measure_empty]; exact zero_le
    have hqp : 0 < q := Nat.pos_of_ne_zero hq0
    have hqr : (0 : ℝ) < q := Nat.cast_pos.2 hqp
    have hfh : f q / q < 1 / 2 := hQ0 q hq
    let S := (Finset.Ico (-(q : ℤ)) (2 * (q : ℤ))).filter fun p : ℤ => Int.gcd p q = 1
    have hsub : A q ⊆ ⋃ p ∈ S, {x : ℝ | |x - (p : ℝ) / q| < f q / q} := by
      rintro x ⟨⟨hx0, hx1⟩, _, p, hgcd, hd⟩
      refine mem_biUnion (mem_filter.2 ⟨Finset.mem_Ico.2 ⟨?_, ?_⟩, hgcd⟩) hd
      · have h1 : -(q : ℝ) < p := by
          have := (lt_div_iff₀ hqr).1 (show -1 / 2 < (p : ℝ) / q by linarith [(abs_lt.1 hd).2]); linarith
        exact_mod_cast (show -(q : ℤ) < p by exact_mod_cast h1).le
      · have h1 : (p : ℝ) < 2 * q := by
          have := (div_lt_iff₀ hqr).1 (show (p : ℝ) / q < 3 / 2 by linarith [(abs_lt.1 hd).1]); linarith
        exact_mod_cast h1
    have hcard : S.card ≤ 3 * Nat.totient q := by
      let C := (range q).filter (Nat.Coprime q)
      have hinj : Set.InjOn (fun p : ℤ => (p / q, (p % q).toNat)) (S : Set ℤ) := by
        intro x _ y _ h; simp only [Prod.mk.injEq] at h
        have := Int.emod_nonneg x (by omega : (q : ℤ) ≠ 0)
        have := Int.emod_nonneg y (by omega : (q : ℤ) ≠ 0)
        rw [← Int.mul_ediv_add_emod x q, ← Int.mul_ediv_add_emod y q, h.1,
          show x % q = y % q by omega]
      have hmap : Set.MapsTo (fun p : ℤ => (p / q, (p % q).toNat)) (S : Set ℤ)
          (↑(({-1, 0, 1} : Finset ℤ) ×ˢ C) : Set (ℤ × ℕ)) := by
        intro p hp
        obtain ⟨hIco, hgcd⟩ := mem_filter.1 hp; obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.1 hIco
        have hm0 := Int.emod_nonneg p (by omega : (q : ℤ) ≠ 0)
        have hmlt := Int.emod_lt_of_pos p (by omega : (0 : ℤ) < q)
        have hdv := Int.mul_ediv_add_emod p q
        refine Finset.mem_coe.2 <| mem_product.2 ⟨by
            simp only [Finset.mem_insert, Finset.mem_singleton]
            have : -1 ≤ p / q ∧ p / q ≤ 1 := ⟨by nlinarith, by nlinarith⟩; omega,
          mem_filter.2 ⟨mem_range.2 (by dsimp; omega), ?_⟩⟩
        have h1 : Int.gcd (p % q) q = 1 := by
          rw [Int.gcd_comm, show p % q = p + -(p / q) * q by linarith,
            Int.gcd_add_mul_right_right, Int.gcd_comm]; exact hgcd
        rw [← Int.toNat_of_nonneg hm0, Int.gcd_natCast_natCast] at h1
        exact Nat.coprime_iff_gcd_eq_one.2 (by rw [Nat.gcd_comm]; exact h1)
      simpa [C, Nat.totient_eq_card_coprime] using card_le_card_of_injOn _ hmap hinj
    calc volume (A q) ≤ ∑ p ∈ S, volume {x : ℝ | |x - (p : ℝ) / q| < f q / q} :=
          (measure_mono hsub).trans (measure_biUnion_finset_le S _)
      _ ≤ ∑ _p ∈ S, ENNReal.ofReal (2 * (f q / q)) := Finset.sum_le_sum fun p _ =>
          (measure_mono (t := Set.Ioo ((p : ℝ) / q - f q / q) ((p : ℝ) / q + f q / q))
            fun x (hx : |x - (p : ℝ) / q| < f q / q) =>
            ⟨by linarith [(abs_lt.1 hx).1], by linarith [(abs_lt.1 hx).2]⟩).trans_eq
            (by rw [Real.volume_Ioo]; congr 1; ring)
      _ = ENNReal.ofReal ((S.card : ℝ) * (2 * (f q / q))) := by
          rw [sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      _ ≤ ENNReal.ofReal (mass q) := ENNReal.ofReal_le_ofReal <| by
          have hcardR : (S.card : ℝ) ≤ 3 * Nat.totient q := by exact_mod_cast hcard
          exact (mul_le_mul_of_nonneg_right hcardR
            (show 0 ≤ 2 * (f q / q) by have := hf q; positivity)).trans_eq (by dsimp [mass]; ring)
  have hts : (∑' q, volume (A q)) ≠ ⊤ := by
    have htail : (∑' q, ENNReal.ofReal (mass q)) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun q => by have := hf q; positivity) (hsum.mul_left 6)]
      exact ENNReal.ofReal_ne_top
    have hfin : (∑' q, if q < Q0 then (1 : ENNReal) else 0) ≠ ⊤ := by
      rw [tsum_eq_sum (s := range Q0) fun q hq => if_neg (by simp at hq; omega)]
      exact (ENNReal.sum_lt_top.2 fun _ _ => by split_ifs <;> simp).ne
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨htail, hfin⟩) ?_
    rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun q => ?_
    by_cases hq : q < Q0
    · rw [if_pos hq]
      exact ((measure_mono fun _ hx => hx.1).trans_eq (by simp [Real.volume_Icc])).trans le_add_self
    · rw [if_neg hq, add_zero]; exact hmb q (not_lt.1 hq)
  have hvol : volume (Icc (0 : ℝ) 1) ≤ volume (limsup A atTop) := measure_mono_ae <| by
    filter_upwards [hae] with x hx hIcc
    change x ∈ limsup A atTop
    rw [limsup_eq_iInf_iSup_of_nat]
    simp only [Set.iInf_eq_iInter, Set.iSup_eq_iUnion, Set.mem_iInter, Set.mem_iUnion]
    intro N; obtain ⟨q, hqm, hqN⟩ := hx.exists_gt N
    exact ⟨q, hqN.le, hIcc, hqm.1, hqm.2⟩
  rw [measure_limsup_atTop_eq_zero hts, Real.volume_Icc, sub_zero, ENNReal.ofReal_one] at hvol
  exact one_ne_zero (le_antisymm hvol zero_le)
