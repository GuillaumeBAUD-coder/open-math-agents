import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R1

open AgohGiuga

private lemma sum_range_mul_eq {α : Type*} [AddCommMonoid α] (f : ℕ → α) (q p : ℕ) :
    ∑ i ∈ Finset.range (q * p), f i = ∑ k ∈ Finset.range q, ∑ r ∈ Finset.range p, f (k * p + r) := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

private lemma mod_p_props {n p : ℕ} (hn : IsStrongGiuga n) (hp : p.Prime) (hpn : p ∣ n) :
    (p - 1) ∣ (n - 1) ∧ p ∣ (n / p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn1 : 1 < n := hn.1.1
  have h0n : 1 ≤ n - 1 := by omega
  have hsum_dvd : p ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) := hpn.trans hn.2
  have hsum_zmod : (1 : ZMod p) + ∑ i ∈ Finset.Ioo 0 n, (i : ZMod p) ^ (n - 1) = 0 := by
    have := (ZMod.natCast_eq_zero_iff (1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1)) p).mpr hsum_dvd
    simpa [Nat.cast_add, Nat.cast_sum, Nat.cast_pow] using this
  have hrange : ∑ i ∈ Finset.Ioo 0 n, (i : ZMod p) ^ (n - 1) =
      ∑ i ∈ Finset.range n, (i : ZMod p) ^ (n - 1) := by
    have hsplit : Finset.range n = insert 0 (Finset.Ioo 0 n) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
      omega
    rw [hsplit, Finset.sum_insert (by simp)]
    simp [Nat.sub_ne_zero_of_lt hn1]
  have hblocks : ∑ i ∈ Finset.range n, (i : ZMod p) ^ (n - 1) =
      ((n / p : ℕ) : ZMod p) * ∑ r ∈ Finset.Ioo 0 p, (r : ZMod p) ^ (n - 1) := by
    obtain ⟨q, hq⟩ := hpn
    have hqp : n / p = q := by rw [hq, Nat.mul_div_cancel_left _ hp.pos]
    rw [hqp]
    have hmul : n = q * p := by rw [hq, mul_comm]
    rw [hmul, sum_range_mul_eq]
    have hinner : ∀ k : ℕ, ∑ r ∈ Finset.range p, ((k * p + r : ℕ) : ZMod p) ^ (n - 1) =
        ∑ r ∈ Finset.Ioo 0 p, (r : ZMod p) ^ (n - 1) := by
      intro k
      have hp0 : 0 < p := hp.pos
      have hsplit : Finset.range p = insert 0 (Finset.Ioo 0 p) := by
        ext x
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
        omega
      rw [hsplit, Finset.sum_insert (by simp)]
      have h0 : ((k * p + 0 : ℕ) : ZMod p) ^ (n - 1) = 0 := by
        simp [Nat.sub_ne_zero_of_lt hn1]
      rw [h0, zero_add]
      refine Finset.sum_congr rfl fun r _ => ?_
      push_cast
      simp
    simp_rw [hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hrange, hblocks] at hsum_zmod
  have hbij : ∑ r ∈ Finset.Ioo 0 p, (r : ZMod p) ^ (n - 1) =
      ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ (n - 1) := by
    refine Finset.sum_bij (fun r hr => Units.mk0 (r : ZMod p) (by
      rw [Finset.mem_Ioo] at hr
      intro h0
      rw [ZMod.natCast_eq_zero_iff] at h0
      exact absurd (Nat.le_of_dvd hr.1 h0) (not_le_of_gt hr.2)))
      (fun _ _ => Finset.mem_univ _)
      (fun r₁ hr₁ r₂ hr₂ heq => by
        rw [Finset.mem_Ioo] at hr₁ hr₂
        have hval := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p).val) heq
        simpa [ZMod.val_natCast_of_lt hr₁.2, ZMod.val_natCast_of_lt hr₂.2] using hval)
      (fun u _ => ⟨(u : ZMod p).val, Finset.mem_Ioo.mpr ⟨ZMod.val_pos.mpr u.ne_zero, ZMod.val_lt _⟩,
        Units.ext (ZMod.natCast_zmod_val _)⟩)
      (fun _ _ => rfl)
  have hdvd_exp : (p - 1) ∣ (n - 1) := by
    by_contra hndvd
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    have hord : orderOf g = p - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
    have hg_ne : g ^ (n - 1) ≠ 1 := by
      intro heq
      exact hndvd (hord ▸ orderOf_dvd_iff_pow_eq_one.mpr heq)
    have hgu_ne : (g : ZMod p) ^ (n - 1) ≠ 1 := by
      intro heq
      exact hg_ne (Units.ext (by simpa using heq))
    have hS : (g : ZMod p) ^ (n - 1) * ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ (n - 1) =
        ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ (n - 1) := by
      rw [Finset.mul_sum]
      calc ∑ u : (ZMod p)ˣ, (g : ZMod p) ^ (n - 1) * (u : ZMod p) ^ (n - 1)
          = ∑ u : (ZMod p)ˣ, (((g * u : (ZMod p)ˣ) : ZMod p) ^ (n - 1)) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [Units.val_mul, mul_pow]
        _ = ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ (n - 1) :=
            Equiv.sum_comp (Equiv.mulLeft g) (fun u : (ZMod p)ˣ => (u : ZMod p) ^ (n - 1))
    have hS0 : ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ (n - 1) = 0 := by
      have hmul0 : ((g : ZMod p) ^ (n - 1) - 1) * ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ (n - 1) = 0 := by
        rw [sub_mul, one_mul, hS, sub_self]
      exact (mul_eq_zero.mp hmul0).resolve_left (sub_ne_zero.mpr hgu_ne)
    rw [hbij, hS0, mul_zero, add_zero] at hsum_zmod
    exact one_ne_zero hsum_zmod
  refine ⟨hdvd_exp, ?_⟩
  have hS_eq : ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ (n - 1) = (-1 : ZMod p) := by
    have hterm : ∀ u : (ZMod p)ˣ, (u : ZMod p) ^ (n - 1) = 1 := by
      intro u
      obtain ⟨k, hk⟩ := hdvd_exp
      rw [hk, pow_mul, ← Units.val_pow_eq_pow_val]
      have : u ^ (p - 1) = 1 := by
        rw [← ZMod.card_units p]
        exact pow_card_eq_one
      simp [this]
    simp_rw [hterm, Finset.sum_const, Finset.card_univ, ZMod.card_units, nsmul_eq_mul, mul_one]
    rw [Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]
  rw [hbij, hS_eq, mul_neg_one] at hsum_zmod
  have hq1 : ((n / p : ℕ) : ZMod p) = 1 := by linear_combination -hsum_zmod
  have hq_pos : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp.pos
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq_pos, hq1, Nat.cast_one, sub_self]

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1.H1 := by
  intro n hn
  have hsq : Squarefree n := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp ⟨k, hk⟩
    have hpn : p ∣ n := ⟨p * k, by rw [hk]; ring⟩
    have hdvd : p ∣ (n / p - 1) := (mod_p_props hn hp hpn).2
    have hnp : n / p = p * k := by
      rw [hk, show p * p * k = p * (p * k) by ring, Nat.mul_div_cancel_left _ hp.pos]
    have hp_dvd_np : p ∣ n / p := ⟨k, hnp⟩
    have hn1 : 1 < n := hn.1.1
    have h1_pos : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp.pos
    have hp_dvd_1 : p ∣ 1 := by
      have := Nat.dvd_sub hp_dvd_np hdvd
      simpa [Nat.sub_sub_self h1_pos] using this
    exact hp.not_dvd_one hp_dvd_1
  exact (AgohGiuga.korselts_criterion n hn.1).mpr ⟨hsq, fun p hp hpn => (mod_p_props hn hp hpn).1⟩
