import OMAStatements.S_oeis_a382837

namespace OMA.S_oeis_a382837

private lemma alternatingSum_nonneg : ∀ {l : List ℕ}, l.Pairwise (· ≥ ·) → 0 ≤ alternatingSum l
  | [], _ => by simp [alternatingSum]
  | [_], _ => by simp [alternatingSum]
  | a :: b :: rest, h => by
    simp only [alternatingSum]
    have hab : b ≤ a := List.rel_of_pairwise_cons h (List.mem_cons_self ..)
    have hrest : rest.Pairwise (· ≥ ·) := (List.pairwise_cons.mp (List.pairwise_cons.mp h).2).2
    have ih := alternatingSum_nonneg hrest
    omega

private lemma six_mul_sub_chi_ge {m : ℕ} (hm4 : 4 ≤ m) (h2 : 2 ∣ m) :
    (m : ℤ) ≤ 6 * ((m : ℤ) - chi m) := by
  have hm0 : m ≠ 0 := by omega
  have hm_pos : 0 < m := by omega
  have h2m : 2 * (m / 2) = m := Nat.mul_div_cancel' h2
  have hm_mem : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_refl m, hm0⟩
  set s₁ := m.divisors.erase m
  have hs₁_eq : m.divisors = insert m s₁ := (Finset.insert_erase hm_mem).symm
  have hsort₁ : m.divisors.sort (· ≥ ·) = m :: s₁.sort (· ≥ ·) := by
    rw [hs₁_eq]
    refine Finset.sort_insert (· ≥ ·) (fun d hd => ?_) (Finset.notMem_erase m m.divisors)
    exact Nat.le_of_dvd hm_pos (Nat.dvd_of_mem_divisors (Finset.mem_of_mem_erase hd))
  have hm2_dvd : m / 2 ∣ m := ⟨2, by omega⟩
  have hm2_mem : m / 2 ∈ s₁ := by
    refine Finset.mem_erase.mpr ⟨by omega, Nat.mem_divisors.mpr ⟨hm2_dvd, hm0⟩⟩
  set s₂ := s₁.erase (m / 2)
  have hs₂_eq : s₁ = insert (m / 2) s₂ := (Finset.insert_erase hm2_mem).symm
  have hsort₂ : s₁.sort (· ≥ ·) = (m / 2) :: s₂.sort (· ≥ ·) := by
    rw [hs₂_eq]
    refine Finset.sort_insert (· ≥ ·) (fun d hd => ?_) (Finset.notMem_erase (m / 2) s₁)
    have hd1 : d ∈ s₁ := Finset.mem_of_mem_erase hd
    have hd_ne : d ≠ m := (Finset.mem_erase.mp hd1).1
    have hd_dvd : d ∣ m := Nat.dvd_of_mem_divisors (Finset.mem_of_mem_erase hd1)
    rcases hd_dvd with ⟨q, hq⟩
    have hq2 : 2 ≤ q := by
      by_contra hqlt
      have hq01 : q = 0 ∨ q = 1 := by omega
      rcases hq01 with rfl | rfl
      · simp at hq; omega
      · simp at hq; exact hd_ne hq.symm
    have h2d : 2 * d ≤ m := by
      calc 2 * d = d * 2 := by ring
        _ ≤ d * q := Nat.mul_le_mul_left d hq2
        _ = m := hq.symm
    omega
  have hchi : (m : ℤ) - chi m = ((m / 2 : ℕ) : ℤ) - alternatingSum (s₂.sort (· ≥ ·)) := by
    unfold chi
    rw [hsort₁, hsort₂]
    simp only [alternatingSum]
    ring
  rw [hchi]
  cases hlist : s₂.sort (· ≥ ·) with
  | nil =>
    simp only [alternatingSum]
    omega
  | cons d rest =>
    have hd_mem : d ∈ s₂ := (Finset.mem_sort (· ≥ ·)).mp (by rw [hlist]; exact List.mem_cons_self ..)
    have hd_ne2 : d ≠ m / 2 := (Finset.mem_erase.mp hd_mem).1
    have hd1 : d ∈ s₁ := Finset.mem_of_mem_erase hd_mem
    have hd_ne1 : d ≠ m := (Finset.mem_erase.mp hd1).1
    have hd_dvd : d ∣ m := Nat.dvd_of_mem_divisors (Finset.mem_of_mem_erase hd1)
    rcases hd_dvd with ⟨q, hq⟩
    have hq3 : 3 ≤ q := by
      by_contra hqlt
      have hq012 : q = 0 ∨ q = 1 ∨ q = 2 := by omega
      rcases hq012 with rfl | rfl | rfl
      · simp at hq; omega
      · simp at hq; exact hd_ne1 hq.symm
      · apply hd_ne2; omega
    have h3d : 3 * d ≤ m := by
      calc 3 * d = d * 3 := by ring
        _ ≤ d * q := Nat.mul_le_mul_left d hq3
        _ = m := hq.symm
    have hpw : (d :: rest).Pairwise (· ≥ ·) := by
      rw [← hlist]
      exact Finset.pairwise_sort s₂ (· ≥ ·)
    have hrest_nonneg : 0 ≤ alternatingSum rest :=
      alternatingSum_nonneg (List.pairwise_cons.mp hpw).2
    simp only [alternatingSum]
    omega

private lemma totient_mul_prime_le (a p : ℕ) (hp : p.Prime) :
    (a * p).totient ≤ a.totient * p := by
  rw [mul_comm a p]
  by_cases h : p ∣ a
  · rw [Nat.totient_mul_of_prime_of_dvd hp h, mul_comm]
  · rw [Nat.totient_mul_of_prime_of_not_dvd hp h, mul_comm]
    exact Nat.mul_le_mul_left a.totient (Nat.sub_le p 1)

private lemma totient_mul_le_totient_mul (a : ℕ) : ∀ b : ℕ, (a * b).totient ≤ a.totient * b := by
  intro b
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    rcases eq_or_ne b 0 with rfl | hb0
    · simp
    rcases eq_or_ne b 1 with rfl | hb1
    · simp
    set p := b.minFac
    have hp : p.Prime := Nat.minFac_prime hb1
    have hpdvd : p ∣ b := Nat.minFac_dvd b
    have hbp : b = p * (b / p) := (Nat.mul_div_cancel' hpdvd).symm
    have hlt : b / p < b := Nat.div_lt_self (Nat.pos_of_ne_zero hb0) hp.one_lt
    have hmul : a * b = (a * p) * (b / p) := by
      conv_lhs => rw [hbp]
      rw [mul_assoc]
    calc (a * b).totient
      _ = ((a * p) * (b / p)).totient := by rw [hmul]
      _ ≤ (a * p).totient * (b / p) := ih (b / p) hlt (a * p)
      _ ≤ (a.totient * p) * (b / p) := Nat.mul_le_mul_right (b / p) (totient_mul_prime_le a p hp)
      _ = a.totient * b := by rw [mul_assoc, Nat.mul_div_cancel' hpdvd]

private lemma totient_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, p).totient = ∏ p ∈ S, (p - 1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hprime_p : p.Prime := hS p (Finset.mem_insert_self p s)
    have hprime_s : ∀ q ∈ s, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      exact (Nat.coprime_primes hprime_p (hprime_s q hq)).mpr (fun h => hp (h ▸ hq))
    rw [Finset.prod_insert hp, Finset.prod_insert hp, Nat.totient_mul hcop,
      Nat.totient_prime hprime_p, ih hprime_s]

private lemma exists_large_sum_primes (k : ℕ) :
    ∀ m : ℕ, ∃ K : ℕ, k ≤ K ∧ (m : ℝ) / 2 ≤ ∑ p ∈ K.primesBelow \ k.primesBelow, (1 / p : ℝ)
  | 0 => ⟨k, le_refl k, by simp⟩
  | m + 1 => by
    obtain ⟨K₁, hkK₁, hsum₁⟩ := exists_large_sum_primes k m
    set K₂ := (4 ^ (K₁.primesBelow.card + 1)).succ
    have hstep : (1 / 2 : ℝ) ≤ ∑ p ∈ K₂.primesBelow \ K₁.primesBelow, (1 / p : ℝ) :=
      one_half_le_sum_primes_ge_one_div K₁
    have hK₁K₂ : K₁ ≤ K₂ := by
      by_contra h
      push_neg at h
      have hsub : K₂.primesBelow ⊆ K₁.primesBelow := Nat.primesBelow_mono h.le
      rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.sum_empty] at hstep
      norm_num at hstep
    have hsub₁ : k.primesBelow ⊆ K₁.primesBelow := Nat.primesBelow_mono hkK₁
    have hsub₂ : K₁.primesBelow ⊆ K₂.primesBelow := Nat.primesBelow_mono hK₁K₂
    have hunion :
        (K₁.primesBelow \ k.primesBelow) ∪ (K₂.primesBelow \ K₁.primesBelow) =
          K₂.primesBelow \ k.primesBelow := by
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (⟨hx1, hxk⟩ | ⟨hx2, hx1⟩)
        · exact ⟨hsub₂ hx1, hxk⟩
        · exact ⟨hx2, fun hxk => hx1 (hsub₁ hxk)⟩
      · rintro ⟨hx2, hxk⟩
        by_cases hx1 : x ∈ K₁.primesBelow
        · exact Or.inl ⟨hx1, hxk⟩
        · exact Or.inr ⟨hx2, hx1⟩
    have hdisj : Disjoint (K₁.primesBelow \ k.primesBelow) (K₂.primesBelow \ K₁.primesBelow) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp hx2).2 (Finset.mem_sdiff.mp hx1).1
    refine ⟨K₂, hkK₁.trans hK₁K₂, ?_⟩
    rw [← hunion, Finset.sum_union hdisj]
    push_cast
    linarith

private lemma exists_coprime_small_totient (M : ℕ) (hM : 0 < M) :
    ∃ A : ℕ, 0 < A ∧ Nat.Coprime A M ∧ 3 * A.totient < A := by
  obtain ⟨K, _, hsum⟩ := exists_large_sum_primes (M + 1) 5
  set S := K.primesBelow \ (M + 1).primesBelow
  have hS_prime : ∀ p ∈ S, p.Prime := fun p hp =>
    Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
  have hS_gt : ∀ p ∈ S, M < p := by
    intro p hp
    have hp_prime := hS_prime p hp
    have hnot : p ∉ (M + 1).primesBelow := (Finset.mem_sdiff.mp hp).2
    by_contra hle
    exact hnot (Nat.mem_primesBelow.mpr ⟨by omega, hp_prime⟩)
  set A := ∏ p ∈ S, p
  have hA_pos : 0 < A := Finset.prod_pos fun p hp => (hS_prime p hp).pos
  have hA_cop : Nat.Coprime A M := by
    refine Nat.Coprime.prod_left fun p hp => ?_
    refine (hS_prime p hp).coprime_iff_not_dvd.mpr fun hdvd => ?_
    exact (hS_gt p hp).not_ge (Nat.le_of_dvd hM hdvd)
  have hA_tot : A.totient = ∏ p ∈ S, (p - 1) := totient_prod_primes S hS_prime
  have hprod_le : ∏ p ∈ S, (1 - 1 / (p : ℝ)) ≤ Real.exp (- ∑ p ∈ S, (1 / (p : ℝ))) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p _ => ?_)
    · have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS_prime p hp).one_lt.le
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (hS_prime p hp).pos
      have hdiv : (1 / (p : ℝ)) ≤ 1 := by
        rw [div_le_one hp_pos]
        exact hp1
      linarith
    · linarith [Real.add_one_le_exp (-(1 / (p : ℝ)))]
  have hexp_gt : (3 : ℝ) < Real.exp (∑ p ∈ S, (1 / (p : ℝ))) := by
    have h1 : (∑ p ∈ S, (1 / (p : ℝ))) + 1 ≤ Real.exp (∑ p ∈ S, (1 / (p : ℝ))) :=
      Real.add_one_le_exp _
    have h5 : ((5 : ℕ) : ℝ) = 5 := by norm_num
    rw [h5] at hsum
    linarith
  have hprod_lt : ∏ p ∈ S, (1 - 1 / (p : ℝ)) < 1 / 3 := by
    calc ∏ p ∈ S, (1 - 1 / (p : ℝ))
      _ ≤ Real.exp (- ∑ p ∈ S, (1 / (p : ℝ))) := hprod_le
      _ = (Real.exp (∑ p ∈ S, (1 / (p : ℝ))))⁻¹ := Real.exp_neg _
      _ < (3 : ℝ)⁻¹ := inv_strictAnti₀ (by norm_num : (0 : ℝ) < 3) hexp_gt
      _ = 1 / 3 := by ring
  have hratio : (A.totient : ℝ) / (A : ℝ) = ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
    rw [hA_tot, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (hS_prime p hp).pos
    have hp1 : 1 ≤ p := (hS_prime p hp).one_lt.le
    rw [Nat.cast_sub hp1, Nat.cast_one, sub_div, div_self hp_pos.ne']
  have hA_real_pos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA_pos
  have hlt_real : 3 * (A.totient : ℝ) < (A : ℝ) := by
    rw [← hratio, div_lt_div_iff₀ hA_real_pos (by norm_num : (0 : ℝ) < 3)] at hprod_lt
    linarith
  have hlt : 3 * A.totient < A := by exact_mod_cast hlt_real
  exact ⟨A, hA_pos, hA_cop, hlt⟩

private lemma isTerm_of_dvd {C m : ℕ} (hC_cop : Nat.Coprime C 2) (hC_tot : 3 * C.totient < C)
    (hdvd : 2 * C ∣ m) (hm4 : 4 ≤ m) : IsTerm m := by
  have hm_pos : 0 < m := by omega
  have h2m : 2 ∣ m := dvd_trans (dvd_mul_right 2 C) hdvd
  have hchi := six_mul_sub_chi_ge hm4 h2m
  rcases hdvd with ⟨r, hr⟩
  have hr_pos : 0 < r := by
    rcases eq_or_ne r 0 with rfl | hr0
    · simp at hr; omega
    · exact Nat.pos_of_ne_zero hr0
  have htot2C : (2 * C).totient = C.totient := by
    rw [Nat.totient_mul hC_cop.symm, Nat.totient_two, one_mul]
  have htotm : m.totient ≤ C.totient * r := by
    rw [hr]
    calc (2 * C * r).totient
      _ ≤ (2 * C).totient * r := totient_mul_le_totient_mul (2 * C) r
      _ = C.totient * r := by rw [htot2C]
  have h6tot : 6 * m.totient < m := by
    calc 6 * m.totient
      _ ≤ 6 * (C.totient * r) := Nat.mul_le_mul_left 6 htotm
      _ = 2 * (3 * C.totient) * r := by ring
      _ < 2 * C * r := by
        have h2lt : 2 * (3 * C.totient) < 2 * C := by omega
        exact Nat.mul_lt_mul_of_pos_right h2lt hr_pos
      _ = m := hr.symm
  have h6tot_z : 6 * (m.totient : ℤ) < (m : ℤ) := by exact_mod_cast h6tot
  refine ⟨hm_pos, ?_⟩
  omega

end OMA.S_oeis_a382837

theorem OMA.solution : type_of% @OMA.S_oeis_a382837.main := by
  intro n hn
  obtain ⟨A, hA_pos, hA_cop2, hA_tot⟩ := OMA.S_oeis_a382837.exists_coprime_small_totient 2 (by norm_num)
  obtain ⟨B, hB_pos, hB_cop2A, hB_tot⟩ := OMA.S_oeis_a382837.exists_coprime_small_totient (2 * A) (by omega)
  have hB_cop2 : Nat.Coprime B 2 := (Nat.coprime_mul_iff_right.mp hB_cop2A).1
  have hcop : Nat.Coprime (2 * A) B := hB_cop2A.symm
  let cr := Nat.chineseRemainder hcop 0 (B - n % B)
  have h2A_dvd : 2 * A ∣ cr.val := by
    have hmod : cr.val % (2 * A) = 0 := by
      have h := cr.property.1
      simpa [Nat.ModEq] using h
    exact Nat.dvd_of_mod_eq_zero hmod
  have hB_dvd : B ∣ cr.val + n := by
    have hmod : cr.val ≡ B - n % B [MOD B] := cr.property.2
    have hadd : cr.val + n ≡ (B - n % B) + n % B [MOD B] :=
      hmod.add (Nat.mod_modEq n B).symm
    have hle : n % B ≤ B := (Nat.mod_lt n hB_pos).le
    rw [Nat.sub_add_cancel hle] at hadd
    have hzero : cr.val + n ≡ 0 [MOD B] := hadd.trans (by simp [Nat.ModEq])
    exact Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using hzero)
  have hA4 : 4 ≤ A := by
    have htot_pos : 0 < A.totient := Nat.totient_pos.mpr hA_pos
    omega
  have hB4 : 4 ≤ B := by
    have htot_pos : 0 < B.totient := Nat.totient_pos.mpr hB_pos
    omega
  let f : ℕ → ℕ := fun t => cr.val + (t + 1) * (2 * A * B)
  have hf_inj : Function.Injective f := by
    intro t₁ t₂ h
    have hpos : 0 < 2 * A * B := Nat.mul_pos (Nat.mul_pos (by decide) hA_pos) hB_pos
    have heq : (t₁ + 1) * (2 * A * B) = (t₂ + 1) * (2 * A * B) := by
      dsimp only [f] at h
      omega
    have := Nat.eq_of_mul_eq_mul_right hpos heq
    omega
  refine (Set.infinite_range_of_injective hf_inj).mono ?_
  rintro _ ⟨t, rfl⟩
  have hft4 : 4 ≤ f t := by
    have h1 : 2 * A * B ≤ (t + 1) * (2 * A * B) := Nat.le_mul_of_pos_left _ (Nat.succ_pos t)
    have h2 : 4 ≤ 2 * A * B := by
      calc 4 ≤ 2 * 4 * 4 := by decide
        _ ≤ 2 * A * B := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hA4) hB4
    dsimp only [f]
    omega
  have h2A_ft : 2 * A ∣ f t := by
    refine dvd_add h2A_dvd ?_
    exact ⟨(t + 1) * B, by ring⟩
  have h2_ftn : 2 ∣ f t + n :=
    dvd_add (dvd_trans (dvd_mul_right 2 A) h2A_ft) hn.two_dvd
  have hB_ftn : B ∣ f t + n := by
    have heq : f t + n = (cr.val + n) + (t + 1) * (2 * A * B) := by dsimp only [f]; ring
    rw [heq]
    refine dvd_add hB_dvd ?_
    exact ⟨(t + 1) * (2 * A), by ring⟩
  have h2B_ftn : 2 * B ∣ f t + n := hB_cop2.symm.mul_dvd_of_dvd_of_dvd h2_ftn hB_ftn
  exact ⟨OMA.S_oeis_a382837.isTerm_of_dvd hA_cop2 hA_tot h2A_ft hft4,
    OMA.S_oeis_a382837.isTerm_of_dvd hB_cop2 hB_tot h2B_ftn (by omega)⟩
