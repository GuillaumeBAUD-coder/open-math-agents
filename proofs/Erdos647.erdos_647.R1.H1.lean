import OMAReductions.R_Erdos647_erdos_647_R1

open ArithmeticFunction

private lemma step_le_12 (a : ℕ) : (a + 3) ^ 6 ≤ 12 * (a + 2) ^ 6 := by
  zify
  have h : (12 : ℤ) * ((a : ℤ) + 2) ^ 6 = ((a : ℤ) + 3) ^ 6 +
      (11 * (a : ℤ) ^ 6 + 126 * (a : ℤ) ^ 5 + 585 * (a : ℤ) ^ 4 +
       1380 * (a : ℤ) ^ 3 + 1695 * (a : ℤ) ^ 2 + 1014 * (a : ℤ) + 39) := by ring
  linarith [show (0 : ℤ) ≤ 11 * (a : ℤ) ^ 6 + 126 * (a : ℤ) ^ 5 + 585 * (a : ℤ) ^ 4 +
    1380 * (a : ℤ) ^ 3 + 1695 * (a : ℤ) ^ 2 + 1014 * (a : ℤ) + 39 by positivity]

private lemma bound_ge_64 {p : ℕ} (hp : 64 ≤ p) (a : ℕ) :
    ((a + 1 : ℚ) ^ 6) / (p : ℚ) ^ a ≤ 1 := by
  have hp0 : (0 : ℚ) < p := by positivity
  rw [div_le_one (pow_pos hp0 a)]
  norm_cast
  induction a with
  | zero => simp
  | succ a ih =>
    rcases a with _ | a
    · simpa using hp
    · calc (a + 1 + 1 + 1) ^ 6 = (a + 3) ^ 6 := by ring_nf
        _ ≤ 12 * (a + 2) ^ 6 := step_le_12 a
        _ ≤ p * (a + 2) ^ 6 := Nat.mul_le_mul_right _ (by omega)
        _ ≤ p * p ^ (a + 1) := Nat.mul_le_mul_left _ ih
        _ = p ^ (a + 2) := by ring

private lemma bound_ge_13 {p : ℕ} (hp : 13 ≤ p) (a : ℕ) :
    ((a + 1 : ℚ) ^ 6) / (p : ℚ) ^ a ≤ 64 / (p : ℚ) := by
  have hp0 : (0 : ℚ) < p := by positivity
  rw [div_le_div_iff₀ (pow_pos hp0 a) hp0]
  norm_cast
  rcases a with _ | a
  · simp; omega
  · suffices h : (a + 2) ^ 6 * p ≤ 64 * p ^ (a + 1) by simpa [add_assoc] using h
    have hpow : (a + 2) ^ 6 ≤ 64 * p ^ a := by
      induction a with
      | zero => simp
      | succ a ih =>
        calc (a + 1 + 2) ^ 6 = (a + 3) ^ 6 := by ring_nf
          _ ≤ 12 * (a + 2) ^ 6 := step_le_12 a
          _ ≤ p * (a + 2) ^ 6 := Nat.mul_le_mul_right _ (by omega)
          _ ≤ p * (64 * p ^ a) := Nat.mul_le_mul_left _ ih
          _ = 64 * p ^ (a + 1) := by ring
    calc (a + 2) ^ 6 * p ≤ (64 * p ^ a) * p := Nat.mul_le_mul_right _ hpow
      _ = 64 * p ^ (a + 1) := by ring

private lemma bound_small_step {p a0 : ℕ} (hp : 0 < p)
    (hstep : ∀ a ≥ a0, (a + 2) ^ 6 ≤ p * (a + 1) ^ 6)
    (hinit : ∀ a ≤ a0, ((a + 1 : ℚ) ^ 6) / (p : ℚ) ^ a ≤ ((a0 + 1 : ℚ) ^ 6) / (p : ℚ) ^ a0)
    (a : ℕ) :
    ((a + 1 : ℚ) ^ 6) / (p : ℚ) ^ a ≤ ((a0 + 1 : ℚ) ^ 6) / (p : ℚ) ^ a0 := by
  rcases le_or_gt a a0 with ha | ha
  · exact hinit a ha
  · have hp0 : (0 : ℚ) < p := by exact_mod_cast hp
    rw [div_le_div_iff₀ (pow_pos hp0 a) (pow_pos hp0 a0)]
    norm_cast
    induction a, ha using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih =>
      have hk1 : (k + 2) ^ 6 * p ^ a0 ≤ p * ((k + 1) ^ 6 * p ^ a0) := by
        calc (k + 2) ^ 6 * p ^ a0 ≤ (p * (k + 1) ^ 6) * p ^ a0 :=
              Nat.mul_le_mul_right _ (hstep k (by omega))
          _ = p * ((k + 1) ^ 6 * p ^ a0) := by ring
      calc (k + 1 + 1) ^ 6 * p ^ a0 = (k + 2) ^ 6 * p ^ a0 := by ring_nf
        _ ≤ p * ((k + 1) ^ 6 * p ^ a0) := hk1
        _ ≤ p * ((a0 + 1) ^ 6 * p ^ k) := Nat.mul_le_mul_left _ ih
        _ = (a0 + 1) ^ 6 * p ^ (k + 1) := by ring

private def c (p : ℕ) : ℚ :=
  if p = 2 then 531441 / 256
  else if p = 3 then 15625 / 81
  else if p = 5 then 4096 / 125
  else if p = 7 then 729 / 49
  else if p = 11 then 729 / 121
  else if p < 64 then 64 / (p : ℚ)
  else 1

private lemma c_ge_one (p : ℕ) (hp : p.Prime) : 1 ≤ c p := by
  unfold c
  split_ifs with h2 h3 h5 h7 h11 h64
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [le_div_iff₀ (by exact_mod_cast hp.pos)]; norm_cast; omega
  · exact le_rfl

private lemma prime_bound (p : ℕ) (hp : p.Prime) (a : ℕ) :
    ((a + 1 : ℚ) ^ 6) / (p : ℚ) ^ a ≤ c p := by
  unfold c
  split_ifs with h2 h3 h5 h7 h11 h64
  · subst h2
    refine bound_small_step (a0 := 8) (by decide) (fun k hk => ?_) (fun k hk => ?_) a
    · zify
      have h : (2 : ℤ) * ((k : ℤ) + 1) ^ 6 = ((k : ℤ) + 2) ^ 6 +
          ((k : ℤ) ^ 6 - 6 * (k : ℤ) ^ 5 - 45 * (k : ℤ) ^ 4 - 120 * (k : ℤ) ^ 3 -
           165 * (k : ℤ) ^ 2 - 120 * (k : ℤ) - 62) := by ring
      have hk8 : (8 : ℤ) ≤ k := by exact_mod_cast hk
      nlinarith [sq_nonneg ((k : ℤ) - 8)]
    · interval_cases k <;> norm_num
  · subst h3
    refine bound_small_step (a0 := 4) (by decide) (fun k hk => ?_) (fun k hk => ?_) a
    · zify
      have hk4 : (4 : ℤ) ≤ k := by exact_mod_cast hk
      have h : (3 : ℤ) * ((k : ℤ) + 1) ^ 6 - ((k : ℤ) + 2) ^ 6 =
          2 * (k : ℤ) ^ 6 + 6 * (k : ℤ) ^ 5 - 15 * (k : ℤ) ^ 4 - 100 * (k : ℤ) ^ 3 -
          195 * (k : ℤ) ^ 2 - 174 * (k : ℤ) - 61 := by ring
      nlinarith [sq_nonneg ((k : ℤ) - 4)]
    · interval_cases k <;> norm_num
  · subst h5
    refine bound_small_step (a0 := 3) (by decide) (fun k hk => ?_) (fun k hk => ?_) a
    · zify
      have hk3 : (3 : ℤ) ≤ k := by exact_mod_cast hk
      have h : (5 : ℤ) * ((k : ℤ) + 1) ^ 6 - ((k : ℤ) + 2) ^ 6 =
          4 * (k : ℤ) ^ 6 + 18 * (k : ℤ) ^ 5 + 15 * (k : ℤ) ^ 4 - 60 * (k : ℤ) ^ 3 -
          165 * (k : ℤ) ^ 2 - 162 * (k : ℤ) - 59 := by ring
      nlinarith [sq_nonneg ((k : ℤ) - 3)]
    · interval_cases k <;> norm_num
  · subst h7
    refine bound_small_step (a0 := 2) (by decide) (fun k hk => ?_) (fun k hk => ?_) a
    · zify
      have hk2 : (2 : ℤ) ≤ k := by exact_mod_cast hk
      have h : (7 : ℤ) * ((k : ℤ) + 1) ^ 6 - ((k : ℤ) + 2) ^ 6 =
          6 * (k : ℤ) ^ 6 + 30 * (k : ℤ) ^ 5 + 45 * (k : ℤ) ^ 4 - 20 * (k : ℤ) ^ 3 -
          135 * (k : ℤ) ^ 2 - 150 * (k : ℤ) - 57 := by ring
      nlinarith [sq_nonneg ((k : ℤ) - 2)]
    · interval_cases k <;> norm_num
  · subst h11
    refine bound_small_step (a0 := 2) (by decide) (fun k hk => ?_) (fun k hk => ?_) a
    · zify
      have hk2 : (2 : ℤ) ≤ k := by exact_mod_cast hk
      have h : (11 : ℤ) * ((k : ℤ) + 1) ^ 6 - ((k : ℤ) + 2) ^ 6 =
          10 * (k : ℤ) ^ 6 + 54 * (k : ℤ) ^ 5 + 105 * (k : ℤ) ^ 4 + 60 * (k : ℤ) ^ 3 -
          75 * (k : ℤ) ^ 2 - 126 * (k : ℤ) - 53 := by ring
      nlinarith [sq_nonneg ((k : ℤ) - 2)]
    · interval_cases k <;> norm_num
  · have hp13 : 13 ≤ p := by
      have := hp.two_le
      omega
    exact bound_ge_13 hp13 a
  · exact bound_ge_64 (by omega) a

theorem OMA.solution : OMA.R_Erdos647_erdos_647_R1.H1 := by
  intro m
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · have hm_pos : (0 : ℚ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hsigma : σ 0 m = ∏ p ∈ m.primeFactors, (m.factorization p + 1) := by
      rw [isMultiplicative_sigma.multiplicative_factorization _ hm]
      refine Finset.prod_congr rfl fun p hp => ?_
      exact sigma_zero_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)
    have hfac : m = ∏ p ∈ m.primeFactors, p ^ m.factorization p := by
      conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hm]
      rfl
    have hdiv : ((σ 0 m : ℚ) ^ 6) / (m : ℚ) =
        ∏ p ∈ m.primeFactors, ((m.factorization p + 1 : ℚ) ^ 6) / (p : ℚ) ^ m.factorization p := by
      rw [hsigma]
      conv_lhs => rhs; rw [hfac]
      push_cast
      rw [Finset.prod_pow, ← Finset.prod_div_distrib]
    have hprod_le : ((σ 0 m : ℚ) ^ 6) / (m : ℚ) ≤ ∏ p ∈ m.primeFactors, c p := by
      rw [hdiv]
      refine Finset.prod_le_prod (fun p _ => by positivity) (fun p hp => ?_)
      exact prime_bound p (Nat.prime_of_mem_primeFactors hp) (m.factorization p)
    have hsub : ∏ p ∈ m.primeFactors, c p ≤
        ∏ p ∈ (Finset.range 64).filter Nat.Prime, c p := by
      let S := m.primeFactors ∪ (Finset.range 64).filter Nat.Prime
      have h1 : ∏ p ∈ m.primeFactors, c p ≤ ∏ p ∈ S, c p := by
        refine Finset.prod_le_prod_of_subset_of_one_le' Finset.subset_union_left fun p hpS _ => ?_
        rcases Finset.mem_union.mp hpS with hp | hp
        · exact c_ge_one p (Nat.prime_of_mem_primeFactors hp)
        · exact c_ge_one p (Finset.mem_filter.mp hp).2
      have h2 : ∏ p ∈ S, c p = ∏ p ∈ (Finset.range 64).filter Nat.Prime, c p := by
        refine (Finset.prod_subset Finset.subset_union_right fun p hpS hnot => ?_).symm
        have hp_prime : p.Prime := by
          rcases Finset.mem_union.mp hpS with hp | hp
          · exact Nat.prime_of_mem_primeFactors hp
          · exact False.elim (hnot hp)
        have hge : 64 ≤ p := by
          by_contra hlt
          exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp_prime⟩)
        unfold c
        split_ifs <;> omega
      exact h1.trans_eq h2
    have hnum : ∏ p ∈ (Finset.range 64).filter Nat.Prime, c p ≤ (139 : ℚ) ^ 6 := by
      norm_num [c, Finset.prod_filter, Finset.prod_range_succ]
    have hfinal : ((σ 0 m : ℚ) ^ 6) / (m : ℚ) ≤ (139 : ℚ) ^ 6 := hprod_le.trans (hsub.trans hnum)
    rw [div_le_iff₀ hm_pos] at hfinal
    exact_mod_cast hfinal
