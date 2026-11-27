import OMAReductions.R_Erdos647_erdos_647_R1
import Mathlib.NumberTheory.ArithmeticFunction.Misc

-- Step Erdos647.erdos_647.R1.H1
-- Credit: @caa1982

namespace Erdos647H1

open ArithmeticFunction.sigma

private def smallPrimes : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61}

private def primeBound (p : ℕ) : ℚ :=
  if p = 2 then 531441 / 256
  else if p = 3 then 15625 / 81
  else if p = 5 then 4096 / 125
  else if p = 7 then 729 / 49
  else if p = 11 then 729 / 121
  else if p < 64 then 64 / (p : ℚ)
  else 1

private lemma one_le_primeBound {p : ℕ} (hp : p.Prime) : 1 ≤ primeBound p := by
  unfold primeBound
  have hp2 : 2 ≤ p := hp.two_le
  split_ifs with h2 h3 h5 h7 h11 h64
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [one_le_div (by positivity)]
    exact_mod_cast le_of_lt h64
  · exact le_rfl

private lemma primeBound_eq_one_of_notMem {p : ℕ} (hp : p.Prime) (hnot : p ∉ smallPrimes) :
    primeBound p = 1 := by
  have hge64 : 64 ≤ p := by
    by_contra hlt
    push Not at hlt
    have hmem : p ∈ smallPrimes := by
      interval_cases p <;> first | exact absurd hp (by decide) | decide
    exact hnot hmem
  unfold primeBound
  split_ifs <;> first | rfl | omega

private lemma step_ge (p e₀ : ℕ)
    (hstep : ∀ e ≥ e₀, (e + 2) ^ 6 ≤ p * (e + 1) ^ 6) (hp : 0 < p) :
    ∀ e ≥ e₀, ((e + 1 : ℚ) ^ 6) / (p : ℚ) ^ e ≤ ((e₀ + 1 : ℚ) ^ 6) / (p : ℚ) ^ e₀ := by
  intro e he
  induction e, he using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    refine le_trans ?_ ih
    have hmul : ((k + 2 : ℚ) ^ 6) ≤ (p : ℚ) * ((k + 1 : ℚ) ^ 6) := by
      exact_mod_cast hstep k hk
    have hpq : (0 : ℚ) < (p : ℚ) := by positivity
    have hpk : (0 : ℚ) < (p : ℚ) ^ k := by positivity
    rw [pow_succ (p : ℚ) k, div_le_div_iff₀ (mul_pos hpk hpq) hpk]
    have hcast : ((k + 1 : ℕ) : ℚ) + 1 = (k : ℚ) + 2 := by push_cast; ring
    rw [hcast]
    nlinarith

private lemma prime_pow_bound {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ((e + 1 : ℚ) ^ 6) / (p : ℚ) ^ e ≤ primeBound p := by
  have hp_pos : 0 < p := hp.pos
  by_cases h2 : p = 2
  · subst h2
    have hstep : ∀ k ≥ 8, (k + 2) ^ 6 ≤ 2 * (k + 1) ^ 6 := by
      intro k hk
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
      have : (8 + t + 2) ^ 6 ≤ 2 * (8 + t + 1) ^ 6 := by
        zify
        nlinarith [sq_nonneg t, sq_nonneg (t ^ 2), sq_nonneg (t ^ 3)]
      exact this
    by_cases he : 8 ≤ e
    · simpa [primeBound] using (step_ge 2 8 hstep (by decide) e he).trans (by norm_num)
    · interval_cases e <;> norm_num [primeBound]
  · by_cases h3 : p = 3
    · subst h3
      have hstep : ∀ k ≥ 4, (k + 2) ^ 6 ≤ 3 * (k + 1) ^ 6 := by
        intro k hk
        obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
        zify; nlinarith [sq_nonneg t, sq_nonneg (t ^ 2), sq_nonneg (t ^ 3)]
      by_cases he : 4 ≤ e
      · simpa [primeBound] using (step_ge 3 4 hstep (by decide) e he).trans (by norm_num)
      · interval_cases e <;> norm_num [primeBound]
    · by_cases h5 : p = 5
      · subst h5
        have hstep : ∀ k ≥ 3, (k + 2) ^ 6 ≤ 5 * (k + 1) ^ 6 := by
          intro k hk
          obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
          zify; nlinarith [sq_nonneg t, sq_nonneg (t ^ 2), sq_nonneg (t ^ 3)]
        by_cases he : 3 ≤ e
        · simpa [primeBound] using (step_ge 5 3 hstep (by decide) e he).trans (by norm_num)
        · interval_cases e <;> norm_num [primeBound]
      · by_cases h7 : p = 7
        · subst h7
          have hstep : ∀ k ≥ 2, (k + 2) ^ 6 ≤ 7 * (k + 1) ^ 6 := by
            intro k hk
            obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
            zify; nlinarith [sq_nonneg t, sq_nonneg (t ^ 2), sq_nonneg (t ^ 3)]
          by_cases he : 2 ≤ e
          · simpa [primeBound] using (step_ge 7 2 hstep (by decide) e he).trans (by norm_num)
          · interval_cases e <;> norm_num [primeBound]
        · by_cases h11 : p = 11
          · subst h11
            have hstep : ∀ k ≥ 2, (k + 2) ^ 6 ≤ 11 * (k + 1) ^ 6 := by
              intro k hk
              obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
              zify; nlinarith [sq_nonneg t, sq_nonneg (t ^ 2), sq_nonneg (t ^ 3)]
            by_cases he : 2 ≤ e
            · simpa [primeBound] using (step_ge 11 2 hstep (by decide) e he).trans (by norm_num)
            · interval_cases e <;> norm_num [primeBound]
          · by_cases h64 : p < 64
            · have hp13 : 13 ≤ p := by
                have := hp.two_le
                by_contra hlt; push Not at hlt
                interval_cases p <;> first | exact absurd hp (by decide) | omega
              have hstep : ∀ k ≥ 1, (k + 2) ^ 6 ≤ p * (k + 1) ^ 6 := by
                intro k hk
                obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
                have h13 : (1 + t + 2) ^ 6 ≤ 13 * (1 + t + 1) ^ 6 := by
                  zify; nlinarith [sq_nonneg t, sq_nonneg (t ^ 2), sq_nonneg (t ^ 3)]
                exact h13.trans (Nat.mul_le_mul_right _ hp13)
              have hpb : primeBound p = 64 / (p : ℚ) := by
                unfold primeBound
                simp [h2, h3, h5, h7, h11, h64]
              rw [hpb]
              rcases Nat.eq_zero_or_pos e with rfl | he
              · simp only [Nat.cast_zero, zero_add, one_pow, pow_zero, div_one]
                rw [one_le_div (by positivity)]
                exact_mod_cast le_of_lt h64
              · have := step_ge p 1 hstep hp_pos e he
                norm_num at this
                exact this
            · have hp64 : 64 ≤ p := by omega
              have hstep : ∀ k ≥ 0, (k + 2) ^ 6 ≤ p * (k + 1) ^ 6 := by
                intro k _
                have h64' : (k + 2) ^ 6 ≤ 64 * (k + 1) ^ 6 := by
                  zify; nlinarith [sq_nonneg k, sq_nonneg (k ^ 2), sq_nonneg (k ^ 3)]
                exact h64'.trans (Nat.mul_le_mul_right _ hp64)
              have hpb : primeBound p = 1 := by
                unfold primeBound
                simp [h2, h3, h5, h7, h11, h64]
              rw [hpb]
              simpa using step_ge p 0 hstep hp_pos e (Nat.zero_le e)

private lemma prod_smallPrimes_le :
    (∏ p ∈ smallPrimes, primeBound p) ≤ (139 : ℚ) ^ 6 := by
  norm_num [smallPrimes, primeBound]

private lemma sigma_zero_eq_prod {m : ℕ} (hm : m ≠ 0) :
    σ 0 m = ∏ p ∈ m.primeFactors, (m.factorization p + 1) := by
  rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hm]

end Erdos647H1

theorem OMA.solution : OMA.R_Erdos647_erdos_647_R1.H1 := by
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hm_ne : m ≠ 0 := hm.ne'
    have hq : ((ArithmeticFunction.sigma 0 m : ℚ) ^ 6) / (m : ℚ) ≤ (139 : ℚ) ^ 6 := by
      have hsig := Erdos647H1.sigma_zero_eq_prod hm_ne
      have hfac : m = ∏ p ∈ m.primeFactors, p ^ m.factorization p :=
        (Nat.prod_factorization_pow_eq_self hm_ne).symm
      have hdiv : ((ArithmeticFunction.sigma 0 m : ℚ) ^ 6) / (m : ℚ) =
          ∏ p ∈ m.primeFactors, ((m.factorization p + 1 : ℚ) ^ 6) / (p : ℚ) ^ m.factorization p := by
        rw [hsig]
        conv_lhs => arg 2; rw [hfac]
        push_cast
        rw [← Finset.prod_pow, Finset.prod_div_distrib]
      rw [hdiv]
      calc (∏ p ∈ m.primeFactors, ((m.factorization p + 1 : ℚ) ^ 6) / (p : ℚ) ^ m.factorization p)
          ≤ ∏ p ∈ m.primeFactors, Erdos647H1.primeBound p := by
            refine Finset.prod_le_prod (fun p _ => by positivity) (fun p hp => ?_)
            exact Erdos647H1.prime_pow_bound (Nat.prime_of_mem_primeFactors hp) _
        _ = ∏ p ∈ m.primeFactors ∩ Erdos647H1.smallPrimes, Erdos647H1.primeBound p := by
            symm
            refine Finset.prod_subset Finset.inter_subset_left fun p hp hnot => ?_
            have hnotS : p ∉ Erdos647H1.smallPrimes := fun hS => hnot (Finset.mem_inter.mpr ⟨hp, hS⟩)
            exact Erdos647H1.primeBound_eq_one_of_notMem (Nat.prime_of_mem_primeFactors hp) hnotS
        _ ≤ ∏ p ∈ Erdos647H1.smallPrimes, Erdos647H1.primeBound p := by
            have h1 : 1 ≤ ∏ p ∈ Erdos647H1.smallPrimes \ (m.primeFactors ∩ Erdos647H1.smallPrimes),
                Erdos647H1.primeBound p := by
              refine Finset.one_le_prod fun p hp => ?_
              have hpS := (Finset.mem_sdiff.mp hp).1
              have hpPrime : p.Prime := by
                simp only [Erdos647H1.smallPrimes, Finset.mem_insert, Finset.mem_singleton] at hpS
                rcases hpS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
              exact Erdos647H1.one_le_primeBound hpPrime
            have hnonneg : 0 ≤ ∏ p ∈ m.primeFactors ∩ Erdos647H1.smallPrimes, Erdos647H1.primeBound p := by
              refine Finset.prod_nonneg fun p hp => ?_
              exact le_trans (by norm_num) (Erdos647H1.one_le_primeBound (Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hp).1))
            have hsdiff := Finset.prod_sdiff (f := Erdos647H1.primeBound)
              (Finset.inter_subset_right (s₁ := m.primeFactors) (s₂ := Erdos647H1.smallPrimes))
            nlinarith
        _ ≤ (139 : ℚ) ^ 6 := Erdos647H1.prod_smallPrimes_le
    have hmul : ((ArithmeticFunction.sigma 0 m : ℚ) ^ 6) ≤ (139 : ℚ) ^ 6 * (m : ℚ) :=
      (div_le_iff₀ (by positivity)).mp hq
    exact_mod_cast hmul
