import OMAReductions.R_Erdos647_erdos_647_R1

/-!
# Proof of `Erdos647.erdos_647.R1.H1`

For every `m : ℕ`, `(σ 0 m) ^ 6 ≤ 139 ^ 6 * m`.
Proved by maximizing `(k + 1)^6 / p^k` independently at each prime `p`:
primes `p ≥ 64` satisfy `(k + 1)^6 ≤ p^k`, while the 18 primes `p < 64`
contribute a product whose sixth root is `≈ 138.313 < 139`.
-/

open ArithmeticFunction.sigma

namespace Erdos647R1H1Proof

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

private lemma prime_lt_64_mem {p : ℕ} (hp : p.Prime) (hlt : p < 64) : p ∈ smallPrimes := by
  have h2 : p ≤ 63 := by omega
  interval_cases p <;> first | (simp [smallPrimes]; done) | exact absurd hp (by norm_num)

private lemma one_le_primeBound {p : ℕ} (hp : p.Prime) : (1 : ℚ) ≤ primeBound p := by
  unfold primeBound
  split_ifs with h2 h3 h5 h7 h11 h64
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · have hp_pos : (0 : ℚ) < (p : ℚ) := Nat.cast_pos.mpr hp.pos
    rw [one_le_div hp_pos]
    exact_mod_cast le_of_lt h64
  · exact le_rfl

private lemma step_le_pow {p a k : ℕ} (hk : a ≤ k) (hstep : (a + 2) ^ 6 ≤ p * (a + 1) ^ 6)
    (hbase : ∀ j ≤ a, (j + 1) ^ 6 * d ≤ c * p ^ j) :
    (k + 1) ^ 6 * d ≤ c * p ^ k := by
  induction k with
  | zero => exact hbase 0 (by omega)
  | succ m ih =>
    by_cases hm : m + 1 ≤ a
    · exact hbase (m + 1) hm
    · have hma : a ≤ m := by omega
      have ihm := ih hma
      have hratio : (m + 2) ^ 6 ≤ p * (m + 1) ^ 6 := by
        have h1 : (m + 2) * (a + 1) ≤ (a + 2) * (m + 1) := by nlinarith
        have h2 : ((m + 2) * (a + 1)) ^ 6 ≤ ((a + 2) * (m + 1)) ^ 6 := Nat.pow_le_pow_left h1 6
        rw [mul_pow, mul_pow] at h2
        have h3 : (m + 2) ^ 6 * (a + 1) ^ 6 ≤ (p * (a + 1) ^ 6) * (m + 1) ^ 6 :=
          h2.trans (Nat.mul_le_mul_right _ hstep)
        have hpos : 0 < (a + 1) ^ 6 := by positivity
        nlinarith
      calc (m + 1 + 1) ^ 6 * d = (m + 2) ^ 6 * d := by ring
        _ ≤ (p * (m + 1) ^ 6) * d := Nat.mul_le_mul_right d hratio
        _ = p * ((m + 1) ^ 6 * d) := by ring
        _ ≤ p * (c * p ^ m) := Nat.mul_le_mul_left p ihm
        _ = c * p ^ (m + 1) := by rw [pow_succ]; ring

private lemma nat_pow_bound_ge_64 {p k : ℕ} (hp : 64 ≤ p) : (k + 1) ^ 6 ≤ p ^ k := by
  have h1 : k + 1 ≤ 2 ^ k := by
    induction k with
    | zero => simp
    | succ m ih =>
      rw [pow_succ]
      have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      omega
  calc (k + 1) ^ 6 ≤ (2 ^ k) ^ 6 := Nat.pow_le_pow_left h1 6
    _ = (2 ^ 6) ^ k := by rw [← pow_mul, mul_comm, pow_mul]
    _ ≤ p ^ k := Nat.pow_le_pow_left (by omega) k

private lemma prime_power_bound {p k : ℕ} (hp : p.Prime) :
    ((k + 1 : ℚ) ^ 6) / (p : ℚ) ^ k ≤ primeBound p := by
  have hpk_pos : (0 : ℚ) < (p : ℚ) ^ k := pow_pos (Nat.cast_pos.mpr hp.pos) k
  rw [div_le_iff₀ hpk_pos]
  unfold primeBound
  split_ifs with h2 h3 h5 h7 h11 h64
  · subst h2
    have hnat : (k + 1) ^ 6 * 256 ≤ 531441 * 2 ^ k := by
      by_cases hk : k ≤ 8
      · interval_cases k <;> norm_num
      · exact step_le_pow (a := 8) (by omega) (by norm_num)
          (fun j hj => by interval_cases j <;> norm_num)
    have hq : ((k + 1 : ℚ) ^ 6) * 256 ≤ 531441 * (2 : ℚ) ^ k := by exact_mod_cast hnat
    linarith
  · subst h3
    have hnat : (k + 1) ^ 6 * 81 ≤ 15625 * 3 ^ k := by
      by_cases hk : k ≤ 4
      · interval_cases k <;> norm_num
      · exact step_le_pow (a := 4) (by omega) (by norm_num)
          (fun j hj => by interval_cases j <;> norm_num)
    have hq : ((k + 1 : ℚ) ^ 6) * 81 ≤ 15625 * (3 : ℚ) ^ k := by exact_mod_cast hnat
    linarith
  · subst h5
    have hnat : (k + 1) ^ 6 * 125 ≤ 4096 * 5 ^ k := by
      by_cases hk : k ≤ 3
      · interval_cases k <;> norm_num
      · exact step_le_pow (a := 3) (by omega) (by norm_num)
          (fun j hj => by interval_cases j <;> norm_num)
    have hq : ((k + 1 : ℚ) ^ 6) * 125 ≤ 4096 * (5 : ℚ) ^ k := by exact_mod_cast hnat
    linarith
  · subst h7
    have hnat : (k + 1) ^ 6 * 49 ≤ 729 * 7 ^ k := by
      by_cases hk : k ≤ 2
      · interval_cases k <;> norm_num
      · exact step_le_pow (a := 2) (by omega) (by norm_num)
          (fun j hj => by interval_cases j <;> norm_num)
    have hq : ((k + 1 : ℚ) ^ 6) * 49 ≤ 729 * (7 : ℚ) ^ k := by exact_mod_cast hnat
    linarith
  · subst h11
    have hnat : (k + 1) ^ 6 * 121 ≤ 729 * 11 ^ k := by
      by_cases hk : k ≤ 2
      · interval_cases k <;> norm_num
      · exact step_le_pow (a := 2) (by omega) (by norm_num)
          (fun j hj => by interval_cases j <;> norm_num)
    have hq : ((k + 1 : ℚ) ^ 6) * 121 ≤ 729 * (11 : ℚ) ^ k := by exact_mod_cast hnat
    linarith
  · have hp13 : 13 ≤ p := by
      have hmem := prime_lt_64_mem hp h64
      simp only [smallPrimes, Finset.mem_insert, Finset.mem_singleton] at hmem
      omega
    have hnat : (k + 1) ^ 6 * p ≤ 64 * p ^ k := by
      by_cases hk : k ≤ 2
      · interval_cases k
        · simp; omega
        · simp
        · norm_num; nlinarith
      · exact step_le_pow (a := 2) (by omega) (by norm_num; nlinarith) (fun j hj => by
          interval_cases j
          · simp; omega
          · simp
          · norm_num; nlinarith)
    have hq : ((k + 1 : ℚ) ^ 6) * (p : ℚ) ≤ 64 * (p : ℚ) ^ k := by exact_mod_cast hnat
    have hp_pos : (0 : ℚ) < (p : ℚ) := Nat.cast_pos.mpr hp.pos
    rw [div_mul_eq_mul_div, le_div_iff₀ hp_pos]
    linarith
  · rw [one_mul]
    exact_mod_cast nat_pow_bound_ge_64 (by omega : 64 ≤ p)

private lemma prod_smallPrimes_le :
    ∏ p ∈ smallPrimes, primeBound p ≤ (139 : ℚ) ^ 6 := by
  simp only [smallPrimes, primeBound]
  norm_num

end Erdos647R1H1Proof

open Erdos647R1H1Proof in
theorem OMA.solution : OMA.R_Erdos647_erdos_647_R1.H1 := by
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hm_ne : m ≠ 0 := by omega
    have hsigma : σ 0 m = ∏ p ∈ m.primeFactors, (m.factorization p + 1) := by
      rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hm_ne]
    have hself : m = ∏ p ∈ m.primeFactors, p ^ m.factorization p := by
      have h := Nat.prod_factorization_pow_eq_self hm_ne
      simpa [Finsupp.prod, Nat.support_factorization] using h.symm
    have hq_ratio : ((σ 0 m : ℚ) ^ 6) / (m : ℚ) ≤ (139 : ℚ) ^ 6 := by
      have hnum : ((σ 0 m : ℚ) ^ 6) =
          ∏ p ∈ m.primeFactors, ((m.factorization p + 1 : ℕ) : ℚ) ^ 6 := by
        rw [hsigma, Nat.cast_prod, Finset.prod_pow]
      have hden : (m : ℚ) =
          ∏ p ∈ m.primeFactors, ((p ^ m.factorization p : ℕ) : ℚ) := by
        conv_lhs => rw [hself]
        rw [Nat.cast_prod]
      rw [hnum, hden, ← Finset.prod_div_distrib]
      have h1 :
          ∏ p ∈ m.primeFactors,
            ((m.factorization p + 1 : ℕ) : ℚ) ^ 6 / ((p ^ m.factorization p : ℕ) : ℚ) ≤
          ∏ p ∈ m.primeFactors, primeBound p := by
        refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
        have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
        push_cast
        exact prime_power_bound hprime
      have h2 : ∏ p ∈ m.primeFactors, primeBound p ≤
          ∏ p ∈ smallPrimes, primeBound p := by
        have hsplit :
            ∏ p ∈ m.primeFactors, primeBound p =
              ∏ p ∈ m.primeFactors ∩ smallPrimes, primeBound p := by
          symm
          refine Finset.prod_subset Finset.inter_subset_left fun p hp hnot => ?_
          have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
          have hge64 : ¬ (p < 64) := fun hlt =>
            hnot (Finset.mem_inter.mpr ⟨hp, prime_lt_64_mem hprime hlt⟩)
          have hne2 : p ≠ 2 := by omega
          have hne3 : p ≠ 3 := by omega
          have hne5 : p ≠ 5 := by omega
          have hne7 : p ≠ 7 := by omega
          have hne11 : p ≠ 11 := by omega
          simp [primeBound, hne2, hne3, hne5, hne7, hne11, hge64]
        rw [hsplit]
        have hsub : m.primeFactors ∩ smallPrimes ⊆ smallPrimes := Finset.inter_subset_right
        have hone : ∀ p ∈ smallPrimes, (1 : ℚ) ≤ primeBound p := by
          intro p hp
          have hprime : p.Prime := by
            simp only [smallPrimes, Finset.mem_insert, Finset.mem_singleton] at hp
            rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
              rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
          exact one_le_primeBound hprime
        rw [← Finset.prod_sdiff hsub]
        have h1_sdiff : (1 : ℚ) ≤ ∏ p ∈ smallPrimes \ (m.primeFactors ∩ smallPrimes), primeBound p :=
          Finset.one_le_prod fun p hp => hone p (Finset.mem_sdiff.mp hp).1
        have h0_inter : (0 : ℚ) ≤ ∏ p ∈ m.primeFactors ∩ smallPrimes, primeBound p :=
          Finset.prod_nonneg fun p hp => by linarith [hone p (hsub hp)]
        nlinarith
      exact h1.trans (h2.trans prod_smallPrimes_le)
    have hm_pos : (0 : ℚ) < (m : ℚ) := Nat.cast_pos.mpr hm
    rw [div_le_iff₀ hm_pos] at hq_ratio
    exact_mod_cast hq_ratio
