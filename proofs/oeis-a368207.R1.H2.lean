import OMAReductions.R_oeis_a368207_R1
import Mathlib

-- Proof of step H2 of reduction oeis-a368207.R1: the classical divisor-count limit
-- d(n)/sqrt(n) -> 0. Route: d(n) = prod over p|n of (a_p + 1); for primes p >= 17 the
-- factor (a_p+1)/p^(a_p/4) <= 1; for the finitely many primes < 16 it is bounded by a
-- constant M_p (linear is little-o of exponential), so d(n) <= C * n^(1/4); then
-- d(n)/sqrt(n) <= C * n^(-1/4) -> 0 by the squeeze theorem.


open Filter Topology Asymptotics


-- For r > 1, the sequence (a+1)/r^a is bounded. -/
set_option maxHeartbeats 800000 in
lemma exists_bound_add_one_le {r : ℝ} (hr : 1 < r) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ a : ℕ, ((a : ℝ) + 1) ≤ M * r ^ a := by
  have h := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 1 hr
  rw [isLittleO_iff] at h
  have h2 := h (by norm_num : (0 : ℝ) < 1 / 2)
  rw [eventually_atTop] at h2
  obtain ⟨A, hA⟩ := h2
  set A' := max A 2 with hA'
  have hA'a : ∀ a : ℕ, A' ≤ a → (a : ℝ) ≤ (1 / 2 : ℝ) * r ^ a := by
    intro a ha
    have h := hA a (le_trans (le_max_left A 2) ha)
    rw [pow_one, Real.norm_eq_abs, Real.norm_eq_abs] at h
    rw [abs_of_nonneg (Nat.cast_nonneg a), abs_of_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ r) a)] at h
    exact h
  have h1r : 1 ≤ r := by linarith
  refine ⟨(A' : ℝ) + 1, by
    have : (2 : ℝ) ≤ (A' : ℝ) := by exact_mod_cast le_max_right A 2
    linarith, fun a => ?_⟩
  have hge : 1 ≤ r ^ a := one_le_pow₀ h1r
  have hnn : 0 ≤ r ^ a := by positivity
  by_cases ha : a < A'
  · have h1 : ((a : ℝ) + 1) ≤ (A' : ℝ) + 1 := by
      have : (a : ℝ) ≤ (A' : ℝ) := by exact_mod_cast ha.le
      linarith
    calc ((a : ℝ) + 1) ≤ (A' : ℝ) + 1 := h1
      _ = ((A' : ℝ) + 1) * 1 := by ring
      _ ≤ ((A' : ℝ) + 1) * r ^ a := mul_le_mul_of_nonneg_left hge (by positivity)
  · have hle := hA'a a (by omega)
    have hA'2 : (2 : ℝ) ≤ A' := by exact_mod_cast le_max_right A 2
    calc ((a : ℝ) + 1) ≤ (1 / 2 : ℝ) * r ^ a + 1 := by linarith
      _ ≤ (1 / 2 : ℝ) * r ^ a + r ^ a := by linarith
      _ = (3 / 2 : ℝ) * r ^ a := by ring
      _ ≤ ((A' : ℝ) + 1) * r ^ a := mul_le_mul_of_nonneg_right (by linarith) hnn

-- Product of rpow: (∏ f i)^ε = ∏ (f i)^ε for nonneg f. -/
set_option maxHeartbeats 800000 in
lemma prod_rpow {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) (ε : ℝ) :
    (∏ i ∈ s, f i) ^ ε = ∏ i ∈ s, (f i) ^ ε := by
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      have hfi : 0 ≤ f i := hf i (Finset.mem_insert_self i s)
      have hfs : 0 ≤ ∏ j ∈ s, f j := Finset.prod_nonneg fun j hj => hf j (Finset.mem_insert_of_mem hj)
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Real.mul_rpow hfi hfs,
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

-- The primes below 16. -/
def badPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13}

set_option maxHeartbeats 800000 in
lemma badPrimes_prime : ∀ p ∈ badPrimes, p.Prime := by decide

set_option maxHeartbeats 800000 in
lemma one_lt_rpow_quarter {p : ℕ} (hp : p.Prime) : 1 < (p : ℝ) ^ (1 / 4 : ℝ) := by
  apply Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by norm_num : (0:ℝ) < 1/4)

-- Bounds for the finitely many bad primes. -/
set_option maxHeartbeats 800000 in
lemma exists_bad_bounds : ∃ M : ℕ → ℝ, ∀ p ∈ badPrimes,
    1 ≤ M p ∧ ∀ a : ℕ, ((a : ℝ) + 1) ≤ M p * (p : ℝ) ^ ((a : ℝ) * (1 / 4 : ℝ)) := by
  have key : ∀ p ∈ badPrimes, ∃ M : ℝ, 1 ≤ M ∧
      ∀ a : ℕ, ((a : ℝ) + 1) ≤ M * (p : ℝ) ^ ((a : ℝ) * (1 / 4 : ℝ)) := by
    intro p hp
    obtain ⟨M, hM, hb⟩ := exists_bound_add_one_le (r := (p : ℝ) ^ (1 / 4 : ℝ))
      (one_lt_rpow_quarter (badPrimes_prime p hp))
    refine ⟨M, hM, fun a => ?_⟩
    have hconv : ((p : ℝ) ^ (1 / 4 : ℝ)) ^ a = (p : ℝ) ^ ((a : ℝ) * (1 / 4 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (p : ℝ))]
      ring_nf
    have h := hb a
    rw [hconv] at h
    exact h
  choose! M hM using key
  exact ⟨M, hM⟩

-- Main bound: d(n) ≤ C * n^(1/4) for all n ≥ 1. -/
set_option maxHeartbeats 800000 in
lemma card_divisors_le {M : ℕ → ℝ} (hM : ∀ p ∈ badPrimes, 1 ≤ M p ∧
    ∀ a : ℕ, ((a : ℝ) + 1) ≤ M p * (p : ℝ) ^ ((a : ℝ) * (1 / 4 : ℝ))) (n : ℕ) (hn : n ≠ 0) :
    (n.divisors.card : ℝ) ≤ (∏ p ∈ badPrimes, M p) * (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hcard := Nat.card_divisors hn
  have hcardR : (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ) := by
    rw [hcard, Nat.cast_prod]
  rw [hcardR]
  -- per-factor bound
  have hfac : ∀ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ) ≤
      (if p ∈ badPrimes then M p else 1) * (p : ℝ) ^ ((n.factorization p : ℝ) * (1 / 4 : ℝ)) := by
    intro p hp
    have hpP := Nat.prime_of_mem_primeFactors hp
    set a := n.factorization p with ha
    by_cases hb : p ∈ badPrimes
    · obtain ⟨hMpos, hMb⟩ := hM p hb
      rw [if_pos hb]
      push_cast
      have := hMb a
      rw [ha] at this
      -- this : ((a:ℝ)+1) ≤ M p * (p:ℝ)^(a*(1/4)); LHS cast matches
      push_cast at this ⊢
      exact this
    · rw [if_neg hb]
      have hp17 : 17 ≤ p := by
        by_contra hlt
        have hlt17 : p < 17 := by omega
        have hmem : p ∈ badPrimes := by
          have hdec : ∀ q : ℕ, q < 17 → q.Prime → q ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ) := by decide
          exact hdec p hlt17 hpP
        exact hb (by simpa [badPrimes] using hmem)
      -- (a+1) ≤ 2^a ≤ (p^{1/4})^a = p^{a/4}
      have h1 : ((a : ℝ) + 1) ≤ (2 : ℝ) ^ a := by
        induction a with
        | zero => norm_num
        | succ a ih =>
            have h : ((a + 1 : ℕ) : ℝ) + 1 = (a : ℝ) + 2 := by push_cast; ring
            rw [pow_succ, h]
            nlinarith
      have h2 : (2 : ℝ) ^ a ≤ ((p : ℝ) ^ (1 / 4 : ℝ)) ^ a := by
        apply pow_le_pow_left₀ (by norm_num)
        have h16 : (16 : ℝ) ≤ p := by exact_mod_cast (by omega : 16 ≤ p)
        have h2q : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
          have h16 : (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
          rw [h16, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
          norm_num
        rw [← h2q]
        exact Real.rpow_le_rpow (by norm_num) h16 (by norm_num)
      have h3 : ((p : ℝ) ^ (1 / 4 : ℝ)) ^ a = (p : ℝ) ^ ((a : ℝ) * (1 / 4 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (p : ℝ))]
        ring_nf
      push_cast
      calc ((a : ℝ) + 1) ≤ (2 : ℝ) ^ a := h1
        _ ≤ (p : ℝ) ^ ((a : ℝ) * (1 / 4 : ℝ)) := by rw [← h3]; exact h2
        _ = 1 * (p : ℝ) ^ ((a : ℝ) * (1 / 4 : ℝ)) := by ring
  -- product inequality
  have hnn : ∀ p ∈ n.primeFactors, 0 ≤ ((n.factorization p + 1 : ℕ) : ℝ) := by
    intro p _; positivity
  have hprod := Finset.prod_le_prod hnn hfac
  rw [Finset.prod_mul_distrib] at hprod
  -- ∏ (p:ℝ)^(a_p * 1/4) = (∏ p^{a_p})^{1/4} = n^{1/4}
  have h_rpow_prod : (∏ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) * (1 / 4 : ℝ))) =
      (n : ℝ) ^ (1 / 4 : ℝ) := by
    have h1 : (∏ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) * (1 / 4 : ℝ))) =
        ∏ p ∈ n.primeFactors, (((p : ℝ) ^ (n.factorization p : ℕ)) ^ (1 / 4 : ℝ)) :=
      Finset.prod_congr rfl fun p hp => by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (p:ℝ))]
    rw [h1, ← prod_rpow _ _ (fun p hp => by positivity) (1/4:ℝ)]
    have h2 : (∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p : ℕ)) = (n : ℝ) := by
      have h : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
        have h0 := Nat.prod_factorization_pow_eq_self hn
        unfold Finsupp.prod at h0
        rwa [Nat.support_factorization] at h0
      calc (∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p : ℕ))
          = ((∏ p ∈ n.primeFactors, p ^ n.factorization p : ℕ) : ℝ) := by
            simp [Nat.cast_prod, Nat.cast_pow]
        _ = (n : ℝ) := by exact_mod_cast h
    rw [h2]
  rw [h_rpow_prod] at hprod
  -- ∏ (if p ∈ bad then M p else 1) ≤ ∏ p ∈ badPrimes, M p
  have hMprod : (∏ p ∈ n.primeFactors, (if p ∈ badPrimes then M p else 1)) ≤
      ∏ p ∈ badPrimes, M p := by
    rw [← Finset.prod_filter]
    have hsub : n.primeFactors.filter (· ∈ badPrimes) ⊆ badPrimes :=
      fun q hq => (Finset.mem_filter.mp hq).2
    exact Finset.prod_le_prod_of_subset_of_one_le hsub
      (fun q hq => le_trans (by norm_num : (0:ℝ) ≤ 1) (hM q (Finset.mem_filter.mp hq).2).1)
      (fun q hq _ => (hM q hq).1)
  -- combine
  have hCnn : 0 ≤ ∏ p ∈ badPrimes, M p :=
    Finset.prod_nonneg fun q hq => le_trans (by norm_num : (0:ℝ) ≤ 1) (hM q hq).1
  calc ∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ)
      ≤ (∏ p ∈ n.primeFactors, (if p ∈ badPrimes then M p else 1)) * (n : ℝ) ^ (1 / 4 : ℝ) := hprod
    _ ≤ (∏ p ∈ badPrimes, M p) * (n : ℝ) ^ (1 / 4 : ℝ) := by
        apply mul_le_mul_of_nonneg_right hMprod
        exact Real.rpow_nonneg (Nat.cast_nonneg n) _

-- The classical divisor-count limit: d(n)/sqrt(n) → 0. -/
set_option maxHeartbeats 800000 in
theorem div_sqrt_tendsto : Tendsto (fun n : ℕ => (n.divisors.card : ℝ) / Real.sqrt n) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := exists_bad_bounds
  set C := ∏ p ∈ badPrimes, M p with hC
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1)
    (Finset.one_le_prod fun p hp => hM p hp |>.1)
  have hbound : ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / 4 : ℝ) :=
    fun n hn => card_divisors_le hM n hn
  have hle : ∀ n : ℕ, (n.divisors.card : ℝ) / Real.sqrt n ≤ C * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [Real.zero_rpow (by norm_num : (-(1 / 4 : ℝ)) ≠ 0)]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hb := hbound n hn
      rw [Real.sqrt_eq_rpow]
      calc (n.divisors.card : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ)
          ≤ (C * (n : ℝ) ^ (1 / 4 : ℝ)) / (n : ℝ) ^ (1 / 2 : ℝ) := by
            apply div_le_div_of_nonneg_right hb
            exact Real.rpow_nonneg (by positivity) _
        _ = C * ((n : ℝ) ^ (1 / 4 : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ)) := by ring
        _ = C * (n : ℝ) ^ ((1 / 4 : ℝ) - (1 / 2 : ℝ)) := by rw [Real.rpow_sub hnpos]
        _ = C * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by ring_nf
  have hge : ∀ n : ℕ, 0 ≤ (n.divisors.card : ℝ) / Real.sqrt n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ hge hle
  have h14 : (0 : ℝ) < 1 / 4 := by norm_num
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop h14 |>.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) ^ (1 / 4 : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h1
  have h3 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
    simpa only [Real.rpow_neg (Nat.cast_nonneg _)] using h2
  simpa using h3.const_mul C

set_option maxHeartbeats 800000 in
theorem OMA.solution : OMA.R_oeis_a368207_R1.H2 := by
  show Tendsto (fun n : ℕ => (n.divisors.card : ℝ) / Real.sqrt n) atTop (𝓝 0)
  exact div_sqrt_tendsto
