import OMAReductions.R_Erdos999_erdos_999_R1

-- Reduction of step H2 of Erdos999.erdos_999.R1 (the second moment bound) to the two inputs of
-- Koukoulopoulos and Maynard, Section 5: the overlap estimate of Pollington and Vaughan and their
-- Proposition 5.4. The dyadic summation argument is carried out here with scales 4^j and an
-- elementary bound for the sum of reciprocals of primes, so that Mertens is not needed.
namespace OMA.R_Erdos999_erdos_999_R1_H2_R1

open MeasureTheory Filter Set Metric
open scoped Topology

-- Odd primes below 2N+2 have reciprocal sum at most half the N-th harmonic number.
lemma sum_odd_primes_le (N : ℕ) :
    ∑ p ∈ Finset.range (2 * N + 2), (if 3 ≤ p ∧ p.Prime then (1 : ℝ) / p else 0) ≤
      (1 / 2) * ∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1) := by
  induction N with
  | zero =>
    simp only [Nat.zero_add, Finset.range_zero, Finset.sum_empty, mul_zero]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro p hp
    have : p < 2 := Finset.mem_range.1 hp
    rw [if_neg]
    omega
  | succ N ih =>
    have e1 : 2 * (N + 1) + 2 = (2 * N + 2) + 1 + 1 := by ring
    rw [e1, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ (fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 1)) N, mul_add]
    have h2 : (if 3 ≤ 2 * N + 2 ∧ (2 * N + 2).Prime then (1 : ℝ) / ((2 * N + 2 : ℕ) : ℝ) else 0)
        = 0 := by
      rw [if_neg]
      rintro ⟨h3, hp⟩
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 ⟨N + 1, by ring⟩
      omega
    have h3 : (if 3 ≤ 2 * N + 2 + 1 ∧ (2 * N + 2 + 1).Prime
        then (1 : ℝ) / ((2 * N + 2 + 1 : ℕ) : ℝ) else 0) ≤ 1 / 2 * (1 / ((N : ℝ) + 1)) := by
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      split_ifs
      · push_cast
        rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      · positivity
    rw [h2]
    linarith

-- Reciprocals of all primes below X, for X at most 2N+2.
lemma sum_primes_le (X N : ℕ) (hX : X ≤ 2 * N + 2) :
    ∑ p ∈ (Finset.range X).filter Nat.Prime, (1 : ℝ) / p ≤
      1 / 2 + (1 / 2) * ∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1) := by
  have hsub : (Finset.range X).filter Nat.Prime ⊆ (Finset.range (2 * N + 2)).filter Nat.Prime :=
    Finset.filter_subset_filter _ (Finset.range_subset_range.2 hX)
  have h1 : ∑ p ∈ (Finset.range X).filter Nat.Prime, (1 : ℝ) / p ≤
      ∑ p ∈ (Finset.range (2 * N + 2)).filter Nat.Prime, (1 : ℝ) / p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
  have h1 := h1.trans (le_of_eq (Finset.sum_filter _ _))
  have h2 : ∑ p ∈ Finset.range (2 * N + 2), (if p.Prime then (1 : ℝ) / p else 0) ≤
      ∑ p ∈ Finset.range (2 * N + 2), ((if p = 2 then (1 : ℝ) / 2 else 0) +
        (if 3 ≤ p ∧ p.Prime then (1 : ℝ) / p else 0)) := by
    apply Finset.sum_le_sum
    intro p _
    by_cases hp : p.Prime
    · rw [if_pos hp]
      rcases (Nat.succ_le_of_lt hp.one_lt).eq_or_lt with h | h
      · have h2 : p = 2 := h.symm
        rw [if_pos h2, if_neg (by omega), h2]
        norm_num
      · rw [if_neg (by omega), if_pos ⟨by omega, hp⟩]
        linarith
    · rw [if_neg hp]
      have : (0 : ℝ) ≤ if p = 2 then (1 : ℝ) / 2 else 0 := by split_ifs <;> norm_num
      have : (0 : ℝ) ≤ if 3 ≤ p ∧ p.Prime then (1 : ℝ) / p else 0 := by
        split_ifs <;> positivity
      linarith
  rw [Finset.sum_add_distrib] at h2
  have h3 : ∑ p ∈ Finset.range (2 * N + 2), (if p = 2 then (1 : ℝ) / 2 else 0) ≤ 1 / 2 := by
    rw [Finset.sum_ite_eq']
    split_ifs <;> norm_num
  linarith [sum_odd_primes_le N]

-- The harmonic sum is at most 1 + log N.
lemma harmonic_sum_le (N : ℕ) :
    ∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1) ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  have e : ((harmonic N : ℚ) : ℝ) = ∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1) := by
    unfold harmonic
    push_cast
    exact Finset.sum_congr rfl (fun i _ => by rw [one_div])
  rw [e] at h
  exact h

-- Reciprocals of primes below 4^(j+1): the exponential is at most 6 * 2^j.
lemma exp_sum_primes_le (j : ℕ) :
    Real.exp (∑ p ∈ (Finset.range (4 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / p) ≤ 6 * 2 ^ j := by
  have hX : 4 ^ (j + 1) ≤ 2 * (2 * 4 ^ j) + 2 := by
    rw [pow_succ]
    omega
  have h1 := sum_primes_le (4 ^ (j + 1)) (2 * 4 ^ j) hX
  have h2 := harmonic_sum_le (2 * 4 ^ j)
  have h3 : Real.log ((2 * 4 ^ j : ℕ) : ℝ) ≤ 2 * Real.log ((2 : ℝ) ^ (j + 1)) := by
    rw [← Real.log_rpow (by positivity)]
    apply Real.log_le_log (by positivity)
    have e : ((2 : ℝ) ^ (j + 1)) ^ (2 : ℝ) = 4 * 4 ^ j := by
      rw [Real.rpow_two]
      calc ((2 : ℝ) ^ (j + 1)) ^ 2 = ((2 : ℝ) ^ 2) ^ (j + 1) := by
            rw [← pow_mul, ← pow_mul, mul_comm]
        _ = 4 ^ (j + 1) := by norm_num
        _ = 4 * 4 ^ j := by rw [pow_succ]; ring
    rw [e]
    push_cast
    have : (0 : ℝ) < 4 ^ j := by positivity
    linarith
  have h4 : ∑ p ∈ (Finset.range (4 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / p ≤
      1 + Real.log ((2 : ℝ) ^ (j + 1)) := by
    linarith
  calc Real.exp (∑ p ∈ (Finset.range (4 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / p)
      ≤ Real.exp (1 + Real.log ((2 : ℝ) ^ (j + 1))) := Real.exp_le_exp.2 h4
    _ = Real.exp 1 * (2 : ℝ) ^ (j + 1) := by
      rw [Real.exp_add, Real.exp_log (by positivity)]
    _ ≤ 3 * (2 : ℝ) ^ (j + 1) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith [Real.exp_one_lt_d9]
    _ = 6 * 2 ^ j := by
      rw [pow_succ]
      ring

-- Reciprocals of the integers strictly between 4^j and 4^(j+1) sum to at most 3.
lemma sum_block_le (j : ℕ) :
    ∑ m ∈ Finset.Ioo ((4 : ℕ) ^ j) ((4 : ℕ) ^ (j + 1)), (1 : ℝ) / (m : ℝ) ≤ 3 := by
  have hpos : (0 : ℝ) < 4 ^ j := by positivity
  have h1 : ∀ m ∈ Finset.Ioo ((4 : ℕ) ^ j) ((4 : ℕ) ^ (j + 1)), (1 : ℝ) / (m : ℝ) ≤ 1 / 4 ^ j := by
    intro m hm
    have hm1 : 4 ^ j < m := (Finset.mem_Ioo.1 hm).1
    have hm2 : ((4 ^ j : ℕ) : ℝ) ≤ m := by exact_mod_cast hm1.le
    push_cast at hm2
    exact one_div_le_one_div_of_le hpos hm2
  have h2 := Finset.sum_le_sum h1
  rw [Finset.sum_const, Nat.card_Ioo, nsmul_eq_mul] at h2
  refine h2.trans ?_
  have hc : ((4 ^ (j + 1) - 4 ^ j - 1 : ℕ) : ℝ) ≤ 3 * 4 ^ j := by
    have : 4 ^ (j + 1) - 4 ^ j - 1 ≤ 3 * 4 ^ j := by
      rw [pow_succ]
      omega
    exact_mod_cast this
  rw [mul_one_div, div_le_iff₀ hpos]
  exact hc

-- The pointwise bound behind the dyadic argument.
lemma prod_bound (n : ℕ) (D : ℝ) (J : ℕ) (hJ : n < 4 ^ J) :
    ∏ p ∈ n.primeFactors.filter (fun p : ℕ => D < p), (1 + 1 / (p : ℝ)) ≤
      Real.exp 13 + ∑ j ∈ Finset.range J,
        (if D ≤ (4 : ℝ) ^ j ∧
            10 ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ => (4 : ℝ) ^ j ≤ p), 1 / (p : ℝ)
          then 6 * Real.exp 10 * 2 ^ j else 0) := by
  obtain ⟨L, hL⟩ : ∃ L : ℝ → ℝ, ∀ t, L t =
      ∑ p ∈ n.primeFactors.filter (fun p : ℕ => t ≤ p), 1 / (p : ℝ) := ⟨_, fun _ => rfl⟩
  simp only [← hL]
  have hterm : ∀ j : ℕ, (0 : ℝ) ≤
      (if D ≤ (4 : ℝ) ^ j ∧ 10 ≤ L ((4 : ℝ) ^ j) then 6 * Real.exp 10 * 2 ^ j else 0) := by
    intro j
    split_ifs <;> positivity
  have hsum0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range J,
      (if D ≤ (4 : ℝ) ^ j ∧ 10 ≤ L ((4 : ℝ) ^ j) then 6 * Real.exp 10 * 2 ^ j else 0) :=
    Finset.sum_nonneg (fun j _ => hterm j)
  have hP : ∏ p ∈ n.primeFactors.filter (fun p : ℕ => D < p), (1 + 1 / (p : ℝ)) ≤
      Real.exp (∑ p ∈ n.primeFactors.filter (fun p : ℕ => D < p), 1 / (p : ℝ)) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p _
      positivity
    · intro p _
      linarith [Real.add_one_le_exp (1 / (p : ℝ))]
  -- splitting the sum over primes above D at a threshold X
  have hsplit : ∀ X : ℝ, ∑ p ∈ n.primeFactors.filter (fun p : ℕ => D < p), 1 / (p : ℝ) ≤
      ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => D < p)).filter (fun p : ℕ => (p : ℝ) < X),
        1 / (p : ℝ) + L X := by
    intro X
    rw [← Finset.sum_filter_add_sum_filter_not (n.primeFactors.filter (fun p : ℕ => D < p))
      (fun p : ℕ => (p : ℝ) < X)]
    apply add_le_add le_rfl
    rw [hL]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [Finset.mem_filter, not_lt] at hp ⊢
      exact ⟨hp.1.1, hp.2⟩
    · intro p _ _
      positivity
  by_cases h1 : 10 ≤ L 1
  · obtain ⟨j, hjJ, hj0, hjmax⟩ : ∃ j, j ≤ J ∧ 10 ≤ L ((4 : ℝ) ^ j) ∧
        ∀ k, j < k → k ≤ J → ¬ (10 ≤ L ((4 : ℝ) ^ k)) := by
      refine ⟨Nat.findGreatest (fun j => 10 ≤ L ((4 : ℝ) ^ j)) J, Nat.findGreatest_le J, ?_, ?_⟩
      · exact Nat.findGreatest_spec (P := fun j => 10 ≤ L ((4 : ℝ) ^ j)) (Nat.zero_le J)
          (by simpa using h1)
      · intro k hk hkJ
        exact Nat.findGreatest_is_greatest hk hkJ
    have hLJ : L ((4 : ℝ) ^ J) = 0 := by
      rw [hL]
      apply Finset.sum_eq_zero
      intro p hp
      exfalso
      simp only [Finset.mem_filter] at hp
      have hpn : p ≤ n := Nat.le_of_mem_primeFactors hp.1
      have : (p : ℝ) < (4 : ℝ) ^ J := by exact_mod_cast lt_of_le_of_lt hpn hJ
      linarith [hp.2]
    have hjlt : j < J := by
      rcases hjJ.eq_or_lt with h | h
      · rw [h, hLJ] at hj0
        linarith
      · exact h
    have hj1 : L ((4 : ℝ) ^ (j + 1)) < 10 := not_le.1 (hjmax (j + 1) (lt_add_one j) hjlt)
    have hs := hsplit ((4 : ℝ) ^ (j + 1))
    by_cases hD : D ≤ (4 : ℝ) ^ j
    · -- the pair lies in the exceptional set at scale 4^j
      have hfirst : ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => D < p)).filter
          (fun p : ℕ => (p : ℝ) < (4 : ℝ) ^ (j + 1)), 1 / (p : ℝ) ≤
          ∑ p ∈ (Finset.range (4 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
          refine ⟨?_, Nat.prime_of_mem_primeFactors hp.1.1⟩
          have := hp.2
          exact_mod_cast this
        · intro p _ _
          positivity
      have hexp : Real.exp (∑ p ∈ n.primeFactors.filter (fun p : ℕ => D < p), 1 / (p : ℝ)) ≤
          6 * Real.exp 10 * 2 ^ j := by
        calc Real.exp (∑ p ∈ n.primeFactors.filter (fun p : ℕ => D < p), 1 / (p : ℝ))
            ≤ Real.exp (∑ p ∈ (Finset.range (4 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / p + 10) :=
              Real.exp_le_exp.2 (by linarith)
          _ = Real.exp (∑ p ∈ (Finset.range (4 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / p) *
              Real.exp 10 := Real.exp_add _ _
          _ ≤ 6 * 2 ^ j * Real.exp 10 :=
              mul_le_mul_of_nonneg_right (exp_sum_primes_le j) (Real.exp_pos _).le
          _ = 6 * Real.exp 10 * 2 ^ j := by ring
      have hmem : (if D ≤ (4 : ℝ) ^ j ∧ 10 ≤ L ((4 : ℝ) ^ j) then 6 * Real.exp 10 * 2 ^ j else 0)
          ≤ ∑ j ∈ Finset.range J,
            (if D ≤ (4 : ℝ) ^ j ∧ 10 ≤ L ((4 : ℝ) ^ j) then 6 * Real.exp 10 * 2 ^ j else 0) :=
        Finset.single_le_sum (f := fun j : ℕ =>
          (if D ≤ (4 : ℝ) ^ j ∧ 10 ≤ L ((4 : ℝ) ^ j) then 6 * Real.exp 10 * 2 ^ j else 0))
          (fun j _ => hterm j) (Finset.mem_range.2 hjlt)
      rw [if_pos ⟨hD, hj0⟩] at hmem
      linarith [Real.exp_pos (13 : ℝ)]
    · -- D is above 4^j: the product is bounded
      have hD' : (4 : ℝ) ^ j < D := not_le.1 hD
      have hfirst : ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => D < p)).filter
          (fun p : ℕ => (p : ℝ) < (4 : ℝ) ^ (j + 1)), 1 / (p : ℝ) ≤
          ∑ m ∈ Finset.Ioo ((4 : ℕ) ^ j) ((4 : ℕ) ^ (j + 1)), (1 : ℝ) / (m : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_Ioo] at hp ⊢
          constructor
          · have : ((4 ^ j : ℕ) : ℝ) < (p : ℝ) := by
              push_cast
              linarith [hp.1.2]
            exact_mod_cast this
          · have := hp.2
            exact_mod_cast this
        · intro p _ _
          positivity
      have hexp : Real.exp (∑ p ∈ n.primeFactors.filter (fun p : ℕ => D < p), 1 / (p : ℝ)) ≤
          Real.exp 13 := Real.exp_le_exp.2 (by linarith [sum_block_le j])
      linarith
  · have hle : ∑ p ∈ n.primeFactors.filter (fun p : ℕ => D < p), 1 / (p : ℝ) ≤ L 1 := by
      rw [hL]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        simp only [Finset.mem_filter] at hp ⊢
        refine ⟨hp.1, ?_⟩
        have : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp.1).one_lt.le
        exact_mod_cast this
      · intro p _ _
        positivity
    have hexp : Real.exp (∑ p ∈ n.primeFactors.filter (fun p : ℕ => D < p), 1 / (p : ℝ)) ≤
        Real.exp 13 := Real.exp_le_exp.2 (by linarith)
    linarith

-- Bookkeeping for the double sum.
lemma sum_split (S : Finset ℕ) (A W : ℕ → ℕ → ℝ) (c e : ℝ) (J : ℕ) (b : ℕ → ℝ)
    (T : ℕ → ℕ → ℕ → ℝ) :
    ∑ q ∈ S, ∑ r ∈ S, (A q r + c * (e * W q r + ∑ j ∈ Finset.range J, b j * T j q r)) =
      ∑ q ∈ S, ∑ r ∈ S, A q r + c * (e * ∑ q ∈ S, ∑ r ∈ S, W q r +
        ∑ j ∈ Finset.range J, b j * ∑ q ∈ S, ∑ r ∈ S, T j q r) := by
  have h3 : ∑ q ∈ S, ∑ r ∈ S, ∑ j ∈ Finset.range J, b j * T j q r =
      ∑ j ∈ Finset.range J, b j * ∑ q ∈ S, ∑ r ∈ S, T j q r := by
    calc ∑ q ∈ S, ∑ r ∈ S, ∑ j ∈ Finset.range J, b j * T j q r
        = ∑ q ∈ S, ∑ j ∈ Finset.range J, ∑ r ∈ S, b j * T j q r :=
          Finset.sum_congr rfl (fun q _ => Finset.sum_comm)
      _ = ∑ j ∈ Finset.range J, ∑ q ∈ S, ∑ r ∈ S, b j * T j q r := Finset.sum_comm
      _ = ∑ j ∈ Finset.range J, b j * ∑ q ∈ S, ∑ r ∈ S, T j q r := by
          simp only [Finset.mul_sum]
  rw [← h3]
  simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_add]

-- (1) Overlap estimate of Pollington and Vaughan (1990, pp. 195-196), Lemma 5.3 of
-- Koukoulopoulos and Maynard, on the circle: for distinct denominators q, r with values
-- a, b in [0, 1/2], the measure of the intersection of the two approximation sets is at most
-- a constant times the product of the weights times the product of (1 + 1/p) over the primes
-- p dividing q r / gcd(q, r)^2 that exceed max(r a, q b) / gcd(q, r).
def H1 : Prop :=
  ∃ C : ℝ, ∀ (q r : ℕ) (a b : ℝ), 0 < q → 0 < r → q ≠ r →
    0 ≤ a → a ≤ 1 / 2 → 0 ≤ b → b ≤ 1 / 2 →
    (volume (approxAddOrderOf UnitAddCircle q (a / q) ∩
        approxAddOrderOf UnitAddCircle r (b / r))).toReal ≤
      C * (((Nat.totient q : ℝ) * a / q) * ((Nat.totient r : ℝ) * b / r)) *
        ∏ p ∈ (q * r / (Nat.gcd q r) ^ 2).primeFactors.filter
          (fun p : ℕ => max ((r : ℝ) * a) ((q : ℝ) * b) / (Nat.gcd q r : ℝ) < p),
          (1 + 1 / (p : ℝ))

-- (2) Proposition 5.4 of Koukoulopoulos and Maynard: for values in [0, 1/2], a finite set of
-- denominators of total weight between 1 and 2 and any t at least 1, the pairs (v, w) with
-- max(w psi(v), v psi(w)) at most t gcd(v, w) and with the primes p at least t dividing
-- v w / gcd(v, w)^2 having reciprocal sum at least 10 carry total weight at most C / t.
def H2 : Prop :=
  ∃ C : ℝ, ∀ ψ : ℕ → ℝ, (∀ q, 0 ≤ ψ q ∧ ψ q ≤ 1 / 2) →
    ∀ S : Finset ℕ, (∀ q ∈ S, 0 < q) →
      1 ≤ ∑ q ∈ S, (Nat.totient q : ℝ) * ψ q / q →
      ∑ q ∈ S, (Nat.totient q : ℝ) * ψ q / q ≤ 2 →
      ∀ t : ℝ, 1 ≤ t →
        ∑ v ∈ S, ∑ w ∈ S,
          (if max ((w : ℝ) * ψ v) ((v : ℝ) * ψ w) / (Nat.gcd v w : ℝ) ≤ t ∧
              10 ≤ ∑ p ∈ (v * w / (Nat.gcd v w) ^ 2).primeFactors.filter
                (fun p : ℕ => t ≤ p), 1 / (p : ℝ)
            then ((Nat.totient v : ℝ) * ψ v / v) * ((Nat.totient w : ℝ) * ψ w / w)
            else 0) ≤ C / t

theorem main : H1 → H2 → OMA.R_Erdos999_erdos_999_R1.H2 := by
  rintro ⟨C1, h1⟩ ⟨C2, h2⟩
  refine ⟨4 + max C1 0 * (Real.exp 13 * 4 + 12 * Real.exp 10 * max C2 0), ?_⟩
  intro ψ hψ S hS hS1 hS2
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ, ∀ q, w q = (Nat.totient q : ℝ) * ψ q / q := ⟨_, fun _ => rfl⟩
  have hw0 : ∀ q, 0 ≤ w q := fun q => by
    rw [hw]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hψ q).1) (Nat.cast_nonneg _)
  have hSa : 1 ≤ ∑ q ∈ S, w q := by simpa only [hw] using hS1
  have hSb : ∑ q ∈ S, w q ≤ 2 := by simpa only [hw] using hS2
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, ∀ q ∈ S, ∀ r ∈ S, q * r / (Nat.gcd q r) ^ 2 < 4 ^ J := by
    refine ⟨(S.sup id) ^ 2 + 1, ?_⟩
    intro q hq r hr
    have hqs : q ≤ S.sup id := Finset.le_sup (f := id) hq
    have hrs : r ≤ S.sup id := Finset.le_sup (f := id) hr
    calc q * r / (Nat.gcd q r) ^ 2 ≤ q * r := Nat.div_le_self _ _
      _ ≤ S.sup id * S.sup id := Nat.mul_le_mul hqs hrs
      _ = (S.sup id) ^ 2 := (sq _).symm
      _ < (S.sup id) ^ 2 + 1 := Nat.lt_succ_self _
      _ ≤ 4 ^ ((S.sup id) ^ 2 + 1) := (Nat.lt_pow_self (by norm_num)).le
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℕ → ℕ → ℝ, ∀ j q r, T j q r =
      (if max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (Nat.gcd q r : ℝ) ≤ (4 : ℝ) ^ j ∧
          10 ≤ ∑ p ∈ (q * r / (Nat.gcd q r) ^ 2).primeFactors.filter
            (fun p : ℕ => (4 : ℝ) ^ j ≤ p), 1 / (p : ℝ)
        then w q * w r else 0) := ⟨_, fun _ _ _ => rfl⟩
  have hT0 : ∀ j q r, 0 ≤ T j q r := by
    intro j q r
    rw [hT]
    split_ifs
    · exact mul_nonneg (hw0 q) (hw0 r)
    · exact le_rfl
  have hK2 : ∀ j : ℕ, ∑ q ∈ S, ∑ r ∈ S, T j q r ≤ max C2 0 / 4 ^ j := by
    intro j
    have h := h2 ψ hψ S hS hS1 hS2 ((4 : ℝ) ^ j) (one_le_pow₀ (by norm_num))
    simp only [hT, hw]
    exact h.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  have hpt : ∀ q ∈ S, ∀ r ∈ S,
      (volume (approxAddOrderOf UnitAddCircle q (ψ q / q) ∩
        approxAddOrderOf UnitAddCircle r (ψ r / r))).toReal ≤
      (if q = r then 2 * w q else 0) + max C1 0 * (Real.exp 13 * (w q * w r) +
        ∑ j ∈ Finset.range J, (6 * Real.exp 10 * 2 ^ j) * T j q r) := by
    intro q hq r hr
    have hsumT : 0 ≤ ∑ j ∈ Finset.range J, (6 * Real.exp 10 * 2 ^ j) * T j q r :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (hT0 j q r))
    have hrest : 0 ≤ max C1 0 * (Real.exp 13 * (w q * w r) +
        ∑ j ∈ Finset.range J, (6 * Real.exp 10 * 2 ^ j) * T j q r) :=
      mul_nonneg (le_max_right _ _) (add_nonneg (mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (hw0 q) (hw0 r))) hsumT)
    by_cases hqr : q = r
    · subst hqr
      rw [Set.inter_self, if_pos rfl]
      have hq0 := hS q hq
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
      have hδ0 : 0 ≤ ψ q / q := div_nonneg (hψ q).1 hqR.le
      have hδ1 : 2 * (ψ q / q) * q ≤ 1 := by
        have : 2 * (ψ q / q) * q = 2 * ψ q := by field_simp
        rw [this]
        linarith [(hψ q).2]
      have hv : (volume (approxAddOrderOf UnitAddCircle q (ψ q / q))).toReal = 2 * w q := by
        rw [OMA.R_Erdos999_erdos_999_R1.volume_approx_eq q hq0 _ hδ0 hδ1, ENNReal.toReal_mul,
          ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by linarith), hw]
        ring
      linarith
    · rw [if_neg hqr, zero_add]
      have hK1 := h1 q r (ψ q) (ψ r) (hS q hq) (hS r hr) hqr (hψ q).1 (hψ q).2 (hψ r).1 (hψ r).2
      rw [← hw q, ← hw r] at hK1
      have hpb := prod_bound (q * r / (Nat.gcd q r) ^ 2)
        (max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (Nat.gcd q r : ℝ)) J (hJ q hq r hr)
      have hww : 0 ≤ w q * w r := mul_nonneg (hw0 q) (hw0 r)
      have hP0 : 0 ≤ ∏ p ∈ (q * r / (Nat.gcd q r) ^ 2).primeFactors.filter
          (fun p : ℕ => max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (Nat.gcd q r : ℝ) < p),
          (1 + 1 / (p : ℝ)) := Finset.prod_nonneg (fun p _ => by positivity)
      refine hK1.trans ?_
      have step1 : C1 * (w q * w r) * ∏ p ∈ (q * r / (Nat.gcd q r) ^ 2).primeFactors.filter
          (fun p : ℕ => max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (Nat.gcd q r : ℝ) < p),
          (1 + 1 / (p : ℝ)) ≤ max C1 0 * (w q * w r) * (Real.exp 13 + ∑ j ∈ Finset.range J,
            (if max ((r : ℝ) * ψ q) ((q : ℝ) * ψ r) / (Nat.gcd q r : ℝ) ≤ (4 : ℝ) ^ j ∧
              10 ≤ ∑ p ∈ (q * r / (Nat.gcd q r) ^ 2).primeFactors.filter
                (fun p : ℕ => (4 : ℝ) ^ j ≤ p), 1 / (p : ℝ)
            then 6 * Real.exp 10 * 2 ^ j else 0)) := by
        apply mul_le_mul _ hpb hP0 (mul_nonneg (le_max_right _ _) hww)
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hww
      refine step1.trans (le_of_eq ?_)
      rw [mul_assoc, mul_add, Finset.mul_sum, mul_comm (w q * w r) (Real.exp 13)]
      congr 2
      apply Finset.sum_congr rfl
      intro j _
      rw [hT]
      split_ifs <;> ring
  calc ∑ q ∈ S, ∑ r ∈ S, (volume (approxAddOrderOf UnitAddCircle q (ψ q / q) ∩
        approxAddOrderOf UnitAddCircle r (ψ r / r))).toReal
      ≤ ∑ q ∈ S, ∑ r ∈ S, ((if q = r then 2 * w q else 0) + max C1 0 *
          (Real.exp 13 * (w q * w r) +
            ∑ j ∈ Finset.range J, (6 * Real.exp 10 * 2 ^ j) * T j q r)) :=
        Finset.sum_le_sum (fun q hq => Finset.sum_le_sum (fun r hr => hpt q hq r hr))
    _ = ∑ q ∈ S, ∑ r ∈ S, (if q = r then 2 * w q else 0) + max C1 0 *
          (Real.exp 13 * ∑ q ∈ S, ∑ r ∈ S, w q * w r +
            ∑ j ∈ Finset.range J, (6 * Real.exp 10 * 2 ^ j) * ∑ q ∈ S, ∑ r ∈ S, T j q r) :=
        sum_split S (fun q r => if q = r then 2 * w q else 0) (fun q r => w q * w r) _ _ J
          (fun j => 6 * Real.exp 10 * 2 ^ j) T
    _ ≤ 4 + max C1 0 * (Real.exp 13 * 4 + 12 * Real.exp 10 * max C2 0) := by
        have hA : ∑ q ∈ S, ∑ r ∈ S, (if q = r then 2 * w q else 0) ≤ 4 := by
          have : ∑ q ∈ S, ∑ r ∈ S, (if q = r then 2 * w q else 0) = ∑ q ∈ S, 2 * w q :=
            Finset.sum_congr rfl (fun q hq => by rw [Finset.sum_ite_eq, if_pos hq])
          rw [this, ← Finset.mul_sum]
          linarith
        have hB : ∑ q ∈ S, ∑ r ∈ S, w q * w r ≤ 4 := by
          rw [← Finset.sum_mul_sum]
          nlinarith [Finset.sum_nonneg (fun q (_ : q ∈ S) => hw0 q)]
        have hC : ∑ j ∈ Finset.range J, (6 * Real.exp 10 * 2 ^ j) * ∑ q ∈ S, ∑ r ∈ S, T j q r ≤
            12 * Real.exp 10 * max C2 0 := by
          have hterm : ∀ j ∈ Finset.range J,
              (6 * Real.exp 10 * 2 ^ j) * ∑ q ∈ S, ∑ r ∈ S, T j q r ≤
                6 * Real.exp 10 * max C2 0 * (1 / 2) ^ j := by
            intro j _
            have h4 : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by
              rw [← mul_pow]
              norm_num
            calc (6 * Real.exp 10 * 2 ^ j) * ∑ q ∈ S, ∑ r ∈ S, T j q r
                ≤ (6 * Real.exp 10 * 2 ^ j) * (max C2 0 / 4 ^ j) :=
                  mul_le_mul_of_nonneg_left (hK2 j) (by positivity)
              _ = 6 * Real.exp 10 * max C2 0 * (1 / 2) ^ j := by
                  rw [h4, one_div, inv_pow]
                  field_simp
          refine (Finset.sum_le_sum hterm).trans ?_
          rw [← Finset.mul_sum]
          have hg := sum_geometric_two_le J
          have hc : 0 ≤ 6 * Real.exp 10 * max C2 0 :=
            mul_nonneg (by positivity) (le_max_right _ _)
          nlinarith
        have hc1 : 0 ≤ max C1 0 := le_max_right _ _
        have hin : Real.exp 13 * ∑ q ∈ S, ∑ r ∈ S, w q * w r +
            ∑ j ∈ Finset.range J, (6 * Real.exp 10 * 2 ^ j) * ∑ q ∈ S, ∑ r ∈ S, T j q r ≤
            Real.exp 13 * 4 + 12 * Real.exp 10 * max C2 0 :=
          add_le_add (mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le) hC
        exact add_le_add hA (mul_le_mul_of_nonneg_left hin hc1)

end OMA.R_Erdos999_erdos_999_R1_H2_R1
