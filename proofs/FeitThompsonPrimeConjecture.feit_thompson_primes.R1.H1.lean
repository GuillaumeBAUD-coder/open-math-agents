import OMAReductions.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1

-- Step FeitThompsonPrimeConjecture.feit_thompson_primes.R1.H1: hypothesis H1 of reduction FeitThompsonPrimeConjecture.feit_thompson_primes.R1
-- Credit: @smurali12
-- H1 := ∀ (p q : ℕ), p.Prime → q.Prime → p < q → q % p = 1 →     ¬ (q ^ p - 1) / (q - 1) ∣ (p ^ q - 1) / (p - 1)  /-- The case q % p ≠ 1, p % 4 = 3, q % 4 = 1: excluded by Jacobi reciprocity. -/

private lemma geom_sum_mul_sub_one (a n : ℕ) (ha : 1 ≤ a) :
    (∑ i ∈ Finset.range n, a ^ i) * (a - 1) = a ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_mul, ih, pow_succ, Nat.mul_sub_left_distrib, mul_one]
    have h1 : 1 ≤ a ^ n := Nat.one_le_pow n a ha
    have h2 : a ^ n ≤ a ^ n * a := Nat.le_mul_of_pos_right _ ha
    omega

private lemma div_sub_one_eq_geom_sum (a n : ℕ) (ha : 2 ≤ a) :
    (a ^ n - 1) / (a - 1) = ∑ i ∈ Finset.range n, a ^ i := by
  rw [← geom_sum_mul_sub_one a n (by omega), Nat.mul_div_cancel _ (by omega)]

theorem OMA.solution : OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1.H1 := by
  intro p q hp hq _hpq hmod hdiv
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : p ∣ (q ^ p - 1) / (q - 1) := by
    rw [div_sub_one_eq_geom_sum q p hq.two_le]
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    have hq1 : (q : ZMod p) = 1 := by
      rw [← ZMod.natCast_mod q p, hmod, Nat.cast_one]
    simp [hq1]
  have h2 : ¬ p ∣ (p ^ q - 1) / (p - 1) := by
    rw [div_sub_one_eq_geom_sum p q hp.two_le]
    have hq_pos : 1 ≤ q := hq.one_lt.le
    rw [show q = (q - 1) + 1 by omega, Finset.sum_range_succ']
    have hdvd_sum : p ∣ ∑ i ∈ Finset.range (q - 1), p ^ (i + 1) := by
      apply Finset.dvd_sum
      intro i _
      rw [pow_succ]
      exact dvd_mul_left p (p ^ i)
    intro h
    have h1' : p ∣ 1 := (Nat.dvd_add_right hdvd_sum).mp (by simpa using h)
    exact hp.not_dvd_one h1'
  exact h2 (dvd_trans h1 hdiv)

