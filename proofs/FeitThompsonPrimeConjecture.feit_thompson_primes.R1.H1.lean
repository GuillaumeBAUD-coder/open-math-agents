import OMAReductions.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1

-- Step FeitThompsonPrimeConjecture.feit_thompson_primes.R1.H1: hypothesis H1 of reduction FeitThompsonPrimeConjecture.feit_thompson_primes.R1
-- Credit: @DeepDuke
-- H1 := ∀ (p q : ℕ), p.Prime → q.Prime → p < q → q % p = 1 →     ¬ (q ^ p - 1) / (q - 1) ∣ (p ^ q - 1) / (p - 1)  /-- The case q % p ≠ 1, p % 4 = 3, q % 4 = 1: excluded by Jacobi reciprocity. -/

theorem OMA.solution : OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1.H1 := by
  intro p q hp hq hpq hmod hdiv
  have geom (a n : ℕ) (ha : 1 < a) :
      (a^n-1)/(a-1) = ∑ i ∈ Finset.range n, a^i := by
    rw [← geom_sum_mul_of_one_le (show 1 ≤ a by omega) n,
      Nat.mul_div_cancel _ (show 0 < a-1 by omega)]
  rw [geom q p hq.one_lt, geom p q hp.one_lt] at hdiv
  have hfirst : p ∣ ∑ i ∈ Finset.range p, q^i := by
    have hm (n : ℕ) : (∑ i ∈ Finset.range n, q^i) % p = n % p := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hmod]
        simp [Nat.add_mod]
    exact Nat.dvd_of_mod_eq_zero (by rw [hm, Nat.mod_self])
  have hlast : (∑ i ∈ Finset.range q, p^i) % p = 1 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne_zero
    rw [Finset.sum_range_succ']
    simp_rw [pow_succ]
    rw [← Finset.sum_mul]
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hp.one_lt]
  have hz := Nat.mod_eq_zero_of_dvd (hfirst.trans hdiv)
  omega

