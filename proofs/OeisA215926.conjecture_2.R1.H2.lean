import OMAReductions.R_OeisA215926_conjecture_2_R1

-- Step OeisA215926.conjecture_2.R1.H2: hypothesis H2 of reduction OeisA215926.conjecture_2.R1
-- Credit: @DeepDuke
-- H2 := ∀ j q : ℕ, q.Prime → 2 < q → q < 2 * 2 ^ j →     (2 ^ j * q).Perfect ∨ (2 ^ j * q).Abundant  private theorem nond {n : ℕ} (hn : 0 < n) :     n.Perfect ∨ n.Abundant ↔ 2 * n ≤ ∑ d ∈ n.divisors, d := by   rw [Nat.perfect_iff_sum_divisors_eq_two_mul hn, Nat.abundant_iff_sum_divisors]   omega  private theorem liftNondef {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (hd : u ∣ v)     (h : u.Perfect ∨ u.Abundant) : v.Perfect ∨ v.Abundant := by   have hi : ∀ t : ℕ, 0 < t → (2 ≤ t.abundancyIndex ↔ t.Perfect ∨ t.Abundant) := by     intro t ht     rw [nond ht, Nat.abundancyIndex, le_div_iff₀ (by positivity)]     norm_cast   exact (hi v hv).mp (((hi u hu).mpr h).trans (Nat.abundancyIndex_le_of_dvd hv.ne' hd))  private theorem obstruction {k p : ℕ} (hp : p.Prime) (hlt : k < p)     (hd : k.Deficient) (hprod : (k*p).Perfect ∨ (k*p).Abundant) :     (∑ d ∈ k.divisors, d) + 1 = 2*k ∧ p+1 ≤ 2*k := by   have hk := hd.pos   have h := (nond (Nat.mul_pos hk hp.pos)).mp hprod   rw [(Nat.coprime_of_lt_prime hk.ne' hlt hp).symm.sum_divisors_mul, hp.divisors] at h   simp [Ne.symm hp.ne_one] at h   have hlt' : (∑ d ∈ k.divisors, d) < 2*k := by     rw [Nat.sum_divisors_eq_sum_properDivisors_add_self]     unfold Nat.Deficient at hd     omega   have he : (∑ d ∈ k.divisors, d) + 1 = 2*k := by     by_contra hn     have hh : (∑ d ∈ k.divisors, d) + 2 ≤ 2*k := by omega     nlinarith [Nat.mul_le_mul_right (1+p) hh]   exact ⟨he, by nlinarith [congrArg (· * p) he]⟩

theorem OMA.solution : OMA.R_OeisA215926_conjecture_2_R1.H2 := by
  intro j q hq hqtwo hbound
  have hpos : 0 < 2 ^ j * q := Nat.mul_pos (by positivity) hq.pos
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, Nat.abundant_iff_sum_divisors]
  have hc : Nat.Coprime (2 ^ j) q := by
    apply Nat.Coprime.pow_left
    exact (Nat.coprime_primes Nat.prime_two hq).mpr (by omega)
  have hs : (∑ d ∈ (2 ^ j).divisors, d) + 1 = 2 * 2 ^ j := by
    rw [Nat.sum_divisors_prime_pow Nat.prime_two]
    clear hbound hpos hc
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith
  have he : (∑ d ∈ (2 ^ j * q).divisors, d) =
      (∑ d ∈ (2 ^ j).divisors, d) * (1 + q) := by
    rw [hc.sum_divisors_mul, hq.divisors]
    simp [Ne.symm hq.ne_one]
  rw [he]
  have : 2 * (2 ^ j * q) ≤ (∑ d ∈ (2 ^ j).divisors, d) * (1 + q) := by
    nlinarith
  omega

