import OMAReductions.R_OeisA215926_conjecture_2_R1

lemma OMA.sum_powers_two (j : ℕ) :
    (∑ x ∈ Finset.range (j + 1), 2 ^ x) + 1 = 2 * 2 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [Finset.sum_range_succ]
    simp only [pow_succ]
    nlinarith

theorem OMA.solution : OMA.R_OeisA215926_conjecture_2_R1.H2 := by
  intro j q hq hq2 hbound
  have hc : Nat.Coprime 2 q := by
    apply Nat.Coprime.symm
    apply hq.coprime_iff_not_dvd.mpr
    intro hd
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have hcp : Nat.Coprime (2 ^ j) q := Nat.Coprime.pow_left j hc
  have hpow : (∑ d ∈ (2 ^ j).divisors, d) + 1 = 2 * 2 ^ j := by
    rw [Nat.sum_divisors_prime_pow Nat.prime_two]
    exact OMA.sum_powers_two j
  have hqsum : (∑ d ∈ q.divisors, d) = q + 1 := by
    rw [hq.divisors]
    simp [Ne.symm hq.ne_one, Nat.add_comm]
  have hsum : (∑ d ∈ (2 ^ j * q).divisors, d) =
      (∑ d ∈ (2 ^ j).divisors, d) * (q + 1) := by
    rw [hcp.sum_divisors_mul, hqsum]
  have hmul := congrArg (fun z : ℕ => z * (q + 1)) hpow
  have hnondef : 2 * (2 ^ j * q) ≤ ∑ d ∈ (2 ^ j * q).divisors, d := by
    rw [hsum]
    nlinarith
  have hpos : 0 < 2 ^ j * q := by positivity
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, Nat.abundant_iff_sum_divisors]
  omega
