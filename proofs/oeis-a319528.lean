import OMAStatements.S_oeis_a319528

-- Problem: A319528, sigma(7n) = 8 sigma(n) exactly when 7 does not divide n.
-- Credit: @bnb9001

namespace OMA_A319528_Proof

lemma geom7 (e : ℕ) : ∑ k ∈ Finset.range (e + 2), 7 ^ k = 7 * ∑ k ∈ Finset.range (e + 1), 7 ^ k + 1 := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm]

lemma geom_pos (e : ℕ) : 1 ≤ ∑ k ∈ Finset.range (e + 1), 7 ^ k := by
  rw [Finset.sum_range_succ']
  simp

end OMA_A319528_Proof

open ArithmeticFunction OMA_A319528_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a319528.main := by
  intro n hn
  have hp : Nat.Prime 7 := by norm_num
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) 7 (by norm_num)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hc : ∀ k, Nat.Coprime (7 ^ k) m := fun k =>
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  have hs : 0 < ArithmeticFunction.sigma 1 m := sigma_pos 1 m hm0
  rw [← mul_assoc, ← pow_succ', isMultiplicative_sigma.map_mul_of_coprime (hc (e + 1)),
    isMultiplicative_sigma.map_mul_of_coprime (hc e), sigma_one_apply_prime_pow hp,
    sigma_one_apply_prime_pow hp, geom7]
  generalize hS : ∑ k ∈ Finset.range (e + 1), 7 ^ k = S
  have hS1 : 1 ≤ S := hS ▸ geom_pos e
  rcases e with _ | e
  · simp at hS
    subst hS
    simp [hm]
  · have hS8 : 8 ≤ S := by
      rw [← hS, geom7]
      have := geom_pos e
      omega
    have hdvd : 7 ∣ 7 ^ (e + 1) * m := Dvd.dvd.mul_right (dvd_pow_self 7 (by omega)) m
    simp only [hdvd, not_true_eq_false, iff_false]
    intro h
    have : (7 * S + 1) * ArithmeticFunction.sigma 1 m < 8 * (S * ArithmeticFunction.sigma 1 m) := by nlinarith
    omega
