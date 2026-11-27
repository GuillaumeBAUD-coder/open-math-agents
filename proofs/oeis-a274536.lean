import OMAStatements.S_oeis_a274536

namespace OMA.S_oeis_a274536

lemma geom_succ (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1 + 1), 5 ^ j = 5 * ∑ j ∈ Finset.range (k + 1), 5 ^ j + 1 := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm]

lemma sig_pow (k : ℕ) :
    ArithmeticFunction.sigma 1 (5 ^ k) = ∑ j ∈ Finset.range (k + 1), 5 ^ j := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_five]

end OMA.S_oeis_a274536

open OMA.S_oeis_a274536 in
theorem OMA.solution : type_of% @OMA.S_oeis_a274536.main := by
  intro n hn
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 5 (by norm_num)
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hn
    · exact h
  have hcop : ∀ j, Nat.Coprime (5 ^ j) m := fun j =>
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hm)
  have h5 : 5 * (5 ^ k * m) = 5 ^ (k + 1) * m := by ring
  unfold a
  rw [h5, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop k),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop (k + 1)),
    sig_pow, sig_pow, geom_succ]
  have hsm : 0 < ArithmeticFunction.sigma 1 m := ArithmeticFunction.sigma_pos 1 m hm0.ne'
  set T := ∑ j ∈ Finset.range (k + 1), 5 ^ j with hT
  rw [show 6 * (T * ArithmeticFunction.sigma 1 m) = (5 * T + 1) * ArithmeticFunction.sigma 1 m
      ↔ T = 1 by
    constructor
    · intro h
      have : 6 * T = 5 * T + 1 := by
        apply Nat.eq_of_mul_eq_mul_right hsm
        rw [← h]; ring
      omega
    · intro h; rw [h]; ring]
  constructor
  · intro hT1 hdvd
    rcases k with _ | k
    · exact hm (by simpa using hdvd)
    · rw [hT, geom_succ] at hT1
      have : 0 < ∑ j ∈ Finset.range (k + 1), 5 ^ j :=
        Finset.sum_pos (fun j _ => by positivity) (by simp)
      omega
  · intro hnd
    rcases k with _ | k
    · simp [hT]
    · exact absurd (Dvd.dvd.mul_right (dvd_pow_self 5 (Nat.succ_ne_zero k)) m) hnd
