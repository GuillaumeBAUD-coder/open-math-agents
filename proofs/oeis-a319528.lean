import OMAStatements.S_oeis_a319528

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: write n = 7^k * m with 7 ∤ m. sigma is multiplicative, sigma(7) = 8 and
-- sigma(7^(k+1)) = 7 * sigma(7^k) + 1. If k = 0 the identity holds; if k ≥ 1 it would force
-- sigma(7^k) = 1, but sigma(7^k) ≥ 8.

namespace OMA.Sol_oeis_a319528
open ArithmeticFunction

lemma sig_pow (k : ℕ) : sigma 1 (7 ^ (k + 1)) = 7 * sigma 1 (7 ^ k) + 1 := by
  rw [sigma_one_apply_prime_pow (by norm_num), sigma_one_apply_prime_pow (by norm_num),
    Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm]

lemma sig_pow_ge (k : ℕ) (hk : 1 ≤ k) : 8 ≤ sigma 1 (7 ^ k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [sig_pow]
  have : 1 ≤ sigma 1 (7 ^ j) := by
    rw [sigma_one_apply_prime_pow (by norm_num), Finset.sum_range_succ']; simp
  omega

end OMA.Sol_oeis_a319528

open ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a319528.main := by
  intro n hn
  obtain ⟨k, m, hm7, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) 7 (by norm_num)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hn
  have hcop : ∀ j, Nat.Coprime (7 ^ j) m := fun j =>
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hm7)
  have e1 : 7 * (7 ^ k * m) = 7 ^ (k + 1) * m := by ring
  rw [e1, isMultiplicative_sigma.map_mul_of_coprime (hcop _),
    isMultiplicative_sigma.map_mul_of_coprime (hcop _), OMA.Sol_oeis_a319528.sig_pow]
  have hs : 0 < sigma 1 m := by
    rw [sigma_one_apply]; exact Finset.sum_pos (fun i hi => Nat.pos_of_mem_divisors hi)
      ⟨1, Nat.one_mem_divisors.mpr hm0⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hm7
  · have h8 := OMA.Sol_oeis_a319528.sig_pow_ge k hk
    have hd : 7 ∣ 7 ^ k * m := Dvd.dvd.mul_right (dvd_pow_self 7 (by omega)) m
    simp only [hd, not_true_eq_false, iff_false]
    intro h
    have : 7 * sigma 1 (7 ^ k) + 1 = 8 * sigma 1 (7 ^ k) := by
      have := h; rw [← mul_assoc] at this
      exact Nat.eq_of_mul_eq_mul_right hs this
    omega
