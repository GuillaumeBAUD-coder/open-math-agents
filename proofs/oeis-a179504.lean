import OMAStatements.S_oeis_a179504

open ArithmeticFunction in
lemma OMA.S_oeis_a179504.sigma_two_pow_cast (k i : ℕ) :
    ((ArithmeticFunction.sigma k (2 ^ i) : ℕ) : ℚ) = ∑ j ∈ Finset.range (i + 1), ((2 : ℚ) ^ k) ^ j := by
  rw [sigma_apply_prime_pow Nat.prime_two]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pow_mul, mul_comm]

open ArithmeticFunction OMA.S_oeis_a179504 in
theorem OMA.solution : type_of% @OMA.S_oeis_a179504.main := by
  intro n hn
  obtain ⟨v, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hcop : ∀ i, Nat.Coprime (2 ^ i) m := fun i =>
    Nat.Coprime.pow_left i (Nat.coprime_two_left.mpr hm)
  have hv : padicValNat 2 n = v := by
    rw [hnm, padicValNat.mul (by positivity) (by rintro rfl; simp at hm),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by
        rintro h; exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h)), add_zero]
  have h2n : 2 * n = 2 ^ (v + 1) * m := by rw [hnm, pow_succ]; ring
  have hA : (a n : ℚ) = (ArithmeticFunction.sigma n (2 ^ (v + 1)) : ℚ) * (ArithmeticFunction.sigma n m : ℚ) := by
    unfold a
    rw [if_neg hn.ne', h2n, isMultiplicative_sigma.map_mul_of_coprime (hcop _)]
    push_cast; ring
  have hB : (ArithmeticFunction.sigma n n : ℚ) = (ArithmeticFunction.sigma n (2 ^ v) : ℚ) * (ArithmeticFunction.sigma n m : ℚ) := by
    rw [show (ArithmeticFunction.sigma n) n = ArithmeticFunction.sigma n (2 ^ v * m) from
      congrArg _ hnm, isMultiplicative_sigma.map_mul_of_coprime (hcop _)]
    push_cast; ring
  rw [hA, hB, hv, sigma_two_pow_cast, sigma_two_pow_cast]
  set x : ℚ := (2 : ℚ) ^ n with hx
  have hx1 : 1 < x := one_lt_pow₀ (by norm_num) hn.ne'
  have hpow : (2 : ℚ) ^ (n * (v + 1)) = x ^ (v + 1) := by rw [pow_mul]
  rw [hpow]
  have hden : x ^ (v + 1) - 1 ≠ 0 := by
    have : 1 < x ^ (v + 1) := one_lt_pow₀ hx1 (Nat.succ_ne_zero v)
    linarith
  have hgeom : (∑ j ∈ Finset.range (v + 1), x ^ j) * (x - 1) = x ^ (v + 1) - 1 :=
    geom_sum_mul x (v + 1)
  have key : (∑ j ∈ Finset.range (v + 1), x ^ j) * ((x - 1) / (x ^ (v + 1) - 1)) = 1 := by
    rw [← mul_div_assoc, hgeom, div_self hden]
  rw [geom_sum_succ]
  linear_combination (-(ArithmeticFunction.sigma n m : ℚ)) * key
