import OMAReductions.R_OeisA215926_conjecture_2_R1
import Mathlib

-- Step OeisA215926.conjecture_2.R1.H2: hypothesis H2 of reduction OeisA215926.conjecture_2.R1
-- Credit: @ivillar
-- H2 := for an odd prime q < 2^(j+1), the number 2^j * q is perfect or abundant.
-- Proof: sigma is multiplicative, so the divisor sum of 2^j * q is (2^(j+1) - 1) * (q + 1), and
-- (2^(j+1) - 1) * (q + 1) >= 2^(j+1) * q is equivalent to q <= 2^(j+1) - 1.

open ArithmeticFunction

lemma OMA.A215926.geom (j : ℕ) : (∑ i ∈ Finset.range (j + 1), 2 ^ i) + 1 = 2 * 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

lemma OMA.A215926.sum_div (j q : ℕ) (hq : q.Prime) (h2 : 2 < q) :
    ∑ d ∈ (2 ^ j * q).divisors, d = (∑ i ∈ Finset.range (j + 1), 2 ^ i) * (q + 1) := by
  have hcop : Nat.Coprime (2 ^ j) q :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega))
  have hm := (isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop
  simp only [sigma_one_apply] at hm
  rw [hm, Nat.sum_divisors_prime_pow Nat.prime_two, hq.sum_divisors]

theorem OMA.solution : OMA.R_OeisA215926_conjecture_2_R1.H2 := by
  unfold OMA.R_OeisA215926_conjecture_2_R1.H2
  intro j q hq h2 hlt
  have hn : 0 < 2 ^ j * q := by positivity
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hn, Nat.abundant_iff_sum_divisors,
    OMA.A215926.sum_div j q hq h2]
  set S := ∑ i ∈ Finset.range (j + 1), 2 ^ i with hSdef
  have hS : S + 1 = 2 * 2 ^ j := OMA.A215926.geom j
  have hqS : q ≤ S := by omega
  have key : 2 * (2 ^ j * q) ≤ S * (q + 1) := by
    calc 2 * (2 ^ j * q) = (S + 1) * q := by rw [hS]; ring
      _ = S * q + q := by ring
      _ ≤ S * q + S := by omega
      _ = S * (q + 1) := by ring
  rcases Nat.lt_or_eq_of_le key with h | h
  · exact Or.inr h
  · exact Or.inl h.symm
