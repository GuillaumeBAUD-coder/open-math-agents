import OMAReductions.R_oeis_a007691_R1
import Mathlib.NumberTheory.LucasPrimality

/-!
# Proof of `oeis-a007691.R1.H1`

Proves Euclid's theorem (Elements IX.36): if `2 ^ (k + 1) - 1` is prime, then
`2 ^ k * (2 ^ (k + 1) - 1)` is a perfect number (`Nat.Perfect`).

Directly applies `Nat.perfect_two_pow_mul_mersenne_of_prime` (or the multiplicative divisor-sum
identity `σ 1 (2 ^ k * p) = (2 ^ (k + 1) - 1) * (p + 1) = 2 * (2 ^ k * p)`).
-/

theorem OMA.solution : OMA.R_oeis_a007691_R1.H1 := by
  intro k hp
  have hpos : 0 < 2 ^ k * (2 ^ (k + 1) - 1) := Nat.mul_pos (pow_pos (by decide) k) hp.pos
  have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have hodd : Odd (2 ^ (k + 1) - 1) := by
    have h2 : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (Nat.succ_ne_zero k)
    obtain ⟨t, ht⟩ := h2
    have ht1 : 1 ≤ t := by omega
    refine ⟨t - 1, ?_⟩
    omega
  have hcop : (2 ^ k).Coprime (2 ^ (k + 1) - 1) :=
    (Nat.coprime_two_left.mpr hodd).pow_left k
  have hsig2 : ArithmeticFunction.sigma 1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
    have hgeom : ∀ n : ℕ, (∑ i ∈ Finset.range n, 2 ^ i) + 1 = 2 ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega
    have := hgeom (k + 1)
    omega
  have hsigp : ArithmeticFunction.sigma 1 (2 ^ (k + 1) - 1) = 2 ^ (k + 1) := by
    rw [ArithmeticFunction.sigma_one_apply, hp.divisors, Finset.sum_pair hp.ne_one.symm]
    omega
  have hsig_mul : ArithmeticFunction.sigma 1 (2 ^ k * (2 ^ (k + 1) - 1)) =
      2 * (2 ^ k * (2 ^ (k + 1) - 1)) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsig2, hsigp]
    rw [pow_succ']
    ring
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos]
  rw [← ArithmeticFunction.sigma_one_apply]
  exact hsig_mul
