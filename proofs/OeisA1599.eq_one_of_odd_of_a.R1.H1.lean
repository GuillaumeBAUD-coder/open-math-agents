import OMAReductions.R_OeisA1599_eq_one_of_odd_of_a_R1
import Mathlib

-- Step OeisA1599.eq_one_of_odd_of_a.R1.H1: hypothesis H1 of reduction OeisA1599.eq_one_of_odd_of_a.R1
-- Credit: @ivillar. Ore (1948): for n = p^k the divisor sum 1 + p + ... + p^k is coprime to p^k, so it would have to divide k + 1, but it exceeds p^k + 1 > k + 1.

/-! Step OeisA1599.eq_one_of_odd_of_a.R1.H1. -/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace P8A1599

theorem no_prime_pow : ∀ n : ℕ, IsPrimePow n → ¬ OeisA1599.A n := by
  intro n hn hA
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hn
  obtain ⟨_, hdvd⟩ := hA
  rw [sigma_zero_apply_prime_pow hp, sigma_one_apply_prime_pow hp] at hdvd
  have hS : ∑ i ∈ Finset.range (k + 1), p ^ i = 1 + p * ∑ i ∈ Finset.range k, p ^ i := by
    rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
    simp [pow_succ, mul_comm]
  have hndvd : ¬ p ∣ ∑ i ∈ Finset.range (k + 1), p ^ i := by
    rw [hS]
    intro h
    have h1 : p ∣ 1 := (Nat.dvd_add_left (dvd_mul_right p _)).mp h
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hcop : Nat.Coprime (∑ i ∈ Finset.range (k + 1), p ^ i) (p ^ k) :=
    Nat.Coprime.pow_right k ((hp.coprime_iff_not_dvd).mpr hndvd).symm
  have h2 : ∑ i ∈ Finset.range (k + 1), p ^ i ∣ k + 1 := hcop.dvd_of_dvd_mul_left hdvd
  have h3 : p ^ k + 1 ≤ ∑ i ∈ Finset.range (k + 1), p ^ i := by
    rw [Finset.sum_range_succ]
    have : p ^ 0 ≤ ∑ i ∈ Finset.range k, p ^ i :=
      Finset.single_le_sum (f := fun i => p ^ i) (fun i _ => Nat.zero_le _)
        (Finset.mem_range.mpr hk)
    simp only [pow_zero] at this
    omega
  have h4 : k < p ^ k := Nat.lt_pow_self hp.one_lt
  have h5 := Nat.le_of_dvd (by omega) h2
  omega

end P8A1599

theorem OMA.solution : OMA.R_OeisA1599_eq_one_of_odd_of_a_R1.H1 :=
  P8A1599.no_prime_pow
