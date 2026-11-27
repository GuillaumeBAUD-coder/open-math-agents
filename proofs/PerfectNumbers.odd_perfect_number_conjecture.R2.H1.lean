import OMAReductions.R_PerfectNumbers_odd_perfect_number_conjecture_R2
import Mathlib

-- Step PerfectNumbers.odd_perfect_number_conjecture.R2.H1: hypothesis H1 of reduction PerfectNumbers.odd_perfect_number_conjecture.R2
-- Credit: @ivillar. Sylvester (1888): no odd perfect number is divisible by 105. If p = 3 or 7 divides
-- an odd perfect n exactly once then sigma(p) = p + 1 (4 or 8) divides sigma(n) = 2n, impossible for odd n;
-- so 3^2 * 5 * 7^2 divides n and sigma(n)/n >= (13/9)(6/5)(57/49) = 4446/2205 > 2.

/-! Sylvester: an odd perfect number is not divisible by 105. -/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace P8Sylvester105

lemma sigma_eq_prod (n : ℕ) (hn : n ≠ 0) :
    σ 1 n = ∏ p ∈ n.primeFactors, σ 1 (p ^ n.factorization p) := by
  rw [isMultiplicative_sigma.multiplicative_factorization (σ 1) hn]
  rfl

lemma n_eq_prod (n : ℕ) (hn : n ≠ 0) :
    n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rfl

lemma pow_le_sigma (p a : ℕ) (hp : p.Prime) : p ^ a ≤ σ 1 (p ^ a) := by
  rw [sigma_one_apply_prime_pow hp]
  exact Finset.single_le_sum (f := fun i => p ^ i) (fun i _ => Nat.zero_le _)
    (Finset.self_mem_range_succ a)

lemma sigma_lower2 (p k : ℕ) (hp : p.Prime) :
    p ^ k * (p ^ 2 + p + 1) ≤ σ 1 (p ^ (k + 2)) := by
  rw [sigma_one_apply_prime_pow hp]
  have hs : ∑ i ∈ Finset.range (k + 2 + 1), p ^ i =
      ∑ i ∈ Finset.range (k + 1), p ^ i + p ^ (k + 1) + p ^ (k + 2) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
  rw [hs]
  have : p ^ k ≤ ∑ i ∈ Finset.range (k + 1), p ^ i :=
    Finset.single_le_sum (f := fun i => p ^ i) (fun i _ => Nat.zero_le _)
      (Finset.self_mem_range_succ k)
  have e : p ^ k * (p ^ 2 + p + 1) = p ^ k + p ^ (k + 1) + p ^ (k + 2) := by ring
  rw [e]
  omega

lemma sigma_lower1 (p k : ℕ) (hp : p.Prime) :
    p ^ k * (p + 1) ≤ σ 1 (p ^ (k + 1)) := by
  rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]
  have : p ^ k ≤ ∑ i ∈ Finset.range (k + 1), p ^ i :=
    Finset.single_le_sum (f := fun i => p ^ i) (fun i _ => Nat.zero_le _)
      (Finset.self_mem_range_succ k)
  have e : p ^ k * (p + 1) = p ^ k + p ^ (k + 1) := by ring
  rw [e]
  omega

theorem sylvester_105 : OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R2.H1 := by
  intro n hperf hodd h105
  have hn0 : n ≠ 0 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hodd
    omega
  have hσ : σ 1 n = 2 * n := by
    rw [sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul (Nat.pos_of_ne_zero hn0)).mp hperf
  have hf := sigma_eq_prod n hn0
  have hg := n_eq_prod n hn0
  have hmem : ∀ p, p.Prime → p ∣ 105 → p ∈ n.primeFactors := fun p hp hd =>
    Nat.mem_primeFactors.mpr ⟨hp, dvd_trans hd h105, hn0⟩
  have h3 := hmem 3 Nat.prime_three (by norm_num)
  have h5 := hmem 5 Nat.prime_five (by norm_num)
  have h7 := hmem 7 (by norm_num) (by norm_num)
  have hdvd : ∀ p ∈ n.primeFactors, σ 1 (p ^ n.factorization p) ∣ 2 * n := by
    intro p hp
    rw [← hσ, hf]
    exact Finset.dvd_prod_of_mem (fun p => σ 1 (p ^ n.factorization p)) hp
  have hnot4 : ¬ 4 ∣ 2 * n := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hpos : ∀ p ∈ n.primeFactors, 0 < n.factorization p := fun p hp =>
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by rwa [Nat.support_factorization]))
  -- exponents of 3 and 7 are not 1
  have e3 : n.factorization 3 ≠ 1 := by
    intro h
    have := hdvd 3 h3
    have h4 : σ 1 3 = 4 := by
      have := sigma_one_apply_prime_pow (i := 1) Nat.prime_three
      simpa [Finset.sum_range_succ] using this
    rw [h, pow_one, h4] at this
    exact hnot4 (dvd_trans (by decide) this)
  have e7 : n.factorization 7 ≠ 1 := by
    intro h
    have := hdvd 7 h7
    have h8 : σ 1 7 = 8 := by
      have := sigma_one_apply_prime_pow (i := 1) (show Nat.Prime 7 by norm_num)
      simpa [Finset.sum_range_succ] using this
    rw [h, pow_one, h8] at this
    exact hnot4 (dvd_trans (by decide) this)
  obtain ⟨k3, hk3⟩ : ∃ k, n.factorization 3 = k + 2 :=
    ⟨n.factorization 3 - 2, by have := hpos 3 h3; omega⟩
  obtain ⟨k5, hk5⟩ : ∃ k, n.factorization 5 = k + 1 :=
    ⟨n.factorization 5 - 1, by have := hpos 5 h5; omega⟩
  obtain ⟨k7, hk7⟩ : ∃ k, n.factorization 7 = k + 2 :=
    ⟨n.factorization 7 - 2, by have := hpos 7 h7; omega⟩
  have hS : ({3, 5, 7} : Finset ℕ) ⊆ n.primeFactors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  set Rg := ∏ p ∈ n.primeFactors \ {3, 5, 7}, p ^ n.factorization p with hRg
  set Rf := ∏ p ∈ n.primeFactors \ {3, 5, 7}, σ 1 (p ^ n.factorization p) with hRf
  have hRle : Rg ≤ Rf := Finset.prod_le_prod' (fun p hp =>
    pow_le_sigma p _ (Nat.prime_of_mem_primeFactors (Finset.sdiff_subset hp)))
  have hRpos : 0 < Rg := Finset.prod_pos (fun p hp =>
    pow_pos (Nat.prime_of_mem_primeFactors (Finset.sdiff_subset hp)).pos _)
  have hprod3 : ∀ F : ℕ → ℕ, ∏ p ∈ ({3, 5, 7} : Finset ℕ), F p = F 3 * (F 5 * F 7) := by
    intro F
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  have E1 : 2 * n = 4410 * (Rg * 3 ^ k3 * 5 ^ k5 * 7 ^ k7) := by
    conv_lhs => rw [hg, ← Finset.prod_sdiff hS, hprod3]
    rw [hk3, hk5, hk7]
    ring
  have l3 := sigma_lower2 3 k3 Nat.prime_three
  have l5 := sigma_lower1 5 k5 Nat.prime_five
  have l7 := sigma_lower2 7 k7 (by norm_num)
  have E2 : 4446 * (Rg * 3 ^ k3 * 5 ^ k5 * 7 ^ k7) ≤ σ 1 n := by
    rw [hf, ← Finset.prod_sdiff hS, hprod3, hk3, hk5, hk7]
    calc 4446 * (Rg * 3 ^ k3 * 5 ^ k5 * 7 ^ k7)
        = Rg * ((3 ^ k3 * (3 ^ 2 + 3 + 1)) * ((5 ^ k5 * (5 + 1)) * (7 ^ k7 * (7 ^ 2 + 7 + 1)))) := by
          ring
      _ ≤ Rf * (σ 1 (3 ^ (k3 + 2)) * (σ 1 (5 ^ (k5 + 1)) * σ 1 (7 ^ (k7 + 2)))) :=
          Nat.mul_le_mul hRle (Nat.mul_le_mul l3 (Nat.mul_le_mul l5 l7))
  have hX : 0 < Rg * 3 ^ k3 * 5 ^ k5 * 7 ^ k7 := by positivity
  omega

end P8Sylvester105

theorem OMA.solution : OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R2.H1 :=
  P8Sylvester105.sylvester_105
