import FormalConjectures.ErdosProblems.«930»
import Mathlib

-- Reduction Erdos930.erdos_930.variants.consecutive_strong.R1 of Erdős Problem 930 — consecutive strong
-- Credit: @cosmaticdev
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- ErSe75 Theorem 2 split: if the interval Icc (n+1) (n+k) contains a prime p then v_p(P) = 1
-- (2p > n+k), so p ≥ k is a witness and l ≥ 2 does not divide 1; the same holds for p = nextPrime k
-- when n < k. Both cases are proved in main below. The remaining case — n ≥ k and the interval
-- Icc (n+1) (n+k) free of primes — is the hard core of Erdős–Selfridge's Theorem 2 and is left
-- as the hypotheses H1 (l = 2) and H2 (l ≥ 3).

namespace OMA.R_Erdos930_erdos_930_variants_consecutive_strong_R1

open Finset

/-- Hard core of ErSe75 Theorem 2, square case: for n ≥ k with a prime-free interval
Icc (n+1) (n+k), some prime p ≥ k divides the product to a multiplicity not divisible by 2. -/
def H1 : Prop := ∀ k l n : ℕ, 3 ≤ k → l = 2 → k ≤ n → (∀ m ∈ Icc (n+1) (n+k), ¬ Nat.Prime m) → ∃ p, k ≤ p ∧ Nat.Prime p ∧ ¬ (l ∣ Nat.factorization (∏ m ∈ Icc (n+1) (n+k), m) p)

/-- Hard core of ErSe75 Theorem 2, higher-power case: same with l ≥ 3. -/
def H2 : Prop := ∀ k l n : ℕ, 3 ≤ k → 3 ≤ l → k ≤ n → (∀ m ∈ Icc (n+1) (n+k), ¬ Nat.Prime m) → ∃ p, k ≤ p ∧ Nat.Prime p ∧ ¬ (l ∣ Nat.factorization (∏ m ∈ Icc (n+1) (n+k), m) p)

/-- If a prime p lies in Icc (n+1) (n+k) and 2p > n+k, then p is the only multiple of p in the
interval, so the p-adic valuation of the product is 1. -/
lemma v_eq_one {k n p : ℕ} (hp : Nat.Prime p) (hmem : p ∈ Icc (n+1) (n+k)) (h2p : n + k < 2 * p) :
    Nat.factorization (∏ m ∈ Icc (n+1) (n+k), m) p = 1 := by
  have hne : ∀ m ∈ Icc (n+1) (n+k), (m : ℕ) ≠ 0 := by
    intro m hm
    have h1 := (Finset.mem_Icc.mp hm).1
    omega
  rw [Nat.factorization_prod_apply hne]
  have hsum : ∑ m ∈ Icc (n+1) (n+k), m.factorization p = p.factorization p :=
    Finset.sum_eq_single_of_mem p hmem (fun m hm hmp => by
      rw [Nat.factorization_eq_zero_of_not_dvd]
      intro hdvd
      have hm := Finset.mem_Icc.mp hm
      obtain ⟨t, ht⟩ := hdvd
      have ht0 : t ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at ht
        omega
      have ht1 : t ≠ 1 := by
        intro h1
        rw [h1, mul_one] at ht
        exact hmp ht
      have h2 : 2 * p ≤ m := by
        have ht2 : 2 ≤ t := by omega
        calc 2 * p = p * 2 := by ring
          _ ≤ p * t := Nat.mul_le_mul_left p ht2
          _ = m := ht.symm
      omega)
  rw [hsum, hp.factorization]
  simp

/-- A prime inside the interval with 2p > n+k is a witness: l ≥ 2 does not divide 1. -/
lemma not_dvd_witness {k l n p : ℕ} (hl : 2 ≤ l) (hp : Nat.Prime p) (hmem : p ∈ Icc (n+1) (n+k))
    (h2p : n + k < 2 * p) :
    ¬ (l ∣ Nat.factorization (∏ m ∈ Icc (n+1) (n+k), m) p) := by
  rw [v_eq_one hp hmem h2p]
  intro hd
  rw [Nat.dvd_one] at hd
  omega

theorem main : H1 → H2 → type_of% @Erdos930.erdos_930.variants.consecutive_strong := by
  intro H1 H2 k l n hk hl hnext
  by_cases hnn : n < k
  · have hspec : k ≤ Erdos930.nextPrime k ∧ (Erdos930.nextPrime k).Prime :=
      Nat.find_spec (Nat.exists_infinite_primes k)
    have hmem : Erdos930.nextPrime k ∈ Icc (n+1) (n+k) := by
      rw [Finset.mem_Icc]
      exact ⟨by omega, hnext⟩
    have h2p : n + k < 2 * Erdos930.nextPrime k := by omega
    exact ⟨Erdos930.nextPrime k, hspec.1, hspec.2, not_dvd_witness hl hspec.2 hmem h2p⟩
  · push Not at hnn
    by_cases hpr : ∃ m ∈ Icc (n+1) (n+k), Nat.Prime m
    · obtain ⟨q, hqmem, hqprime⟩ := hpr
      have hq1 := (Finset.mem_Icc.mp hqmem).1
      have hq2 := (Finset.mem_Icc.mp hqmem).2
      have hqk : k ≤ q := by omega
      have h2q : n + k < 2 * q := by omega
      exact ⟨q, hqk, hqprime, not_dvd_witness hl hqprime hqmem h2q⟩
    · push Not at hpr
      by_cases hl2 : l = 2
      · exact H1 k l n hk hl2 hnn hpr
      · exact H2 k l n hk (by omega) hnn hpr

end OMA.R_Erdos930_erdos_930_variants_consecutive_strong_R1
