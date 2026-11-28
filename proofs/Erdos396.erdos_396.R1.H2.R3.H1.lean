import OMAReductions.R_Erdos396_erdos_396_R1_H2_R3
import Mathlib

-- Step Erdos396.erdos_396.R1.H2.R3.H1: the refined Kummer carry criterion.
-- The exponent of a prime p in C(2n, n) is the number of j >= 1 with p ^ j <= 2 * (n % p ^ j)
-- (Kummer's theorem, in Mathlib as padicValNat_choose). The exponent of p in the falling
-- factorial n (n-1) ... (n-k) is the sum of the exponents of its factors. For p <= k the first
-- hypothesis bounds this sum. For p > k at most one factor is divisible by p, since two factors
-- differ by a positive amount at most k, so the sum is a single term, bounded by the second
-- hypothesis, or zero.

namespace OMA.Helpers

lemma refined396_carries (p n : ℕ) (hp : p.Prime) :
    padicValNat p ((2 * n).choose n) =
      ((Finset.Ico 1 (2 * n + 1)).filter fun j => p ^ j ≤ 2 * (n % p ^ j)).card := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hlog : Nat.log p (2 * n) < 2 * n + 1 :=
    lt_of_le_of_lt (Nat.log_le_self p (2 * n)) (Nat.lt_succ_self _)
  rw [padicValNat_choose (by omega : n ≤ 2 * n) hlog]
  have h2 : 2 * n - n = n := by omega
  congr 1
  apply Finset.filter_congr
  intro j _
  rw [h2, two_mul]

lemma refined396_falling (p k n : ℕ) (hp : p.Prime) (hkn : k < n) :
    (∏ i ∈ Finset.range (k + 1), (n - i)).factorization p =
      ∑ i ∈ Finset.range (k + 1), padicValNat p (n - i) := by
  have hne : ∀ i ∈ Finset.range (k + 1), n - i ≠ 0 := by
    intro i hi
    have := Finset.mem_range.mp hi
    omega
  rw [Nat.factorization_prod hne, Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact Nat.factorization_def _ hp

lemma refined396_unique (p k n i j : ℕ) (hkp : k < p) (hkn : k < n) (hi : i ≤ k) (hj : j ≤ k)
    (hpi : p ∣ n - i) (hpj : p ∣ n - j) (hij : i < j) : False := by
  have hd : p ∣ (n - i) - (n - j) := Nat.dvd_sub hpi hpj
  have he : (n - i) - (n - j) = j - i := by omega
  rw [he] at hd
  have := Nat.le_of_dvd (by omega) hd
  omega

lemma refined396_large (p k n : ℕ) (hp : p.Prime) (hkp : k < p) (hkn : k < n)
    (h : ∀ i : ℕ, i ≤ k → p ∣ n - i → padicValNat p (n - i) ≤
        ((Finset.Ico 1 (2 * n + 1)).filter fun j => p ^ j ≤ 2 * (n % p ^ j)).card) :
    ∑ i ∈ Finset.range (k + 1), padicValNat p (n - i) ≤
        ((Finset.Ico 1 (2 * n + 1)).filter fun j => p ^ j ≤ 2 * (n % p ^ j)).card := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hex : ∃ i0, i0 ≤ k ∧ p ∣ n - i0
  · obtain ⟨i0, hi0, hd0⟩ := hex
    rw [Finset.sum_eq_single_of_mem i0 (Finset.mem_range.mpr (by omega))]
    · exact h i0 hi0 hd0
    · intro i hi hne
      have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
      apply padicValNat.eq_zero_of_not_dvd
      intro hdi
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact refined396_unique p k n i i0 hkp hkn hik hi0 hdi hd0 hlt
      · exact refined396_unique p k n i0 i hkp hkn hi0 hik hd0 hdi hgt
  · push_neg at hex
    have hz : ∑ i ∈ Finset.range (k + 1), padicValNat p (n - i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
      exact padicValNat.eq_zero_of_not_dvd (hex i hik)
    rw [hz]
    exact Nat.zero_le _

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos396_erdos_396_R1_H2_R3.H1 := by
  intro k n hkn hs hl
  have hne : ∀ i ∈ Finset.range (k + 1), n - i ≠ 0 := by
    intro i hi
    have := Finset.mem_range.mp hi
    omega
  have hprod : (∏ i ∈ Finset.range (k + 1), (n - i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  have hch : (2 * n).choose n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  rw [Nat.descFactorial_eq_prod_range, Nat.centralBinom_eq_two_mul_choose]
  rw [← Nat.factorization_prime_le_iff_dvd hprod hch]
  intro p hp
  rw [OMA.Helpers.refined396_falling p k n hp hkn, Nat.factorization_def _ hp,
    OMA.Helpers.refined396_carries p n hp]
  by_cases hpk : p ≤ k
  · exact hs p hp hpk
  · exact OMA.Helpers.refined396_large p k n hp (by omega) hkn (hl p hp (by omega))
