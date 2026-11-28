import OMAReductions.R_Erdos396_erdos_396_R3
import Mathlib

-- Step Erdos396.erdos_396.R3.H1: Kummer's carry criterion.
-- The exponent of a prime p in C(2n, n) is the number of j >= 1 with p ^ j <= 2 * (n % p ^ j)
-- (Kummer's theorem, in Mathlib as padicValNat_choose). The falling factorial n (n-1) ... (n-k)
-- is a product of positive integers, so its exponent at p is the sum of the exponents of the
-- factors. Divisibility then follows prime by prime.

namespace OMA.Helpers

lemma kummer396_carries (p n : ℕ) (hp : p.Prime) :
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

lemma kummer396_falling (p k n : ℕ) (hp : p.Prime) (hkn : k < n) :
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

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos396_erdos_396_R3.H1 := by
  intro k n hkn h
  have hne : ∀ i ∈ Finset.range (k + 1), n - i ≠ 0 := by
    intro i hi
    have := Finset.mem_range.mp hi
    omega
  have hprod : (∏ i ∈ Finset.range (k + 1), (n - i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  have hch : (2 * n).choose n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  rw [Nat.descFactorial_eq_prod_range, Nat.centralBinom_eq_two_mul_choose]
  rw [← Nat.factorization_prime_le_iff_dvd hprod hch]
  intro p hp
  rw [OMA.Helpers.kummer396_falling p k n hp hkn, Nat.factorization_def _ hp,
    OMA.Helpers.kummer396_carries p n hp]
  exact h p hp
