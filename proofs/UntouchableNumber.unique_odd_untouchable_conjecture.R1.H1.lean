import OMAReductions.R_UntouchableNumber_unique_odd_untouchable_conjecture_R1
import Mathlib

/-! Step H1: no natural number has proper divisors summing to 5. A composite n has a proper
divisor d with d * d at least n, so its proper divisors sum to at least 1 + d, which bounds n
by 16, and the numbers up to 16 are checked directly. -/

-- Step UntouchableNumber.unique_odd_untouchable_conjecture.R1.H1: hypothesis H1 of reduction UntouchableNumber.unique_odd_untouchable_conjecture.R1
-- Credit: @ivillar

theorem OMA.solution : OMA.R_UntouchableNumber_unique_odd_untouchable_conjecture_R1.H1 := by
  rintro ⟨n, hsum⟩
  by_cases hn : n ≤ 16
  · interval_cases n <;> revert hsum <;> decide
  by_cases hp : n.Prime
  · rw [Nat.Prime.sum_properDivisors hp] at hsum
    omega
  -- Every proper divisor greater than one contributes alongside one, so it is at most four.
  have bound (d : ℕ) (hd : d ∣ n) (hd1 : 1 < d) (hdn : d < n) : d ≤ 4 := by
    have hsub : ({1, d} : Finset ℕ) ⊆ n.properDivisors :=
      Finset.insert_subset_iff.mpr ⟨Nat.mem_properDivisors.mpr ⟨one_dvd _, by omega⟩,
        Finset.singleton_subset_iff.mpr (Nat.mem_properDivisors.mpr ⟨hd, hdn⟩)⟩
    have h := Finset.sum_le_sum_of_subset (f := fun t => t) hsub
    rw [Finset.sum_pair (by omega)] at h
    omega
  obtain ⟨d, hd, hd1, hdn⟩ := Nat.exists_dvd_of_not_prime2 (by omega : 2 ≤ n) hp
  have he := Nat.div_mul_cancel hd
  have hq : 1 < n / d := by
    by_contra! h
    have := Nat.mul_le_mul_right d h
    omega
  have hb := Nat.mul_le_mul
    (bound (n / d) (Nat.div_dvd_of_dvd hd) hq (Nat.div_lt_self (by omega) hd1))
    (bound d hd hd1 hdn)
  omega
