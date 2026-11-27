import Mathlib

/-!
# A242560: Least positive number k such that (n!-k)/(n-k) is an integer.

Source: https://oeis.org/A242560

Offset 1 (data 2, 1, 2, 2, 4, 3, 6, 4, ...). The quotient is taken in ℤ, so `k > n` (negative
denominator) is allowed, and `k = n` (zero denominator) is excluded. "(n!-k)/(n-k) is an integer"
is expressed as `(n! - k) % (n - k) = 0` in ℤ. Such a `k` always exists (`k = n + 1` works),
so `a n` is the least one, given by `Nat.find`.

Formalizes the conjecture stated in the OEIS entry: a(2n) = n (for n >= 1).
-/

namespace OMA.S_oeis_a242560

/-- Some positive `k ≠ n` makes `(n! - k)/(n - k)` an integer (for example `k = n + 1`). -/
theorem exists_good (n : ℕ) :
    ∃ k : ℕ, 0 < k ∧ k ≠ n ∧ ((n.factorial : ℤ) - k) % ((n : ℤ) - k) = 0 := by
  refine ⟨n + 1, by omega, by omega, ?_⟩
  have h : ((n : ℤ) - ((n + 1 : ℕ) : ℤ)) = -1 := by push_cast; ring
  rw [h]
  exact Int.emod_eq_zero_of_dvd (neg_dvd.mpr (one_dvd _))

/-- A242560: the least positive `k` such that `(n! - k)/(n - k)` is an integer. -/
def a (n : ℕ) : ℕ := Nat.find (exists_good n)

/-- The conjecture of A242560: `a(2n) = n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a (2 * n) = n := by
  sorry

end OMA.S_oeis_a242560
