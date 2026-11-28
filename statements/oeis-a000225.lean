import Mathlib

/-!
# A000225: a(n) = 2^n - 1. (Sometimes called Mersenne numbers, although that name is usually reserved for A001348.)

Source: https://oeis.org/A000225
Credit: @azmiozgen

Conjecture (Chai Wah Wu, Sep 08 2021): except for a(2) = 3, the terms are the numbers m such that
2^(m+1) - 2^j - 2^k - 1 is composite for all 0 <= j < k <= m.

Formalization notes:
* The conjecture is stated as a characterization of the numbers m ≥ 0: the condition holds
  exactly for m = 2^n - 1 (n ≥ 0) with m ≠ 3.
* For 0 <= j < k <= m the number 2^(m+1) - 2^j - 2^k - 1 is at least 2^(k-1) - 1 ≥ 0, so the
  subtraction in ℕ never truncates.
* "Composite" is read as "not prime". The two readings differ only when the number is 0 or 1,
  which happens only for m = 1 (the single pair j = 0, k = 1 gives 0). Under the strict reading
  m = 1 = a(1) would be excluded and the conjecture would fail at once, contradicting the entry,
  which lists only a(2) as the exception; so the intended reading is "not prime".
* Controls: for m ≤ 20 the condition holds exactly for m = 0, 1, 7, 15.
-/

namespace OMA.S_oeis_a000225

/-- Wu's condition: `2^(m+1) - 2^j - 2^k - 1` is not prime for all `0 ≤ j < k ≤ m`. -/
def WuCondition (m : ℕ) : Prop :=
  ∀ j k : ℕ, j < k → k ≤ m → ¬ (2 ^ (m + 1) - 2 ^ j - 2 ^ k - 1).Prime

/-- Wu's conjecture: the condition holds exactly at the terms `2^n - 1` other than `3`. -/
theorem main : ∀ m : ℕ, WuCondition m ↔ (m ≠ 3 ∧ ∃ n : ℕ, m = 2 ^ n - 1) := by
  sorry

end OMA.S_oeis_a000225
