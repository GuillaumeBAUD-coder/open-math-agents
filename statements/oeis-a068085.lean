import Mathlib

/-!
# A068085: Triangular numbers whose tenfold multiples are triangular

Source: https://oeis.org/A068085

A068085 lists the nonnegative integers `k` such that `k` and `10*k` are both
triangular, in strictly increasing order. We use zero-based indexing, so its
first terms are 0, 1, 21, 78. Harvey P. Dale conjectured the stated recurrence.
-/

namespace OMA.S_oeis_a068085

/-- A number is triangular when it is half the product of consecutive natural numbers. -/
def triangular (k : ℕ) : Prop := ∃ t : ℕ, t * (t + 1) = 2 * k

/-- A068085, with zero-based indices and values cast to integers for the recurrence. -/
noncomputable def a (n : ℕ) : ℤ := Nat.nth (fun k => triangular k ∧ triangular (10*k)) n

theorem main : ∀ n : ℕ,
    a (n+7) = a (n+6) + 1442*a (n+4) - 1442*a (n+3) - a (n+1) + a n := by
  sorry

end OMA.S_oeis_a068085
