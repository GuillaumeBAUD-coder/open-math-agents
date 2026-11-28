import Mathlib

/-!
# OEIS A076771: even numbers are not eventually all sums of two non-coprime odd composites

Source: https://oeis.org/A076771
Credit: @SudharsanAnimations

A076771 lists the even numbers representable as the sum of two non-coprime odd composites. It was
conjectured that there is no N such that every even number n > N is represented; the entry records that
this is true (Charles R Greathouse IV, Aug 2011): 2p is never represented for a prime p. We state the
proved result.

Conventions: an odd composite is an odd number greater than 1 that is not prime; non-coprime means
`gcd a b ≠ 1`.
-/

namespace OMA.S_oeis_a076771

/-- An odd composite number: odd, greater than `1`, and not prime. -/
def OddComposite (a : ℕ) : Prop := Odd a ∧ 1 < a ∧ ¬ a.Prime

/-- `n` is representable as the sum of two non-coprime odd composites (A076771 lists the even
such `n`). -/
def Rep (n : ℕ) : Prop :=
  ∃ a b : ℕ, OddComposite a ∧ OddComposite b ∧ a + b = n ∧ Nat.gcd a b ≠ 1

/-- There is no `N` such that every even number `n > N` is so representable. -/
theorem main : ¬ ∃ N : ℕ, ∀ n : ℕ, N < n → Even n → Rep n := by
  sorry

end OMA.S_oeis_a076771
