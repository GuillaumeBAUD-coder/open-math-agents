import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Finite.Basic

/-!
# OEIS A068132

The conjecture in OEIS A068132 says that every triangular number is the
decimal digit sum of infinitely many triangular numbers.
We use the triangular numbers of A000217, starting at index zero.
Source: https://oeis.org/A068132
-/

namespace OMA.S_oeis_a068132

def triangular (n : ℕ) : ℕ := n * (n + 1) / 2

theorem main :
    ∀ t : ℕ, (∃ n : ℕ, triangular n = t) →
      {m : ℕ | (∃ n : ℕ, triangular n = m) ∧ (Nat.digits 10 m).sum = t}.Infinite := by
  sorry

end OMA.S_oeis_a068132
