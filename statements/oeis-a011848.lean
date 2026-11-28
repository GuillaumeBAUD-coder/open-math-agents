import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Bounds.Defs

/-!
# The proposed maximum-index description of A011848 at n = 2

Peter Kagey's November 18, 2016 comment in A011848 specifies n = 2.
The compared sequence A123663 counts shared edges in a square spiral and
has offset 1. Its published integer-square-root formula is used below.
A000217 has offset 0 and gives the triangular numbers.

Sources: https://oeis.org/A011848, https://oeis.org/A123663,
https://oeis.org/A000217 (OEIS Foundation, CC BY-SA 4.0).
Credit: @yukimiyazaki
-/

namespace OMA.S_oeis_a011848

def a (n : ℕ) : ℕ := n.choose 2 / 2

def edges (k : ℕ) : ℕ := 2*k - 1 - (4*k - 1).sqrt

def triangular (m : ℕ) : ℕ := m*(m+1)/2

def candidates (n : ℕ) : Set ℕ := {k | 1 ≤ k ∧ edges k < triangular (n-2)}

theorem main : IsGreatest (candidates 2) (a 2) := by
  sorry

end OMA.S_oeis_a011848
