import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.GCD.Basic

/-!
# Common divisors of powers of two and five

OEIS A270390 records the Ailon–Rudnick conjecture for bases 2 and 5.
The sequence starts at index 1. Source: https://oeis.org/A270390
(OEIS Foundation, CC BY-SA 4.0). Formalization: @ZedingZhang.
-/

namespace OMA.S_oeis_a270390

theorem main : Set.Infinite {n : ℕ | 0 < n ∧ Nat.gcd (2 ^ n - 1) (5 ^ n - 1) = 1} := by
  sorry

end OMA.S_oeis_a270390
