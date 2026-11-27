import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# The three-term recurrence for OEIS A014484

Source: https://oeis.org/A014484. The sequence has exponential generating function
(1 + 2x)/(1 - 2x)^4. We use Ralf Stephan's explicit formula (2004), combining
(n + 1)(n + 2)n! into (n + 2)!. R. J. Mathar proposed the recurrence in 2013.
The OEIS credits Robert Israel with verifying it in 2018.
Credit: @dreamzzz-dev
-/

namespace OMA.S_oeis_a014484

/-- The coefficient of x^n/n! in the exponential generating function, starting at n = 0. -/
def a (n : ℕ) : ℕ := (n + 2).factorial * (2 * n + 3) * 2 ^ n / 6

/-- Mathar's recurrence at every index where all three terms are defined. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (a n : ℤ) + (-2 * (n : ℤ) - 9) * a (n - 1) +
      6 * ((n : ℤ) + 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a014484
