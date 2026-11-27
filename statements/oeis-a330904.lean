import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Int.Basic

/-!
# Binary and balanced ternary digit sums (OEIS A330904)

Source: https://oeis.org/A330904 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

Thomas König conjectures that no five consecutive nonnegative integers
have equal binary and balanced ternary digit sums at every position in
the run. A remainder of two in balanced ternary is the digit minus one
and carries one to the next place.
-/

namespace OMA.S_oeis_a330904

def balancedTernaryDigitSum (n : ℕ) : ℤ :=
  if _h : n ≤ 1 then (n : ℤ)
  else if n % 3 = 2 then balancedTernaryDigitSum (n / 3 + 1) - 1
  else balancedTernaryDigitSum (n / 3) + (n % 3 : ℕ)
termination_by n
decreasing_by all_goals omega

def MatchingDigitSums (n : ℕ) : Prop :=
  ((Nat.digits 2 n).count 1 : ℤ) = balancedTernaryDigitSum n

theorem main : ∀ n : ℕ, ¬ (∀ i : Fin 5, MatchingDigitSums (n + i.val)) := by
  sorry

end OMA.S_oeis_a330904
