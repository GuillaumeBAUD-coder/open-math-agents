import Mathlib

/-!
# A035062: Numbers n such that 2^n does not contain the digit 7.

Source: https://oeis.org/A035062
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a035062

def IsTerm (k : ℕ) : Prop :=
  7 ∉ Nat.digits 10 (2 ^ k)

theorem main : IsTerm 71 ∧ ∀ k : ℕ, IsTerm k → k ≤ 71 := by
  sorry

end OMA.S_oeis_a035062
