import Mathlib

/-!
# A035064: Numbers k such that 2^k does not contain the digit 9 (probably finite).

Source: https://oeis.org/A035064
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a035064

def IsTerm (k : ℕ) : Prop :=
  9 ∉ Nat.digits 10 (2 ^ k)

theorem main : IsTerm 108 ∧ ∀ k : ℕ, IsTerm k → k ≤ 108 := by
  sorry

end OMA.S_oeis_a035064
