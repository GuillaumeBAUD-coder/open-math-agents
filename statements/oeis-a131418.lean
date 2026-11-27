import Mathlib

/-!
# A131418: Numbers n such that Sumdigits(n) = Sumdigits(n + Sumdigits(n)).

Source: https://oeis.org/A131418
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a131418

def sumdigits (n : ℕ) : ℕ :=
  (Nat.digits 10 n).sum

def IsTerm (n : ℕ) : Prop :=
  sumdigits n = sumdigits (n + sumdigits n)

theorem main : ∀ n : ℕ, IsTerm n → 9 ∣ n := by
  sorry

end OMA.S_oeis_a131418
