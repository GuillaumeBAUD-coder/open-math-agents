import Mathlib

/-!
# A007531: a(n) = n*(n-1)*(n-2) (or n!/(n-3)!).

Source: https://oeis.org/A007531
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a007531

theorem main : ∀ n k : ℕ,
    ((n : ℤ) ^ 3 - (n : ℤ) = (Nat.factorial k : ℤ) ↔
      (n = 2 ∧ k = 3) ∨ (n = 3 ∧ k = 4) ∨
        (n = 5 ∧ k = 5) ∨ (n = 9 ∧ k = 6)) := by
  sorry

end OMA.S_oeis_a007531
