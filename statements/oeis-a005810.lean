import Mathlib

/-!
# A005810: a(n) = binomial(4n,n).

Source: https://oeis.org/A005810
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a005810

/-- The OEIS sequence A005810. -/
def a (n : ℕ) : ℕ :=
  Nat.choose (4 * n) n

theorem main : ∀ n : ℕ, 2 ≤ n → (a n ≡ 4 [MOD n ^ 3] ↔ Nat.Prime n) := by
  sorry

end OMA.S_oeis_a005810
