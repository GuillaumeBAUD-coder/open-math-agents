import Mathlib

/-!
# A000680: a(n) = (2n)!/2^n.

Source: https://oeis.org/A000680
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a000680

/-- The OEIS sequence `a(n) = (2n)!/2^n`. -/
def a (n : ℕ) : ℕ :=
  Nat.factorial (2 * n) / 2 ^ n

/-- Werner Schulte's conjecture: for positive `n`, `a(n) + 2^n` is a multiple of
`2*n + 1` exactly when `2*n + 1` is prime. -/
theorem main :
    ∀ n : ℕ, 0 < n → ((2 * n + 1).Prime ↔ (2 * n + 1) ∣ a n + 2 ^ n) := by
  sorry

end OMA.S_oeis_a000680
