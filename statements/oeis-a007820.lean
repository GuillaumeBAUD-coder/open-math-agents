import Mathlib

/-!
# A007820: Stirling numbers of second kind S(2n,n).

Source: https://oeis.org/A007820
Credit: @eitanteperman

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a007820

/-- A007820: a(n) = S(2n, n), Stirling numbers of the second kind (Mathlib's `Nat.stirlingSecond`),
offset 0 (a(0) = 1, a(1) = 1, a(2) = 7, a(3) = 90, ...). -/
def a (n : ℕ) : ℕ := Nat.stirlingSecond (2 * n) n

/-- Conjecture (Peter Bala, Mar 2025): a(2n+1) is divisible by (2n+1)^2, for all n >= 0. -/
theorem main : ∀ n : ℕ, (2 * n + 1) ^ 2 ∣ a (2 * n + 1) := by
  sorry

end OMA.S_oeis_a007820
