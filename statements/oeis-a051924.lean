import Mathlib

/-!
# A051924: a(n) = binomial(2*n,n) - binomial(2*n-2,n-1); or (3n-2)*C(n-1), where C = Catalan numbers (A000108).

Source: https://oeis.org/A051924
Credit: @eitanteperman

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a051924

/-- A051924: a(n) = binomial(2n, n) - binomial(2n-2, n-1), offset 1 (a(1) = 1, a(2) = 4, a(3) = 14, ...).
The subtraction is in the naturals but never truncates (the first binomial is larger). -/
def a (n : ℕ) : ℕ := (2 * n).choose n - (2 * n - 2).choose (n - 1)

/-- Conjecture (Gary Detlefs, Feb 2013): for n >= 1, `a(n) mod n^2 = n + 2` if and only if `n` is an
odd prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n % n ^ 2 = n + 2 ↔ (n.Prime ∧ Odd n)) := by
  sorry

end OMA.S_oeis_a051924
