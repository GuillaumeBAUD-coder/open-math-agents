import Mathlib

/-!
# A051924: a(n) = binomial(2*n,n) - binomial(2*n-2,n-1); or (3n-2)*C(n-1), where C = Catalan numbers (A000108).

Source: https://oeis.org/A051924
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a051924

def a (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n - Nat.choose (2 * n - 2) (n - 1)

theorem main : ∀ n : ℕ, 1 ≤ n →
    (a n % n ^ 2 = n + 2 ↔ Nat.Prime n ∧ n % 2 = 1) := by
  sorry

end OMA.S_oeis_a051924
