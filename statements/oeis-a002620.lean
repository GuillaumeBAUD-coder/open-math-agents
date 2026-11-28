import Mathlib

/-!
# A002620: Quarter-squares: a(n) = floor(n/2)*ceiling(n/2). Equivalently, a(n) = floor(n^2/4).

Source: https://oeis.org/A002620
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a002620

def a (n : ℕ) : ℕ :=
  n ^ 2 / 4

theorem main : ∀ n : ℕ, n > 2 → ∃ p : ℕ, p.Prime ∧ a n < p ∧ p < a (n + 1) := by
  sorry

end OMA.S_oeis_a002620
