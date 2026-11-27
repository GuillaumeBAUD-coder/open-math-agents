import Mathlib

/-!
# A008676: Expansion of 1/((1-x^3)*(1-x^5)).

Source: https://oeis.org/A008676
Credit: @eitanteperman

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a008676

/-- A008676: expansion of 1/((1-x^3)(1-x^5)), i.e. the number of partitions of n into parts 3 and 5
(OEIS comment by Andrew Baxter): the number of pairs `(i, j)` of naturals with `3 i + 5 j = n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter (fun p => 3 * p.1 + 5 * p.2 = n)).card

/-- Conjecture (John W. Layman, Sep 2009): a(n) = floor(2(n+3)/3) - floor(3(n+3)/5), for all n >= 0.
Floors are integer division on nonnegative integers. -/
theorem main : ∀ n : ℕ, (a n : ℤ) = 2 * ((n : ℤ) + 3) / 3 - 3 * ((n : ℤ) + 3) / 5 := by
  sorry

end OMA.S_oeis_a008676
