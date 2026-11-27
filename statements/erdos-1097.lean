import Mathlib

/-!
# Erdős Problem 1097

Source: https://www.erdosproblems.com/1097
Credit: @SudharsanAnimations

Let `A` be a set of `n` integers. How many distinct `d` can occur as the common difference of
a three-term arithmetic progression in `A`? In particular, are there always `O(n^{3/2})` such `d`?

We formalize the second question. As noted on the problem page, it has a negative answer: the
best known lower bound for the optimal exponent (due to Lemm) exceeds `3/2`. We state that
negative answer: there is no constant `C` such that every finite set `A` of integers has at most
`C · |A|^{3/2}` common differences of three-term arithmetic progressions in `A`. (The first
question, the exact order of magnitude, is not formalized here.)

Conventions:
- A three-term arithmetic progression in `A` with common difference `d` is `a, a + d, a + 2d`
  all in `A` with `d > 0`. The progressions with difference `d` and `-d` are the same set, so
  counting positive differences only is the natural reading, and it changes the count by at most
  a factor of `2`, which does not affect an `O(n^{3/2})` bound.
- `O(n^{3/2})` is read as a uniform bound `≤ C · n^{3/2}` over all finite sets; since every
  nonempty `A` has at most `|A|^2` differences, this is equivalent to the asymptotic reading.
-/

namespace OMA.S_erdos_1097

/-- The common differences `d > 0` of three-term arithmetic progressions `a, a + d, a + 2d`
contained in `A`. -/
def apDifferences (A : Finset ℤ) : Finset ℤ :=
  ((A ×ˢ A).filter (fun p => p.1 < p.2 ∧ 2 * p.2 - p.1 ∈ A)).image (fun p => p.2 - p.1)

/-- The answer to the second question is negative: the number of common differences is not
always `O(n^{3/2})`. -/
theorem main : ¬ ∃ C : ℝ, ∀ A : Finset ℤ,
    ((apDifferences A).card : ℝ) ≤ C * (A.card : ℝ) ^ ((3 : ℝ) / 2) := by
  sorry

end OMA.S_erdos_1097
