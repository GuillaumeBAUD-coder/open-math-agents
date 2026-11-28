import Mathlib

/-!
# A355330: Numbers k such that A020696(2^k-1) < A020696(2^k+1).

Source: https://oeis.org/A355330
Credit: @jagraj28

`A020696(n)` is Vandiver's function: the product of `d + 1` over the divisors `d` of `n`.
Sándor (2021, "On Vandiver's arithmetical function - I", Notes on Number Theory and Discrete
Mathematics 27(3)) showed that every Mersenne exponent is in A355330, and conjectured that both
A355330 and its complement are infinite.

Formalization notes:
* `vandiver n = ∏ d ∈ n.divisors, (d + 1)`, which is A020696 for `n ≥ 1`.
* The sequence lists positive integers `k` (offset 1), so both sets are subsets of the positive
  integers; the complement is the set of positive `k` that are not terms.
* `main` is the conjunction of the two conjectures. A direct computation of `vandiver` gives
  exactly the listed terms up to `125`.
-/

namespace OMA.S_oeis_a355330

/-- Vandiver's function (A020696): the product of `d + 1` over the divisors `d` of `n`. -/
def vandiver (n : ℕ) : ℕ := ∏ d ∈ n.divisors, (d + 1)

/-- `k` is a term of A355330. -/
def IsTerm (k : ℕ) : Prop := vandiver (2 ^ k - 1) < vandiver (2 ^ k + 1)

/-- Sándor's conjecture: A355330 and its complement in the positive integers are infinite. -/
theorem main :
    {k : ℕ | 0 < k ∧ IsTerm k}.Infinite ∧ {k : ℕ | 0 < k ∧ ¬ IsTerm k}.Infinite := by
  sorry

end OMA.S_oeis_a355330
