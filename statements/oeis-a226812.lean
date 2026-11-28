import Mathlib

/-!
# A226812: sums of distinct numbers 3^j + 6^k with no summand dividing another

Source: https://oeis.org/A226812 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A226812 (offset 1): numbers of the form 3^j + 6^k, for j and k >= 0; data
2, 4, 7, 9, 10, 15, 28, 33, 37, 39, 45, 63, ...

The entry records (Zhi-Wei Sun, May 01 2023):

  Conjecture: Any positive integer not among 1, 3, 5, 6, 8, 12, 27 can be written as a sum of
  distinct terms of the current sequence with no summand dividing another.

Reading of the source:
* The terms are the numbers `3^j + 6^k` with `j, k ≥ 0`.
* "a sum of distinct terms with no summand dividing another": a finite set `T` of such numbers
  (so the summands are distinct), with `∑ T = n`, such that for any two different elements `x`, `y`
  of `T`, `x` does not divide `y`. A single term counts as such a sum.
* "Any positive integer not among 1, 3, 5, 6, 8, 12, 27": every `n ≥ 1` other than these seven.
  (These seven are exactly the exceptions below 400.)
-/

namespace OMA.S_oeis_a226812

/-- `x` is a term of A226812: `x = 3^j + 6^k` for some `j, k ≥ 0`. -/
def IsTerm (x : ℕ) : Prop := ∃ j k : ℕ, x = 3 ^ j + 6 ^ k

/-- Every positive integer other than 1, 3, 5, 6, 8, 12, 27 is the sum of a set of terms in which
no element divides another. -/
theorem main : ∀ n : ℕ, 1 ≤ n → n ∉ ({1, 3, 5, 6, 8, 12, 27} : Finset ℕ) →
    ∃ T : Finset ℕ, (∀ x ∈ T, IsTerm x) ∧ (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧
      ∑ x ∈ T, x = n := by
  sorry

end OMA.S_oeis_a226812
