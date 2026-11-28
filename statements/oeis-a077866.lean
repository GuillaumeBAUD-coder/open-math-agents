import Mathlib

/-!
# A077866: Expansion of (1-x)^(-1)/(1 - x - 2*x^2 + 2*x^3).

Source: https://oeis.org/A077866
Comment (Clark Kimberling, Sep 27 2022): let b(n) be the number of subsets S of
{1,2,...,n} having more than one element such that (sum of least two elements of S)
= max(S). Then b(0) = b(1) = b(2) = 0 and b(n+3) = a(n) for n >= 0.
The sequence a begins 1, 2, 5, 8, 15, 22, 37, 52, ... and satisfies
a(n) = 2*a(n-1) + a(n-2) - 4*a(n-3) + 2*a(n-4).

Credit: @bear20252026 (agent: catpaw, model CatPaw)

We state Kimberling's conjecture: the counting function `kimberlingCount` below
equals the shifted OEIS sequence `a077866`.  The predicate uses the equivalent
formulation: there are two distinct elements `a < b` that are both at most every
element of `S`, and their sum lies in `S` and dominates every element of `S`;
then `a` and `b` are the two smallest elements and their sum is the maximum.
The body stays `sorry`; a person reviews the translation before merging.
-/

noncomputable section

open scoped Classical

namespace OMA.S_oeis_a077866

/-- `TwoSmallestSumToMax S` says that `S` has at least two elements and the sum of
its two smallest elements equals its largest element.

Equivalently, there are `a < b` in `S` with `a` and `b` both at most every element
of `S`, such that `a + b` belongs to `S` and is at least every element of `S`
(hence `a + b` is the maximum of `S`). -/
def TwoSmallestSumToMax (S : Finset ℕ) : Prop :=
  ∃ a b : ℕ, a ∈ S ∧ b ∈ S ∧ a < b ∧
    (∀ c ∈ S, a ≤ c) ∧ (∀ c ∈ S, b ≤ c) ∧
    a + b ∈ S ∧ (∀ c ∈ S, c ≤ a + b)

/-- `kimberlingCount n` is the number `b(n)` of subsets `S` of `{1, ..., n}` having
more than one element such that the sum of the two smallest elements of `S` equals
the maximum of `S`. -/
def kimberlingCount (n : ℕ) : ℕ :=
  (((Finset.range n).image (fun k => k + 1)).powerset.filter
    (fun S => TwoSmallestSumToMax S)).card

/-- One step of the OEIS recurrence, carrying four consecutive values. -/
def a077866Step : (ℕ × ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ × ℕ)
  | (a, b, c, d) => (b, c, d, 2 * d + c - 4 * b + 2 * a)

/-- The OEIS A077866 sequence `1, 2, 5, 8, 15, 22, ...`, defined by
`a(n) = 2*a(n-1) + a(n-2) - 4*a(n-3) + 2*a(n-4)` with `a(0) = 1`, `a(1) = 2`,
`a(2) = 5`, `a(3) = 8`. -/
def a077866 (n : ℕ) : ℕ :=
  ((List.range n).foldl (fun acc _ => a077866Step acc) (1, 2, 5, 8)).1

theorem main :
    kimberlingCount 0 = 0 ∧ kimberlingCount 1 = 0 ∧ kimberlingCount 2 = 0 ∧
      ∀ n : ℕ, kimberlingCount (n + 3) = a077866 n := by
  sorry

end OMA.S_oeis_a077866

end
