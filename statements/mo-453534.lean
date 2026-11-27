import Mathlib

/-!
# A question about Euclidean domains

Source: https://mathoverflow.net/questions/453534
Credit: @koolkao

Question (Mohammad Safdari, MathOverflow 453534, 2023; CC BY-SA 4.0). An integral domain `R` is a
Euclidean domain if there is a degree function `deg : R - {0} → ℤ_{≥0}` such that
1. for every `a, b ∈ R` with `b ≠ 0` there are `q, r ∈ R` such that `a = bq + r` in which either
   `r = 0` or `deg(r) < deg(b)`;
2. for every nonzero `a, b ∈ R` we have `deg(a) ≤ deg(ab)`.
Now the question is: let `R` be a Euclidean domain with degree function `deg`. Is it true that in
the division algorithm `a = bq + r` we can always choose some remainder `r` so that either
`a - r = 0` or `deg(a - r) ≤ deg a`? […] So is it true in any Euclidean domain? Or are there any
counterexamples? And if so, is there any extra property of the domain or its degree function that
guarantees the existence of such remainders (for example `deg` being multiplicative)? Edit: […]
the degree function is not required to be defined at `0`, so the trivial case of `r = a` and
`q = 0` is mentioned separately.

`main` states that the answer is yes: for every integral domain `R`, every degree function `deg`
satisfying 1 and 2, and all `a, b ∈ R` with `b ≠ 0`, there are `q, r` with `a = bq + r`, `r = 0` or
`deg r < deg b`, and `a - r = 0` or `deg(a - r) ≤ deg a`. A disproof is a counterexample.

Translation choices:
* `R` is a commutative ring with `IsDomain R`, in `Type`;
* the degree function is given as `deg : R → ℕ`; its value at `0` is never used: in each place
  where `deg` is applied to an element that could be `0` (`deg r` in 1 and in the conclusion,
  `deg (a - r)`, `deg a`), the formula has the alternative `r = 0`, resp. `a - r = 0`, or `a ≠ 0`
  is forced, exactly as in the source. (If `a = 0`, the choice `q = 0`, `r = 0` satisfies the
  conclusion, so `deg 0` never matters there either);
* "we can always choose some remainder" is read as: for all `a` and all `b ≠ 0` some pair `(q, r)`
  satisfies both the division condition 1 and the extra condition;
* not formalized: the follow-up question about extra properties that would guarantee such
  remainders.
-/

namespace OMA.S_mo_453534

/-- The two axioms of a Euclidean degree function, as in the source. -/
def IsEuclideanDegree {R : Type} [CommRing R] (deg : R → ℕ) : Prop :=
  (∀ a b : R, b ≠ 0 → ∃ q r : R, a = b * q + r ∧ (r = 0 ∨ deg r < deg b)) ∧
  (∀ a b : R, a ≠ 0 → b ≠ 0 → deg a ≤ deg (a * b))

/-- In every Euclidean domain, for every `a` and `b ≠ 0` one can choose the division
`a = bq + r` so that also `a - r = 0` or `deg (a - r) ≤ deg a`. -/
theorem main :
    ∀ (R : Type) [CommRing R] [IsDomain R] (deg : R → ℕ), IsEuclideanDegree deg →
      ∀ a b : R, b ≠ 0 → ∃ q r : R, a = b * q + r ∧ (r = 0 ∨ deg r < deg b) ∧
        (a - r = 0 ∨ deg (a - r) ≤ deg a) := by
  sorry

end OMA.S_mo_453534
