import Mathlib

/-!
# A047704: Numbers that are the sum of 5 but no fewer positive cubes.

Source: https://oeis.org/A047704
Credit: @jagraj28

Conjecture (T. D. Noe, 2006, stated in A047704): the sequence has only finitely many terms.

Formalization notes:
* `IsSumOfPosCubes k n`: `n` is the sum of `k` positive cubes (repetitions allowed), written
  with a function `Fin k → ℕ` of positive values.
* A term is an `n` that is a sum of `5` positive cubes and not a sum of `k` positive cubes for
  any `k < 5`.
* A direct computation of the least number of positive cubes gives exactly the listed data
  (the terms up to `248`).
-/

namespace OMA.S_oeis_a047704

/-- `n` is the sum of `k` positive cubes. -/
def IsSumOfPosCubes (k n : ℕ) : Prop :=
  ∃ f : Fin k → ℕ, (∀ i, 0 < f i) ∧ ∑ i, f i ^ 3 = n

/-- The conjecture of A047704: only finitely many numbers are sums of 5 but no fewer positive
cubes. -/
theorem main :
    {n : ℕ | IsSumOfPosCubes 5 n ∧ ∀ k < 5, ¬ IsSumOfPosCubes k n}.Finite := by
  sorry

end OMA.S_oeis_a047704
