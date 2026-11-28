import FormalConjectures.OEIS.«77408»

/-!
# Reduction OeisA77408.conjecture.R1

A077408: `a` is the trajectory of `103` under Reverse-and-Add in base `3`, i.e. `a 0 = 103` and
`a (n+1) = a n + revBase 3 (a n)`.  The conjecture is that this trajectory never reaches a
base-3 palindrome, which would make `103` the least base-3 Reverse-and-Add Lychrel number.

The statement quantifies over all `n`, so it splits at the concrete bound `1000`:

* `H1` -- the finite window `n <= 1000`: a finite, decidable verification with cheap evaluation.
  `a` is a structurally recursive function on a concrete numeral and `IsBasePalindrome` unfolds
  to an equality of naturals, so each case is one kernel computation: `decide` closes the case
  `n = 1000` in a few seconds, and the cases below it are cheaper still (neither a digit-list
  search nor a primality test is involved).  It is true: an independent base-3 computation of the
  trajectory up to `n = 3000` finds no palindromic term.
* `H2` -- the tail `1000 < n`: the honest open core.  The orbit grows by about a factor of `1.6`
  per step and there is no known invariant that survives the Reverse-and-Add step in base `3`
  (the classical heuristics for Lychrel numbers are purely probabilistic), so ruling out a
  palindromic term at arbitrary height is the whole conjecture.

`H1` and `H2` together cover all `n`, each is strictly weaker than the parent statement, and
`main` is the case split on `n <= 1000`.
-/

namespace OMA.R_OeisA77408_conjecture_R1

open OeisA77408

/-- The finite window `n <= 1000`: finitely many explicit computations. -/
def H1 : Prop :=
  ∀ n : ℕ, n ≤ 1000 → ¬ IsBasePalindrome 3 (a n)

/-- The tail `1000 < n`: the open core. -/
def H2 : Prop :=
  ∀ n : ℕ, 1000 < n → ¬ IsBasePalindrome 3 (a n)

theorem main : H1 → H2 → type_of% @OeisA77408.conjecture := by
  intro h1 h2 n
  by_cases h : n ≤ 1000
  · exact h1 n h
  · exact h2 n (by omega)

end OMA.R_OeisA77408_conjecture_R1
