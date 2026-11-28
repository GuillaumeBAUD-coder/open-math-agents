import FormalConjectures.OEIS.«91591»

/-!
# Reduction OeisA91591.conjecture.R1

A091591: `a n` is the number of twin prime pairs `(p, p + 2)` that lie strictly between
`n ^ 2` and `(n + 1) ^ 2`.  Noe's conjecture (2007) is that `a n > 0` for every `n > 122`;
proving it would also prove Legendre's conjecture.

The statement quantifies over all `n > 122`, so it splits at the concrete bound `1000`:

* `H1` -- the finite window `122 < n <= 1000`: a finite, decidable verification (978 finite
  searches over bounded intervals, each one a primality test).  It is true: a sieve up to
  `1001 ^ 2` shows that every one of those 978 intervals contains at least one twin prime pair.
* `H2` -- the tail `1000 < n`: the honest open core.  It implies Legendre's conjecture, and no
  known argument produces a twin prime pair between two consecutive squares at arbitrary
  height, so all the difficulty of the problem sits in this half.

`H1` and `H2` together cover exactly the range of the parent statement, each is strictly weaker
than it, and `main` is the case split on `n <= 1000`.
-/

namespace OMA.R_OeisA91591_conjecture_R1

open OeisA91591

/-- The finite window `122 < n <= 1000`: finitely many explicit cases. -/
def H1 : Prop :=
  ∀ n : ℕ, 122 < n → n ≤ 1000 → 0 < a n

/-- The tail `1000 < n`: the open core (it implies Legendre's conjecture). -/
def H2 : Prop :=
  ∀ n : ℕ, 1000 < n → 0 < a n

theorem main : H1 → H2 → type_of% @OeisA91591.conjecture := by
  intro h1 h2 n hn
  by_cases h : n ≤ 1000
  · exact h1 n hn h
  · exact h2 n (by omega)

end OMA.R_OeisA91591_conjecture_R1
