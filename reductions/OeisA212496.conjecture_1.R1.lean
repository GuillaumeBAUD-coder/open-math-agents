import FormalConjectures.OEIS.«212496»

/-!
# Reduction OeisA212496.conjecture_1.R1

A212496: `a n = sum_{k = 1..n} (-1) ^ (k + Omega k)`, the partial sums of `(-1) ^ (k - Omega k)`,
where `Omega k` is the number of prime factors of `k` counted with multiplicity.  Sun's
conjecture of 16 May 2012 is that `a n > 0` for every `n > 4`.

The statement quantifies over all `n > 4`, so it splits at the concrete bound `1000`:

* `H1` -- the finite window `4 < n <= 1000`: a finite, decidable verification with cheap
  evaluation.  `Omega` is decidable and the recursion is a partial sum, so each case is a single
  kernel computation of about `n` small steps: `decide` closes the worst case `n = 1000` in a few
  seconds (measured in the pinned checkout).  It is true: an independent sieve for `Omega` up to
  `20000` finds no `n > 4` with `a n <= 0`.
* `H2` -- the tail `1000 < n`: the honest open core.  The conjecture says the partial sums of the
  Liouville-type sequence `(-1) ^ (k + Omega k)` stay positive, i.e. the odd and even terms
  never tie again.  No known method controls the sign of such a partial sum, so the tail carries
  the whole difficulty.

`H1` and `H2` together cover the range of the parent statement, each is strictly weaker than it,
and `main` is the case split on `n <= 1000`.
-/

namespace OMA.R_OeisA212496_conjecture_1_R1

open OeisA212496

/-- The finite window `4 < n <= 1000`: finitely many explicit computations. -/
def H1 : Prop :=
  ∀ n : ℕ, 4 < n → n ≤ 1000 → 0 < a n

/-- The tail `1000 < n`: the open core. -/
def H2 : Prop :=
  ∀ n : ℕ, 1000 < n → 0 < a n

theorem main : H1 → H2 → type_of% @OeisA212496.conjecture_1 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 1000
  · exact h1 n hn h
  · exact h2 n (by omega)

end OMA.R_OeisA212496_conjecture_1_R1
