import FormalConjectures.OEIS.«109671»

-- Reduction OeisA109671.conjecture.R1 of Conjectures associated with A109671
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The self-describing sequence of A109671: the checked values and the open tail

The sequence has `a 1 = 1`, `a (2n) = a n`, and `a (2n + 1)` is the smallest positive integer whose
distance from `a (2n - 1)` is `a n`. Its odd-indexed absolute differences are the sequence itself,
and the record values alternate between `3 ^ j` and `2 * 3 ^ j` at the indices `2 ^ k - 1`
(observed through the first `2 * 10 ^ 5` terms).

The open question is whether every positive integer occurs. Nothing uniform is known: the value
`a n` is built from a difference of two earlier values, so a small integer can be squeezed out for
a long time, and the sequence is not monotone.

The OEIS entry A109671 publishes the table of `a n` for `n = 1..10000` (N. J. A. Sloane). Running
that recurrence over the first `10 ^ 4` terms and collecting the values shows that every integer
from `1` to `49` occurs there (for instance `1` at `n = 1`, `2` at `n = 3`, `3` at `n = 7`,
`4` at `n = 39`, `5` at `n = 17`, `6` at `n = 15`), while `50` and `56` do not occur among those
`10 ^ 4` terms. So the question splits along the checked prefix:

* `H1` (checked values): every `m` with `0 < m ≤ 49` occurs among the first `10 ^ 4` terms.
* `H2` (the open tail): every `m > 49` occurs. This is the open part; `50` and `56` already show
  that the occurrence is not monotone in `m`, so the tail needs its own argument.

`H1` is stated without the index bound `10 ^ 4`, because an occurrence at any index is all that its
half of the target needs; the bound is only where the finite check lives. Neither hypothesis
mentions the target, the other one, or `main`; `main` is the case split at `49`.
-/

namespace OMA.R_OeisA109671_conjecture_R1

/-- The checked values: every `m` with `0 < m ≤ 49` occurs in the sequence (table to `10 ^ 4`). -/
def H1 : Prop :=
  ∀ m : ℕ, 0 < m → m ≤ 49 → ∃ n : ℕ, 0 < n ∧ OeisA109671.a n = m

/-- The open tail: every `m > 49` occurs; `50` and `56` are the first values the table misses. -/
def H2 : Prop :=
  ∀ m : ℕ, 49 < m → ∃ n : ℕ, 0 < n ∧ OeisA109671.a n = m

theorem main : H1 → H2 → type_of% @OeisA109671.conjecture := by
  intro h1 h2 m hm
  by_cases h : m ≤ 49
  · exact h1 m hm h
  · exact h2 m (Nat.lt_of_not_le h)

end OMA.R_OeisA109671_conjecture_R1
