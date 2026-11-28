import Mathlib

/-!
# A337226: every difference is realised exactly once

Source: https://oeis.org/A337226
Credit: @jagraj28

A337226 is the lexicographically earliest sequence of positive integers with the property that,
for all `k > 0`, there is at most one `j` such that `a(j) = a(j+k)`
(1, 1, 2, 1, 3, 4, 2, 5, 1, 6, ...). The entry records the conjecture: for all `k > 0`, there is
exactly one `j` such that `a(j) = a(j+k)` (verified for `0 < k < 11911`).

`main` states the conjecture for every sequence `a` (indexed from 1) that is this lexicographically
earliest sequence, described term by term.

Conventions:
* `GoodUpTo a n`: among the indices `1, ..., n`, for every `k > 0` at most one `j` has
  `a(j) = a(j+k)`.
* The lexicographically earliest sequence is the greedy one: each `a(n)` is the least positive
  integer that keeps `GoodUpTo a n`. The greedy choice never gets stuck (a value not used before
  always works), so the greedy sequence is the lexicographically earliest infinite sequence with
  the property, and the description determines `a(n)` for every `n ≥ 1` by induction. A
  simulation of this description reproduces the listed terms.
-/

namespace OMA.S_oeis_a337226

/-- Among indices `1..n`, for every `k > 0` there is at most one `j` with `a j = a (j + k)`. -/
def GoodUpTo (a : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ k, 0 < k → ∀ i j, 1 ≤ i → 1 ≤ j → i + k ≤ n → j + k ≤ n →
    a i = a (i + k) → a j = a (j + k) → i = j

/-- `a` is the lexicographically earliest sequence of OEIS A337226 (on indices `n ≥ 1`):
each term is the least positive integer that keeps the property. -/
def IsA337226 (a : ℕ → ℕ) : Prop :=
  ∀ n, 1 ≤ n → 1 ≤ a n ∧ GoodUpTo a n ∧
    ∀ v, 1 ≤ v → v < a n → ¬ GoodUpTo (Function.update a n v) n

/-- The conjecture in OEIS A337226. -/
theorem main : ∀ a : ℕ → ℕ, IsA337226 a →
    ∀ k, 0 < k → ∃! j, 1 ≤ j ∧ a j = a (j + k) := by
  sorry

end OMA.S_oeis_a337226
