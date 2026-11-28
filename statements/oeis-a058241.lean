import Mathlib

/-!
# A058241: n integers on a circle whose arc sums are 1, ..., n^2 - n + 1

Source: https://oeis.org/A058241 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A058241 (offset 1): number of sets of n positive integers that can be placed along a circle such
that the set of sums of adjacent integers forms {1, 2, ..., n^2-n+1}; data
1, 1, 1, 2, 1, 5, 0, 6, 4, 6, 0, 18, ...
(For n = 3, the set {1, 2, 4} placed as (1, 4, 2) gives the sums 1, 2, 4, 1+4, 4+2, 2+1 and
1+2+4, which are 1, ..., 7.)

The entry records:

  Conjecture: for n > 2, p prime, e > 0, if n-1 is of the form p^e then a(n) > 0,
  otherwise a(n)=0.

Reading of the source:
* "sums of adjacent integers" are the sums of runs of consecutive integers along the circle, as
  in the example: for an arrangement `x 0, ..., x (n-1)` (indices modulo n), the run starting at
  `i` of length `l` with `1 ≤ l ≤ n - 1` sums to `x i + x (i+1) + ... + x (i+l-1)`, and the run
  of length `n` is the whole circle. The condition is that the set of all these sums is exactly
  `{1, ..., n^2 - n + 1}`.
* "sets of n positive integers": the `x i` are positive and pairwise distinct.
* `a(n) > 0` holds exactly when some such arrangement exists, so the conjecture is stated as:
  for `n > 2`, an arrangement exists if and only if `n - 1` is a prime power `p^e` with `e > 0`
  (Mathlib's `IsPrimePow`). (Data check: a(4) = 2, a(5) = 1, a(7) = 0 since 6 is not a prime
  power.)
-/

namespace OMA.S_oeis_a058241

/-- The sum of the run of `l` consecutive entries of the circular arrangement `x` of length `n`
starting at position `i`: positions are `0, ..., n - 1`, taken modulo `n`. -/
def runSum (n : ℕ) (x : ℕ → ℕ) (i l : ℕ) : ℕ :=
  ∑ t ∈ Finset.range l, x ((i + t) % n)

/-- `x 0, ..., x (n-1)` is a placement of `n` distinct positive integers on a circle whose run
sums (runs of length `1, ..., n - 1` from every position, and the whole circle) are exactly
`{1, ..., n^2 - n + 1}`. Values of `x` at positions `≥ n` play no role. -/
def IsGood (n : ℕ) (x : ℕ → ℕ) : Prop :=
  (∀ i, i < n → 0 < x i) ∧ Set.InjOn x (Set.Iio n) ∧
    ({s | ∃ i l, i < n ∧ 1 ≤ l ∧ l ≤ n - 1 ∧ s = runSum n x i l} ∪
        {∑ i ∈ Finset.range n, x i} : Set ℕ) =
      Set.Icc 1 (n ^ 2 - n + 1)

/-- For `n > 2`, such a placement exists if and only if `n - 1` is a prime power. -/
theorem main : ∀ n : ℕ, 2 < n → ((∃ x : ℕ → ℕ, IsGood n x) ↔ IsPrimePow (n - 1)) := by
  sorry

end OMA.S_oeis_a058241
