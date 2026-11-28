import Mathlib

/-!
# A217864: number of primes between floor(n log n) and (n+1) log(n+1)

Source: https://oeis.org/A217864 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A217864 (offset 1): number of prime numbers between floor(n*log(n)) and (n + 1)*log(n + 1);
data 0, 2, 2, 2, 0, 2, 1, 2, 2, 1, ...
(a(2) = 2: floor(2 log 2) = 1 and 3 log 3 = 3.29..., with the primes 2 and 3 in between.)

The entry records two conjectures:

  Conjecture: a(n) is unbounded.
  Conjecture: a(n)=0 infinitely often.

Both are stated here, as a conjunction.

Reading of the source:
* "between floor(n log n) and (n+1) log(n+1)" counts the primes `p` with
  `⌊n log n⌋ ≤ p ≤ (n+1) log(n+1)`, natural logarithm. The lower end is included: the data need
  it (a(3) = 2 counts 3 and 5 between ⌊3 log 3⌋ = 3 and 4 log 4 = 5.54...). For `n ≥ 1` the upper
  end is irrational or 0, so it is the same as counting up to `⌊(n+1) log(n+1)⌋`.
* "unbounded": for every bound `B` some term with `n ≥ 1` exceeds `B`; "a(n) = 0 infinitely
  often": for every `N` there is an `n ≥ N`, `n ≥ 1`, with `a n = 0`.
-/

namespace OMA.S_oeis_a217864

/-- A217864(n): the number of primes `p` with `⌊n log n⌋ ≤ p ≤ ⌊(n+1) log(n+1)⌋`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc ⌊(n : ℝ) * Real.log n⌋₊ ⌊((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)⌋₊).filter
    Nat.Prime).card

/-- The sequence is unbounded, and it takes the value 0 infinitely often. -/
theorem main :
    (∀ B : ℕ, ∃ n, 1 ≤ n ∧ B < a n) ∧ (∀ N : ℕ, ∃ n, N ≤ n ∧ 1 ≤ n ∧ a n = 0) := by
  sorry

end OMA.S_oeis_a217864
