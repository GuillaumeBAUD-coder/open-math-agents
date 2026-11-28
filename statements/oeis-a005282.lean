import Mathlib

/-!
# A005282: growth of the Mian-Chowla sequence

Source: https://oeis.org/A005282
Credit: @majdi19

A005282 (Mian-Chowla sequence, a B_2 sequence): `a(1) = 1`; for `n > 1`, `a(n)` is the smallest
number greater than `a(n-1)` such that the pairwise sums of elements are all distinct.
It begins 1, 2, 4, 8, 13, 21, 31, 45, 66, 81, ...

The OEIS comment by Thomas Ordowski (Sep 19 2014) reads:

  Known estimate: n^2/2 + O(n) < a(n) < n^3/6 + O(n^2). Conjecture: a(n) ~ n^3 / log(n)^2.

Conventions.
* The sequence is indexed from `1`, as in the OEIS; the value `a 0` is irrelevant.
* Pairwise sums are `a(i) + a(j)` with `i ≤ j`, including `i = j` (the B_2 condition).
  Including `i = j` is forced by the data: without it `a(3)` would be `3`, but `a(3) = 4`.
* `IsMianChowla a` says that `a` satisfies the defining recursion. It determines `a(n)` for
  every `n ≥ 1` (by induction), so the statement is about the Mian-Chowla sequence itself.
* `~[atTop]` is `Asymptotics.IsEquivalent`: `a(n) / (n^3 / log(n)^2) → 1`.
-/

namespace OMA.S_oeis_a005282

open Asymptotics Filter

/-- The terms `a 1, …, a n` have pairwise distinct sums `a i + a j` (`i ≤ j`). -/
def SumsDistinct (a : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ i j k l : ℕ, 1 ≤ i → i ≤ j → j ≤ n → 1 ≤ k → k ≤ l → l ≤ n →
    a i + a j = a k + a l → i = k ∧ j = l

/-- `a` is the Mian-Chowla sequence: `a 1 = 1` and each `a (n + 1)` is the least number
greater than `a n` keeping all pairwise sums of `a 1, …, a (n + 1)` distinct. -/
def IsMianChowla (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ ∀ n : ℕ, 1 ≤ n →
    IsLeast {m : ℕ | a n < m ∧ SumsDistinct (Function.update a (n + 1) m) (n + 1)} (a (n + 1))

/-- Ordowski's conjecture: `a(n) ~ n^3 / log(n)^2`. -/
theorem main : ∀ a : ℕ → ℕ, IsMianChowla a →
    (fun n : ℕ => (a n : ℝ)) ~[atTop] (fun n : ℕ => (n : ℝ) ^ 3 / Real.log (n : ℝ) ^ 2) := by
  sorry

end OMA.S_oeis_a005282
