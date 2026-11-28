import Mathlib

/-!
# When is a number like "ddd...ddd"+1 (where d is a digit) a perfect square or a prime?

Source: https://math.stackexchange.com/questions/548549 (question by Mark S.)

The question asks: for which integers `d ∈ [1, 8]` and `n ≥ 1` is
`1 + d * ∑_{j=0}^{n} 10^j = 1 + d * (10^(n+1) - 1) / 9` a perfect square, and which are prime?
The author adds that he does not know how to approach "are there infinitely many primes for
some `d`?", and hopes the "no squares" part can be proved.

Reading choices (for the reviewer):
* `ddd...ddd + 1` is the number `1 + d * ∑_{j=0}^{n} 10^j` written with the source's own formula,
  with the source's ranges `1 ≤ d ≤ 8` and `1 ≤ n`. The number has `n + 1` digits.
* The question has two parts, and the statement is their conjunction:
  1. the squares part, stated as the expected answer "never a perfect square". A partial
     answer on the page proves this; it stays in because the source asks it;
  2. the primes part. This is the open question the author names: for some `d` in the range,
     there are infinitely many `n` that give a prime.
* `IsSquare` and `Nat.Prime` are Mathlib's definitions.

Numeric sanity checks (the `example`s below; all values match the source's list):
`ddd 2 1 = 23`, `ddd 6 5 = 666667`, `ddd 8 1 = 89`, `ddd 3 1 = 34`, `ddd 1 3 = 1112`;
23, 223, 67 and 89 are prime, and 34 = 2 * 17 is not prime.
-/

namespace OMA.S_mse_548549

open Finset

/-- The number `ddd...ddd + 1` with `n + 1` copies of the digit `d`: `1 + d * ∑_{j=0}^{n} 10^j`. -/
def ddd (d n : ℕ) : ℕ := 1 + d * ∑ j ∈ range (n + 1), 10 ^ j

example : ddd 2 1 = 23 := by decide
example : ddd 6 5 = 666667 := by decide
example : ddd 8 1 = 89 := by decide
example : ddd 3 1 = 34 := by decide
example : ddd 1 3 = 1112 := by decide
example : ddd 2 2 = 223 := by decide
example : (ddd 2 1).Prime := by norm_num [ddd, Finset.sum_range_succ]
example : (ddd 2 2).Prime := by norm_num [ddd, Finset.sum_range_succ]
example : (ddd 6 1).Prime := by norm_num [ddd, Finset.sum_range_succ]
example : (ddd 8 1).Prime := by norm_num [ddd, Finset.sum_range_succ]
example : ¬ (ddd 3 1).Prime := by norm_num [ddd, Finset.sum_range_succ]
/-- The source's closed form `1 + d * (10^(n+1) - 1) / 9` agrees with the digit sum. -/
example : ∀ d ∈ Icc 1 8, ∀ n ∈ range 6, ddd d n = 1 + d * (10 ^ (n + 1) - 1) / 9 := by decide

theorem main :
    (∀ d n : ℕ, 1 ≤ d → d ≤ 8 → 1 ≤ n → ¬ IsSquare (ddd d n)) ∧
    (∃ d : ℕ, 1 ≤ d ∧ d ≤ 8 ∧ {n : ℕ | 1 ≤ n ∧ (ddd d n).Prime}.Infinite) := by
  sorry

end OMA.S_mse_548549
