import Mathlib

/-!
# A273045: Fibonacci numbers with digits in nondecreasing order.

Source: https://oeis.org/A273045
Credit: @darealpandaboi

Conjecture: the sequence is finite, with 377 being the last term (verified up to Fibonacci(10^8)).

Translation notes.
* The decimal digits of m, read from the most significant one, are nondecreasing exactly when the
  little-endian list Nat.digits 10 m is antitone (nonincreasing): stated as List.Pairwise (· ≥ ·).
  For m = 0 the list is empty, so 0 is a term, as in the data.
* The last term 377 is stated as: every Fibonacci number with nondecreasing digits is at most
  377 (finiteness follows). The term 377 = Fib 14 itself has nondecreasing digits.
* This reproduces the listed data 0, 1, 1, 2, 3, 5, 8, 13, 34, 55, 89, 144, 233, 377 and finds no
  other term among the first 5000 Fibonacci numbers (checked by computer).
-/

namespace OMA.S_oeis_a273045

theorem main : ∀ n : ℕ, (Nat.digits 10 (Nat.fib n)).Pairwise (· ≥ ·) → Nat.fib n ≤ 377 := by
  sorry

end OMA.S_oeis_a273045
