import Mathlib

/-!
# A083396: Least n such that n and 2k+n are both brilliant numbers.

Source: https://oeis.org/A083396
Credit: @gblacher2

Conjecture (comment in A083396): "for any k >= 1 there will always be a brilliant constellation
of the form {n, 2k+n} for some n. (True for all k <= 5000.)" That is, for every `k ≥ 1` there is
some `n` such that `n` and `n + 2k` are both brilliant numbers, so that A083396 is defined for
every `k ≥ 1`.

Conventions: brilliant numbers (A078972) are the semiprimes `p * q`, with `p` and `q` primes
(not necessarily distinct), whose two prime factors have the same number of decimal digits.

With this definition the least such `n` for `k = 1, …, 9` is 4, 6, 4, 6, 4, 9, 21, 9, 169, as in
the OEIS data (for example `169 = 13 * 13` and `169 + 18 = 187 = 11 * 17`).
-/

namespace OMA.S_oeis_a083396

/-- A078972: `m` is a brilliant number, a product of two primes with the same number of
decimal digits. -/
def IsBrilliant (m : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p * q ∧ (Nat.digits 10 p).length = (Nat.digits 10 q).length

/-- The conjecture: for every `k ≥ 1` some `n` has `n` and `n + 2k` both brilliant. -/
theorem main : ∀ k : ℕ, 1 ≤ k → ∃ n : ℕ, IsBrilliant n ∧ IsBrilliant (n + 2 * k) := by
  sorry

end OMA.S_oeis_a083396
