import Mathlib

/-!
# A108518: a(n) is the smallest natural number m such that (10^n)! + m is prime.

Source: https://oeis.org/A108518
Credit: @gblacher2

Conjecture (comment in A108518): "All terms are noncomposite numbers", that is, for every
`n ≥ 0` the least `m` with `(10^n)! + m` prime is `1` or a prime.

Conventions:
* the offset of A108518 is 0, so `n` ranges over all natural numbers;
* `m` ranges over the natural numbers. Allowing `m = 0` changes nothing, since `(10^n)! + 0` is
  never prime (`1` for `n = 0`, and an even number larger than `2` for `n ≥ 1`);
* "noncomposite" (A008578) means `1` or a prime.

With this definition `a(0) = 1` and `a(1) = 11`, and the next terms are 229 and 1283, as in the
OEIS data `1, 11, 229, 1283, 44159`.
-/

namespace OMA.S_oeis_a108518

open Nat

/-- A108518: the smallest natural number `m` such that `(10^n)! + m` is prime. The set is
nonempty because there are infinitely many primes, so its infimum is its least element. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | ((10 ^ n)! + m).Prime}

/-- The conjecture: every term of A108518 is noncomposite, that is, `1` or a prime. -/
theorem main : ∀ n : ℕ, a n = 1 ∨ (a n).Prime := by
  sorry

end OMA.S_oeis_a108518
