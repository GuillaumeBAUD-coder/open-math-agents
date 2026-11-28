import Mathlib

/-!
# A293662: Base-9 circular primes that are not base-9 repunits.

Source: https://oeis.org/A293662
Credit: @keiichisince1986-bot

A293662 lists, in increasing order and written in decimal, the base-9 circular primes that are
not base-9 repunits: `11, 13, 17, 19, 23, 37, 43, 47, 67, 71, 73, 79, 101, 149, 173, …`.
The entry states: Conjecture: The sequence is finite.

Conventions:
- A base-9 circular prime is a prime such that every number obtained by cyclically permuting its
  base-9 digits is prime (A293142). `IsCircularPrime n`: for every `k`, the number whose base-9
  digit list is the digit list of `n` rotated by `k` places is prime. Rotating by `0` gives `n`
  itself, so `n` is prime. `Nat.digits 9` lists the digits from the least significant one; the
  set of all rotations of a cyclic word does not depend on that direction.
- A rotation that brings a digit `0` to the leading position is read with the usual
  `Nat.ofDigits` convention. This choice never matters: if a number with at least two digits
  contains a `0`, the rotation that makes `0` the last digit is a positive multiple of `9`, which
  is not prime.
- The OEIS data, and the PARI program of the entry, exclude every number whose base-9 digits
  are all equal (`vecmin(digits(p, 9)) != vecmax(digits(p, 9))`): this removes the base-9
  repunits and also the one-digit primes. Among primes, the numbers with all base-9 digits equal
  are exactly the repunit primes with at least two digits and the primes below `9`, since a
  number `d · (11…1)` with `d ≥ 2` and at least two digits is composite. We follow the data:
  `HasEqualDigits n` excludes them. This changes the set only by finitely many one-digit numbers,
  so it does not affect the conjecture.
- The conjecture says that the set of terms is finite.
-/

namespace OMA.S_oeis_a293662

/-- Every cyclic permutation of the base-9 digits of `n` is a prime. -/
def IsCircularPrime (n : ℕ) : Prop :=
  ∀ k : ℕ, (Nat.ofDigits 9 ((Nat.digits 9 n).rotate k)).Prime

/-- All base-9 digits of `n` are equal (true for `n = 0`, whose digit list is empty). -/
def HasEqualDigits (n : ℕ) : Prop :=
  ∀ d ∈ Nat.digits 9 n, ∀ e ∈ Nat.digits 9 n, d = e

theorem main : {n : ℕ | IsCircularPrime n ∧ ¬ HasEqualDigits n}.Finite := by
  sorry

end OMA.S_oeis_a293662
