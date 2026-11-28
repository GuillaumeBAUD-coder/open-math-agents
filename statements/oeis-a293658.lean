import Mathlib

/-!
# A293658: Base-5 circular primes that are not base-5 repunits.

Source: https://oeis.org/A293658
Credit: @keiichisince1986-bot

A293658 lists, in increasing order and written in decimal, the base-5 circular primes that are
not base-5 repunits: `7, 11, 13, 17, 19, 23, 167, 211, 239, 283, 359, 431, 547, 571, 1069, 1249, …, 3121`.
The entry states: Conjecture: The sequence is finite, with 3121 being the last term (see A293142).

Conventions:
- A base-5 circular prime is a prime such that every number obtained by cyclically permuting its
  base-5 digits is prime (A293142). `IsCircularPrime n`: for every `k`, the number whose base-5
  digit list is the digit list of `n` rotated by `k` places is prime. Rotating by `0` gives `n`
  itself, so `n` is prime. `Nat.digits 5` lists the digits from the least significant one; the
  set of all rotations of a cyclic word does not depend on that direction.
- A rotation that brings a digit `0` to the leading position is read with the usual
  `Nat.ofDigits` convention. This choice never matters: if a number with at least two digits
  contains a `0`, the rotation that makes `0` the last digit is a positive multiple of `5`, which
  is not prime.
- The OEIS data, and the PARI program of the entry, exclude every number whose base-5 digits
  are all equal (`vecmin(digits(p, 5)) != vecmax(digits(p, 5))`): this removes the base-5
  repunits and also the one-digit primes. Among primes, the numbers with all base-5 digits equal
  are exactly the repunit primes with at least two digits and the primes below `5`, since a
  number `d · (11…1)` with `d ≥ 2` and at least two digits is composite. We follow the data:
  `HasEqualDigits n` excludes them. This changes the set only by finitely many one-digit numbers,
  so it does not affect the conjecture.
- The sequence is finite with last term `3121` exactly when `3121` is the greatest
  element of the set of terms: `IsGreatest S 3121` says that `3121 ∈ S` and every
  element of `S` is at most `3121`, so `S` is finite.
-/

namespace OMA.S_oeis_a293658

/-- Every cyclic permutation of the base-5 digits of `n` is a prime. -/
def IsCircularPrime (n : ℕ) : Prop :=
  ∀ k : ℕ, (Nat.ofDigits 5 ((Nat.digits 5 n).rotate k)).Prime

/-- All base-5 digits of `n` are equal (true for `n = 0`, whose digit list is empty). -/
def HasEqualDigits (n : ℕ) : Prop :=
  ∀ d ∈ Nat.digits 5 n, ∀ e ∈ Nat.digits 5 n, d = e

theorem main : IsGreatest {n : ℕ | IsCircularPrime n ∧ ¬ HasEqualDigits n} 3121 := by
  sorry

end OMA.S_oeis_a293658
