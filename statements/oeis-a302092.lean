import Mathlib

/-!
# A302092: Bell(n) times Bell(n) written backwards (only two semiprimes)

Source: https://oeis.org/A302092 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A302092 (offset 0): product of the n-th Bell number and the n-th Bell number written backwards,
a(n) = A000110(n) * A004098(n); data 1, 1, 4, 25, 765, 1300, 61306, ...
(a(4) = 765 because Bell(4) = 15 and 15 * 51 = 765; a(5) = 52 * 25 = 1300.)

The entry records:

  Conjecture: in this sequence only two semiprimes (4,25).

Reading of the source:
* Bell numbers are Mathlib's `Nat.bell` (Bell(0) = 1, Bell(4) = 15, Bell(5) = 52).
* "written backwards" reverses the base-10 digits (A004098): `Nat.digits 10` lists the digits
  least significant first, so `Nat.ofDigits 10 (Nat.digits 10 b).reverse` is `b` reversed
  (15 -> 51, 52 -> 25; a trailing 0 of `b` is dropped, as in A004098: 1300 -> 31).
* A semiprime is a product of two primes, not necessarily distinct: a number with exactly two
  prime factors counted with multiplicity (`Nat.primeFactorsList` has length 2).
* "only two semiprimes (4,25)": the semiprime values of the sequence are exactly 4 and 25
  (a(2) = 2 * 2 and a(3) = 5 * 5).
-/

namespace OMA.S_oeis_a302092

/-- The base-10 digits of `b` in reverse order, read as a number (A004098 at a Bell number). -/
def reverseDigits (b : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 b).reverse

/-- A302092(n) = Bell(n) * (Bell(n) written backwards). -/
def a (n : ℕ) : ℕ := n.bell * reverseDigits n.bell

/-- `x` is a semiprime: exactly two prime factors, counted with multiplicity. -/
def IsSemiprime (x : ℕ) : Prop := x.primeFactorsList.length = 2

/-- The only semiprime terms of the sequence are 4 and 25. -/
theorem main : {x : ℕ | (∃ n, a n = x) ∧ IsSemiprime x} = {4, 25} := by
  sorry

end OMA.S_oeis_a302092
