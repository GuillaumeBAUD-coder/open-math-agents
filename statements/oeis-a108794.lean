import Mathlib

/-!
# A108794: primes whose 10's complement is a semiprime.

Source: https://oeis.org/A108794
Credit: @cjchaffin

A prime `p` with `L` decimal digits belongs to the sequence when `10^L - p` is a
semiprime (example: `563` is prime and `10^3 - 563 = 437 = 19*23`). Twin prime terms
include `(149, 151)`, `(311, 313)`, `(419, 421)`, `(659, 661)`, …

Conjecture (on the OEIS page): there are infinitely many twin primes in this sequence.

Conventions: `L = (Nat.digits 10 p).length`; a semiprime is `Nat.IsSemiprime`
(exactly two prime factors counted with multiplicity, so squares of primes are
included). A twin prime pair is written as `p` and `p+2`, both in the sequence.
-/

namespace OMA.S_oeis_a108794

def IsA108794 (p : ℕ) : Prop :=
  p.Prime ∧ (10 ^ (Nat.digits 10 p).length - p).IsSemiprime

theorem main : {p : ℕ | IsA108794 p ∧ IsA108794 (p + 2)}.Infinite := by
  sorry

end OMA.S_oeis_a108794
