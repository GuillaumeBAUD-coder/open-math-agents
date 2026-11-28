import Mathlib

/-!
# A364421: For n >= 3, r >= 0, y an integer, a(n) is the number of integral solutions to the elliptic equation y^2 = n^3 + n^2 + 2*r*n + r^2.

Source: https://oeis.org/A364421
Credit: @xor2k

Thomas Scheuerle (Sep 04 2023), in the comments of A364421:
  Conjecture: a(p^3) = 5 if p is an odd prime.
  Conjecture: a(2*p^2) = 7 if p is an odd prime.

Only these two conjectures are stated here, joined by a conjunction. The other conjectures of the
same comment (a(A190300(n)) = 3, a(A196226(n)) = 4, a(prime(n)^prime(n)) = A245685(n - 1) - 1)
are not formalized.

Conventions:
* `a n` is the number of integers r ≥ 0 for which n^3 + n^2 + 2*r*n + r^2 is a perfect square,
  as a `Set.ncard` of a set of natural numbers r (the set is finite for n ≥ 1). A solution is
  counted once per r, that is, with y ≥ 0 (y and -y are not counted twice; y = 0 does not occur
  for n ≥ 1). This is the reading fixed by the formula in the entry (Robin Visser): a(n) is the
  number of divisors d of n^3 such that (d - n^3/d)/2 - n is a nonnegative integer; it is also the
  only reading under which the odd values 5 and 7 of the conjectures are possible.
* The sequence has offset 3 (n ≥ 3). The arguments p^3 ≥ 27 and 2*p^2 ≥ 18 of the conjectures are
  in that range, so the definition is not used outside the range of the entry.
* p ranges over the odd primes, as natural numbers.

Numerical check: a Python copy of the definition gives, for n = 3, 4, 5, ...:
2, 2, 2, 3, 2, 4, 3, 4, 2, 8, 2, 4, 8, 5, 2, 7, 2, 9, 8, 4, 2, 15, 3, 4, 5, 10, 2, 15, ...
and the same values come out of the divisor formula of the entry. The DATA field of the entry was
not available offline for comparison. Also a(27) = a(125) = 5 and a(18) = a(50) = a(98) = 7.
-/

namespace OMA.S_oeis_a364421

/-- A364421: the number of r ≥ 0 such that y^2 = n^3 + n^2 + 2*r*n + r^2 has a solution y. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {r : ℕ | ∃ y : ℕ, y ^ 2 = n ^ 3 + n ^ 2 + 2 * r * n + r ^ 2}

/-- Scheuerle's conjectures: a(p^3) = 5 and a(2*p^2) = 7 for every odd prime p. -/
theorem main : (∀ p : ℕ, p.Prime → Odd p → a (p ^ 3) = 5) ∧
    (∀ p : ℕ, p.Prime → Odd p → a (2 * p ^ 2) = 7) := by
  sorry

end OMA.S_oeis_a364421
