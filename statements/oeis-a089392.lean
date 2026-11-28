import Mathlib

/-!
# A089392: Magnanimous primes: primes with the property that inserting a "+" in any place between two digits yields a sum which is prime.

Source: https://oeis.org/A089392
Credit: @luciusacarr

The entry's comments record one conjecture: the sequence is infinite.
The source also notes (M. F. Hasler, Dec 25 2014) that, in contradiction to this conjecture, it is
rather expected that the sequence is finite (C. Rivera's Puzzle 401, G. Resta's web page). It is
stated here as the source's conjecture; it has not been refuted.

Reading of the source:
* A prime `p` with `k` decimal digits is a term if, for every way of inserting one `+` between two
  of its digits, the resulting sum is prime. Inserting the `+` after the first `k - i` digits
  (for `1 ≤ i < k`) gives the sum `p / 10^i + p % 10^i` of the leading part and the trailing `i`
  digits. The trailing part may have leading zeros (e.g. 101 gives 10 + 1 and 1 + 01, both prime),
  as in the entry's PARI program `divrem(n, 10^i)`.
* `p` itself must be prime (the original definition lists the unsplit number among the primes).
  One-digit primes 2, 3, 5, 7 are terms, the condition on splittings being vacuous.
* The conjecture is that the set of such primes is infinite.
-/

namespace OMA.S_oeis_a089392

/-- `p` is a magnanimous prime: `p` is prime and every split of its decimal digits into a nonempty
leading part and a nonempty trailing part has a prime sum. -/
def IsMagnanimousPrime (p : ℕ) : Prop :=
  p.Prime ∧ ∀ i : ℕ, 1 ≤ i → i < (Nat.digits 10 p).length → (p / 10 ^ i + p % 10 ^ i).Prime

theorem main : {p : ℕ | IsMagnanimousPrime p}.Infinite := by
  sorry

end OMA.S_oeis_a089392
