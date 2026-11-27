import Mathlib

/-!
# Are there infinitely many sexy primes?

Source: https://en.wikipedia.org/wiki/sexy_prime
Credit: @Andyi955

Sexy primes are prime numbers that differ from another prime by `6`: `p` and `p + 6` are both prime,
e.g. `5` and `11`. The sexy prime conjecture, a weaker analogue of the twin prime conjecture,
asserts that there exist infinitely many pairs of prime numbers that differ by `6`
(Wikipedia, Sexy primes, section Sexy prime conjecture). It is open.

## Encoding

* A pair of sexy primes is a pair `(p, p + 6)` with both entries prime; the conjecture says there are
  infinitely many such pairs. Since `p` determines the pair, this is stated as the set of lower
  members `p` being infinite. `p + 6` keeps the ordering (`p + 6 > p`), so pairs are not counted
  twice.
* `Nat.Prime` is Mathlib's prime predicate and `Set.Infinite` is infinitude of the set of lower
  members. Equivalently (as the source notes) the conjecture says the least gap occurring
  infinitely often between primes is at most `6`; the set form above is the source wording.
-/

namespace OMA.S_wp_are_there_infinitely_many_sexy_primes

/-- **Sexy prime conjecture**: infinitely many primes `p` have `p + 6` prime as well. -/
theorem main : {p : ℕ | p.Prime ∧ (p + 6).Prime}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_sexy_primes
