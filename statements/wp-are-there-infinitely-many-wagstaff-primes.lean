import Mathlib

/-!
# Infinitely many Wagstaff primes

A Wagstaff prime is a prime q = (2^p + 1) / 3 for an odd prime p.
The conjecture asks whether the set of these prime values q is infinite.
For odd p, the natural-number division by 3 is exact.

Source https://en.wikipedia.org/wiki/Wagstaff_prime
Credit @gwelb
-/

namespace OMA.S_wp_are_there_infinitely_many_wagstaff_primes

theorem main :
    Set.Infinite {q : ℕ | q.Prime ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ q = (2 ^ p + 1) / 3} := by
  sorry

end OMA.S_wp_are_there_infinitely_many_wagstaff_primes
