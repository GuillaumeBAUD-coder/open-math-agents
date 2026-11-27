import Mathlib

/-!
# Are there infinitely many Kummer primes?

Source: https://en.wikipedia.org/wiki/Euclid_number
Credit: @John-A-McMahon

Source statement (Wikipedia, *Euclid number*, linked from the list of unsolved problems): a
Kummer number (Euclid number of the second kind) is `p_n# - 1`, where `p_n#` is the `n`-th
primorial, the product of the first `n` primes; a Kummer prime is a prime Kummer number. It is
not known whether there are infinitely many. Stated here in its positive form.

Mathlib's `primorial p` is the product of all primes `≤ p`, so for the `n`-th prime `p_n` it is
exactly `p_n#`. Distinct primes `p` give distinct primorials, hence infinitely many primes `p`
with `primorial p - 1` prime is the same as infinitely many Kummer primes. (`2# - 1 = 1` is not
prime.)
-/

namespace OMA.S_wp_are_there_infinitely_many_kummer_primes

theorem main : {p : ℕ | p.Prime ∧ (primorial p - 1).Prime}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_kummer_primes
