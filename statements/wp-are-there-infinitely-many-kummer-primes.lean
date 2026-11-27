import Mathlib

/-!
# Are there infinitely many Kummer primes?

Source: https://en.wikipedia.org/wiki/Euclid_number#Generalization

A Kummer number (a Euclid number of the second kind) is `E_n = p_n# - 1`, where `p_n#` is the
product of the first `n` primes. The source asks whether infinitely many of these numbers are prime.
Here `n` starts at `0`, so the sequence is `1, 5, 29, 209, ...`, matching the source list.
-/

namespace OMA.S_wp_are_there_infinitely_many_kummer_primes

/-- The `n`-th Kummer number `p_n# - 1`, with `Nat.nth Nat.Prime n` the `n`-th prime. -/
noncomputable def kummerNumber (n : ℕ) : ℕ :=
  (∏ p ∈ Finset.filter Nat.Prime (Finset.range (Nat.nth Nat.Prime n + 1)), p) - 1

theorem main : {k : ℕ | k.Prime ∧ ∃ n, k = kummerNumber n}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_kummer_primes
