import Mathlib

/-!
# A108144: `n` such that `(n-1)/P(n-1)` is a power of two greater than 1.

Source: https://oeis.org/A108144
Credit: @cjchaffin

Here `P(m)` is the largest prime factor of `m`. Example: `1537` is a term because
`1536 / 3 = 512 = 2^9`.

Conjecture (on the OEIS page): there are infinitely many primes and infinitely many
semiprimes in this sequence.

Conventions: offset 1; `P(m) = m.primeFactors.sup id` (and `n ≥ 2`, so `n-1 ≥ 1` has
a prime factor whenever the displayed quotient is defined). A power of two greater
than 1 is `2^k` for some `k ≥ 1`. Semiprimes are `Nat.IsSemiprime`.
-/

namespace OMA.S_oeis_a108144

def largestPrimeFactor (m : ℕ) : ℕ := m.primeFactors.sup id

def IsA108144 (n : ℕ) : Prop :=
  2 ≤ n ∧ ∃ k : ℕ, 1 ≤ k ∧ n - 1 = largestPrimeFactor (n - 1) * 2 ^ k

theorem main :
    {n : ℕ | n.Prime ∧ IsA108144 n}.Infinite ∧
      {n : ℕ | n.IsSemiprime ∧ IsA108144 n}.Infinite := by
  sorry

end OMA.S_oeis_a108144
