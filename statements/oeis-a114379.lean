import Mathlib

/-!
# A114379: sums of the `p`-th through `q`-th primes, where `p` and `q` are twin primes.

Source: https://oeis.org/A114379
Credit: @cjchaffin

Example: `3` and `5` are a twin prime pair, and `prime(3)+prime(4)+prime(5) = 5+7+11 = 23`
is the first term. In general a twin prime pair `(p, p+2)` contributes
`prime(p)+prime(p+1)+prime(p+2)`.

Conjecture (on the OEIS page): the number of terms is infinite.

Conventions: offset 1; `prime(n)` is the `n`-th prime with `prime(1) = 2`. Twin primes
are pairs of primes differing by 2 (so `(2, 3)` is not a twin pair, matching the
example that begins at `(3, 5)`).
-/

namespace OMA.S_oeis_a114379

/-- The `n`-th prime with `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

theorem main :
    {s : ℕ | ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧
        s = prime p + prime (p + 1) + prime (p + 2)}.Infinite := by
  sorry

end OMA.S_oeis_a114379
