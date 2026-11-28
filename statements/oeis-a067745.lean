import Mathlib

/-!
# OEIS A067745: a numerator equal to the odd part of 3n - 2

Source: https://oeis.org/A067745
Credit: @SudharsanAnimations

`A067745(n)` is the numerator of `(3n - 2) / (n^(2n-1) (2n - 1) 4^(n-1))`. The entry conjectures that
it is the odd part of `3n - 2`, and records the proof (Robert Israel): `gcd(3n - 2, 2n - 1) = 1`,
`gcd(3n - 2, n) ∈ {1, 2}`, and the power of `2` dividing `3n - 2` is small enough to cancel into
`4^(n-1)`. We state this proved result for all `n ≥ 1` (offset `1`).

Conventions: the fraction is taken in `ℚ` and `Rat.num` is its reduced numerator; the odd part of
`m` is `m / 2^{v₂(m)}`, with `v₂(m) = m.factorization 2`.
-/

namespace OMA.S_oeis_a067745

/-- The odd part of `m`: `m / 2^{v₂(m)}`. -/
def oddPart (m : ℕ) : ℕ := m / 2 ^ (m.factorization 2)

theorem main : ∀ n : ℕ, 1 ≤ n →
    (((3 * n - 2 : ℕ) : ℚ) / ((n : ℚ) ^ (2 * n - 1) * ((2 * n - 1 : ℕ) : ℚ) * 4 ^ (n - 1))).num
      = (oddPart (3 * n - 2) : ℤ) := by
  sorry

end OMA.S_oeis_a067745
