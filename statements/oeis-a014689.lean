import Mathlib

/-!
# A014689: residues of prime(n) - n and prime(n) + n

Source: https://oeis.org/A014689
Credit: @jagraj28

A014689 is `a(n) = prime(n) - n` for `n ≥ 1`. The entry records a conjecture of Zhi-Wei Sun
(2013): each residue class contains infinitely many terms of this sequence. Similarly, for any
integers `m > 0` and `r`, `prime(n) + n ≡ r (mod m)` for infinitely many positive integers `n`.

`main` is the conjunction of the two parts, for all integers `m > 0` and `r`:
1. `prime(n) - n ≡ r (mod m)` for infinitely many `n ≥ 1`;
2. `prime(n) + n ≡ r (mod m)` for infinitely many `n ≥ 1`.

Conventions: `prime(n)` is the `n`-th prime with `prime(1) = 2`, in Mathlib
`Nat.nth Nat.Prime (n - 1)`; the congruences are in `ℤ`. Part 1 counts indices `n`; since
`a(n)` is nondecreasing and takes each value at most twice, this is the same as infinitely many
distinct terms in each residue class.
-/

namespace OMA.S_oeis_a014689

/-- `prime n`: the `n`-th prime, with `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- Sun's conjecture in OEIS A014689. -/
theorem main : ∀ m : ℤ, 0 < m → ∀ r : ℤ,
    {n : ℕ | 1 ≤ n ∧ (prime n : ℤ) - n ≡ r [ZMOD m]}.Infinite ∧
    {n : ℕ | 1 ≤ n ∧ (prime n : ℤ) + n ≡ r [ZMOD m]}.Infinite := by
  sorry

end OMA.S_oeis_a014689
