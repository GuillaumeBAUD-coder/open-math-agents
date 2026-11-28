import Mathlib

/-!
# A242223: primitive prime divisors of harmonic numbers

Source: https://oeis.org/A242223
Credit: @coleman415

The sequence (Zhi-Wei Sun) is: `a(n)` = least prime `p` such that `H(n) == 0 (mod p)` but
`H(k) == 0 (mod p)` for no `0 < k < n`, or `1` if such a prime `p` does not exist, where
`H(n) = sum_{k=1..n} 1/k` is the `n`-th harmonic number.
The entry records: *Conjecture: a(n) is prime except for n = 1, 7.*

So the conjecture says: for `n ≥ 1`, a prime `p` with `H(n) ≡ 0 (mod p)` and `H(k) ≢ 0 (mod p)`
for all `0 < k < n` exists exactly when `n` is not 1 or 7.

Conventions:
- A rational number `x` is `≡ 0 (mod p)` when `p` divides the numerator of `x` in lowest terms
  (the denominator is then prime to `p`). Example from the entry: `H(4) = 25/12 ≡ 0 (mod 5)`.
- `harmonic n` is Mathlib's `H(n)` as a rational number.
-/

namespace OMA.S_oeis_a242223

/-- The rational number `x` is congruent to 0 modulo `p`: `p` divides its reduced numerator. -/
def RatModZero (x : ℚ) (p : ℕ) : Prop := (p : ℤ) ∣ x.num

/-- `p` is a primitive prime divisor of the harmonic number `H(n)`. -/
def IsPrimitivePrime (n p : ℕ) : Prop :=
  p.Prime ∧ RatModZero (harmonic n) p ∧ ∀ k : ℕ, 0 < k → k < n → ¬ RatModZero (harmonic k) p

/-- The conjecture of OEIS A242223. -/
theorem main : ∀ n : ℕ, 0 < n → ((∃ p : ℕ, IsPrimitivePrime n p) ↔ (n ≠ 1 ∧ n ≠ 7)) := by
  sorry

end OMA.S_oeis_a242223
