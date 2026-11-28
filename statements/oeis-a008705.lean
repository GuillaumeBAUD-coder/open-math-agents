import Mathlib

/-!
# OEIS A008705: two supercongruences for the coefficient of x^n in (Product (1-x^m))^n

Source: https://oeis.org/A008705
Credit: @sntntHb

A008705: `a(n)` is the coefficient of `x^n` in `(Product_{m=1..n} (1 - x^m))^n`.

Peter Bala (Apr 18 2023) conjectures: the supercongruences `a(p) == -1 - p (mod p^2)` and
`a(2*p) == p - 1 (mod p^2)` hold for all primes `p >= 3`.

Formalized: `a n` is the coefficient of `X^n` in the integer polynomial
`(Product_{m=1..n} (1 - X^m))^n`, and `main` states that for every prime `p >= 3` both
`a p == -1 - p` and `a (2*p) == p - 1` hold modulo `p^2` in the integers.
-/

namespace OMA.S_oeis_a008705

open Polynomial

/-- `a(n)` = coefficient of `x^n` in `(Product_{m=1..n} (1 - x^m))^n`. -/
noncomputable def a (n : ℕ) : ℤ :=
  ((∏ m ∈ Finset.Icc 1 n, (1 - X ^ m : ℤ[X])) ^ n).coeff n

theorem main :
    ∀ p : ℕ, p.Prime → 3 ≤ p →
      a p ≡ -1 - (p : ℤ) [ZMOD (p : ℤ) ^ 2] ∧
      a (2 * p) ≡ (p : ℤ) - 1 [ZMOD (p : ℤ) ^ 2] := by
  sorry

end OMA.S_oeis_a008705
