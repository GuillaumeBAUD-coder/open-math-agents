import Mathlib

/-!
# A131262: a(n) = least index k such that A130654(k) = n.

Source: https://oeis.org/A131262
Credit: @thatoneguy006

The conjecture stated here, from the entry:

  Conjecture: a(n) = Sigma(2^n)*EulerPhi(2^n) = 2^(2n) - Floor(2^n/2) = A062354(2^n).

(the entry adds that if it is true then a(5) = 1008), with offset 0: a(0..4) = 1, 3, 14, 60, 248.

Definitions.
* A092505(k) = A002430(k)/A046990(k), k >= 1, where A002430(k) is the numerator of the
  coefficient of x^(2k-1) in tan x and A046990(k) is the numerator of the coefficient of x^(2k)
  in log(1/cos x) (the Mathematica program of A130654).
  - The coefficient of x^(2k-1) in tan x is the classical
    (-1)^(k-1) 2^(2k) (2^(2k) - 1) B(2k) / (2k)!, with B Mathlib's `bernoulli` (only even indices
    occur, so the convention for B(1) is irrelevant).
  - Since d/dx log(1/cos x) = tan x, the coefficient of x^(2k) in log(1/cos x) is the
    coefficient of x^(2k-1) in tan x divided by 2k.
* A130654(k) is the exponent m with 2^m = A092505(k); the entry writes it as
  A007814(A092505(k)), the 2-adic valuation, which is what is used here (`padicValRat 2`).
  That A092505(k) is always a power of 2 is a separate conjecture of A130654 and is not assumed.
* a(n) is the least k >= 1 with A130654(k) = n. The conjecture is stated as: this least k
  exists and equals 2^(2n) - floor(2^n/2) (`IsLeast`), so it does not rely on an `sInf`.

Checks: with these definitions A130654(1..34) is 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 2, ...,
the data of A130654, and the least indices for n = 0..5 are 1, 3, 14, 60, 248, 1008.
-/

namespace OMA.S_oeis_a131262

/-- The coefficient of `x^(2k-1)` in the Taylor series of `tan x`, for `k ≥ 1`. -/
def tanCoeff (k : ℕ) : ℚ :=
  (-1) ^ (k - 1) * 2 ^ (2 * k) * (2 ^ (2 * k) - 1) * bernoulli (2 * k) / (2 * k).factorial

/-- The coefficient of `x^(2k)` in the Taylor series of `log (1 / cos x)`, for `k ≥ 1`. -/
def logSecCoeff (k : ℕ) : ℚ := tanCoeff k / (2 * k)

/-- A130654: the 2-adic valuation of `A092505 k = num(tanCoeff k) / num(logSecCoeff k)`. -/
def A130654 (k : ℕ) : ℤ :=
  padicValRat 2 (((tanCoeff k).num : ℚ) / ((logSecCoeff k).num : ℚ))

/-- The conjecture: the least `k ≥ 1` with `A130654 k = n` is `2^(2n) - floor(2^n/2)`. -/
theorem main : ∀ n : ℕ,
    IsLeast {k : ℕ | 1 ≤ k ∧ A130654 k = n} (2 ^ (2 * n) - 2 ^ n / 2) := by
  sorry

end OMA.S_oeis_a131262
