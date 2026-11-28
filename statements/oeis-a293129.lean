import Mathlib

/-!
# A293129: the coefficients at indices 2^n + 1

Sources:
* OEIS Foundation, A293129, https://oeis.org/A293129.
* Sela Fried, Further proofs of conjectures from the OEIS, §3.7, Theorem 49,
  https://arxiv.org/html/2607.24832v1.

The logarithmic generating function L(X) is specified in the OEIS entry by
L(X) = -log(1-X) - ∑_{m ≠ 0} (X-X^(2m))^(2m)/(2m).
The term a(n) is (2n-1) times the coefficient of X^(2n-1) in L(X), with
offset 1. The definitions below use finite coefficient sums from the binomial
theorem for positive and negative m. For positive m, the first possible degree
is 2m, and for negative m it is 4m^2. The conjecture proved by Fried is
a(2^n+1) = 1 for all n ≥ 1.
-/

namespace OMA.S_oeis_a293129

open Finset

/-- Coefficient of X^e in the summand for a positive index m. -/
def positiveCoeff (m e : ℕ) : ℚ :=
  (∑ k ∈ range (2*m+1),
    if 2*m + k*(2*m-1) = e then (-1 : ℚ)^k * ((2*m).choose k : ℚ) else 0) / (2*m : ℚ)

/-- Coefficient of X^e in the summand for index -m, where m is positive. -/
def negativeCoeff (m e : ℕ) : ℚ :=
  (∑ k ∈ range (e+1),
    if 4*m^2 + k*(2*m+1) = e then ((2*m+k-1).choose k : ℚ) else 0) / (-(2*m : ℚ))

/-- The coefficient normalization defining A293129 at offset 1. -/
def a (n : ℕ) : ℚ :=
  let e := 2*n - 1
  1 - (e : ℚ) * ∑ m ∈ Icc 1 e, (positiveCoeff m e + negativeCoeff m e)

theorem main : ∀ n : ℕ, 1 ≤ n → a (2^n + 1) = 1 := by
  sorry

end OMA.S_oeis_a293129
