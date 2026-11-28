import Mathlib

/-!
# A375853: Triangle read by rows: T(n, k) = k*(n - k)*binomial(2*n+2, 2*k+1)/(4*n + 2) for 1 <= k <= n-1.

Source: https://oeis.org/A375853
Credit: @JeremyDevs

Formalizes the conjecture recorded in the FORMULA section of OEIS A375853:
Sum_{k>=0} T(n, k) = A002699(n-1) (conjectured by Bourn and Erickson).

Conventions:
* The triangle has rows n >= 2 and columns 1 <= k <= n-1 (offset 2; rows 2; 8, 8; 20, 56, 20;
  40, 216, 216, 40; ...), with T(n,k) = k*(n-k)*binomial(2n+2, 2k+1)/(4n+2). `T n k` is this
  quotient taken in the rationals, so nothing is assumed about the divisibility.
* Sum_{k>=0} T(n,k) is the sum of row n, i.e. the sum over the entries 1 <= k <= n-1 of the
  triangle, rendered as the sum over `Finset.Ico 1 n` (the formula would give 0 at k = 0 and k = n).
* A002699 (offset 0) is defined by A002699(n) = n*2^(2n-1), data 0, 2, 16, 96, 512, ...; it is only
  used at n-1 >= 1 here, where the exponent 2(n-1)-1 is a positive natural number.
* The identity is asserted for every row of the triangle, that is for every n >= 2.
-/

namespace OMA.S_oeis_a375853

/-- A375853: T(n,k) = k*(n-k)*binomial(2n+2, 2k+1)/(4n+2), for 1 <= k <= n-1. -/
def T (n k : ℕ) : ℚ :=
  (k : ℚ) * ((n : ℚ) - k) * ((2 * n + 2).choose (2 * k + 1) : ℚ) / (4 * n + 2)

/-- A002699 (offset 0): n*2^(2n-1). -/
def A002699 (n : ℕ) : ℚ := (n : ℚ) * 2 ^ (2 * n - 1)

/-- For every n >= 2 the sum of row n of the triangle is A002699(n-1). -/
theorem main : ∀ n : ℕ, 2 ≤ n → ∑ k ∈ Finset.Ico 1 n, T n k = A002699 (n - 1) := by
  sorry

end OMA.S_oeis_a375853
