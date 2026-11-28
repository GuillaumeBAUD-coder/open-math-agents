import Mathlib

/-!
# A371798: a(n) = Sum_{k=0..floor(n/2)} (-1)^k * binomial(2*n-2*k-1,n-2*k).

Source: https://oeis.org/A371798
Credit: @Harsha0912

Conjecture (the only one in the entry; Stefano Spezia, Dec 27 2024, citing Elizalde et al.):
Conjectured g.f.: 1 + x*(4 - 10*x + 8*x^2)/(2 - 11*x + 14*x^2 - 8*x^3 + (2 - 3*x)*sqrt(1 - 4*x)).

Conventions:
* Offset 0. `a n = Sum_{k=0..floor(n/2)} (-1)^k * binomial(2n-2k-1, n-2k)`, computed in `ℤ`.
  For `n >= 1` the subtraction `2n - 2k - 1` never truncates (`k <= n/2`); at `n = 0` the single
  term is `binomial(0, 0) = 1` in `ℕ` (OEIS a(0) = 1; `binomial(-1, 0) = 1` as well).
* `sqrt(1 - 4x)` is the power series `S` over `ℚ` with `S^2 = 1 - 4x` and constant term `1`; the
  statement quantifies over every such `S` (there is exactly one).
* With `D = 2 - 11x + 14x^2 - 8x^3 + (2 - 3x) S` (constant term `4`, so invertible), the claim
  `A = 1 + x N / D` is stated cleared of its denominator: `A * D = D + x N`.
-/

namespace OMA.S_oeis_a371798

open PowerSeries

/-- A371798: `a(n) = Sum_{k=0..floor(n/2)} (-1)^k * binomial(2n-2k-1, n-2k)`. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n / 2 + 1), (-1) ^ k * ((2 * n - 2 * k - 1).choose (n - 2 * k) : ℤ)

/-- Spezia's conjectured algebraic generating function, cleared of its denominator. -/
theorem main : ∀ S : PowerSeries ℚ, S ^ 2 = 1 - 4 * X → constantCoeff S = 1 →
    PowerSeries.mk (fun n => (a n : ℚ)) *
        (2 - 11 * X + 14 * X ^ 2 - 8 * X ^ 3 + (2 - 3 * X) * S) =
      (2 - 11 * X + 14 * X ^ 2 - 8 * X ^ 3 + (2 - 3 * X) * S) +
        X * (4 - 10 * X + 8 * X ^ 2) := by
  sorry

end OMA.S_oeis_a371798

