import Mathlib

/-!
# OEIS A320907: row sums of the triangle A320906

Source: https://oeis.org/A320907
Credit: Sudharsan Rajendiran

A320907(n) is the n-th row sum of the triangle A320906, whose entries are
`T(n, k) = binomial(2n - k, k - 1) * hypergeom([2, 2, 1 - k], [1, 2(1 - k + n)], -1)` for `0 ≤ k ≤ n`.
Colin Barker conjectured (Oct 2018) the g.f. `x(1 - x)^2/((1 - 2x)^3 (1 - 3x + x^2))` and the
recurrence `a(n) = 9a(n-1) - 31a(n-2) + 50a(n-3) - 36a(n-4) + 8a(n-5)` for `n > 4`.

Conventions: we use the finite closed form of the hypergeometric definition given in OEIS
(Detlef Meya / Andrew Howroyd),
`T(n, k) = Σ_{j=0..2n+1-k} binomial(2n+1-k, 2n+2-2k+j) * binomial(j+2, 2)`, with offset 0, so
`a(n) = Σ_{k=0..n} T(n, k)` and `a(0) = 0`, matching the factor `x` of the g.f. The g.f. is stated as
an identity of formal power series over `ℚ` with the denominator multiplied across, and the
recurrence is stated over `ℤ` for all `n > 4`.
-/

namespace OMA.S_oeis_a320907

/-- The triangle A320906 in its finite binomial form:
`T(n, k) = Σ_{j=0..2n+1-k} binomial(2n+1-k, 2n+2-2k+j) * binomial(j+2, 2)`. -/
def T (n k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (2 * n + 2 - k), (2 * n + 1 - k).choose (2 * n + 2 - 2 * k + j) * (j + 2).choose 2

/-- A320907(n): the row sum `Σ_{k=0..n} T(n, k)` of the triangle A320906. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), T n k

open PowerSeries in
theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * ((1 - 2 * X) ^ 3 * (1 - 3 * X + X ^ 2)) = X * (1 - X) ^ 2 ∧
      ∀ n : ℕ, 4 < n → (a n : ℤ) = 9 * a (n - 1) - 31 * a (n - 2) + 50 * a (n - 3) - 36 * a (n - 4) +
        8 * a (n - 5) := by
  sorry

end OMA.S_oeis_a320907
