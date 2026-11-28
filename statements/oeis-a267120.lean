import Mathlib

/-!
# A267120: the Gaussian polynomial [2n+3,3]_q in powers of (1 + q^2)

Source: https://oeis.org/A267120

A267120 is the irregular triangle a(n, k), n >= 0, k = 0..g with g = 3n (row n has 3n+1 entries),
of the coefficients in the representation of the Gaussian polynomial [2n+3,3]_q as
`Sum_{k=0..g} a(n, k) * (1 + q^2)^k * q^(g - k)`. Data: 1, 0, -1, 1, 1, -1, 0, 5, -2, -4, 1, 1, ...

Conjecture (OEIS comment): more generally, for m >= 0 and n >= 0 the Gaussian polynomial
`[2n + m + 1 - (m mod 2), m]_q = Sum_{k=0..g(m;n)} a(m;n,k) * (1 + q^2)^k * q^(g(m;n) - k)`, where
`g(m;n) = m*n` if m is odd and `(2n + 1)*m/2` if m is even, and `a(m;n,k) = [x^k] G(m;n,x)` with
`G(m;n,x) = (d^m/dt^m) G(m;n,t,x) / m! |_(t=0)` and
`G(m;n,t,x) = (1 + t) * Product_{k=1..n+(m - (m mod 2))/2} (1 + t^2 + 2*t*T(k, x/2))`,
`T` the Chebyshev polynomials of the first kind. The present entry is the instance m = 3.

Formalization choices:
* The Gaussian polynomial `[N, m]_q` is defined by the q-Pascal rule `[N, 0]_q = 1`,
  `[0, m + 1]_q = 0`, `[N + 1, m + 1]_q = [N, m]_q + q^(m + 1) * [N, m + 1]_q`, as a polynomial in
  `q` with integer coefficients.
* `G(m;n,t,x)` is a polynomial in `t` whose coefficients are polynomials in `x` over `ℚ`
  (`T(k, x/2)` has non-integral coefficients); `T(k, x/2)` is `Polynomial.Chebyshev.T ℚ k`
  composed with `x/2`.
* The statement is the displayed identity for m = 3 and every n, with `a(m;n,k)` replaced by
  `[x^k] G(m;n,x)`, read in `ℚ[q]`.
-/

namespace OMA.S_oeis_a267120

open Polynomial

/-- The Gaussian polynomial `[N, m]_q`, by the q-Pascal rule. -/
noncomputable def gauss : ℕ → ℕ → ℤ[X]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | N + 1, m + 1 => gauss N m + X ^ (m + 1) * gauss N (m + 1)

/-- `T(k, x/2)`, the Chebyshev polynomial of the first kind evaluated at `x/2`. -/
noncomputable def chebHalf (k : ℕ) : ℚ[X] := (Chebyshev.T ℚ k).comp (C (1 / 2 : ℚ) * X)

/-- `G(m;n,t,x) = (1 + t) * Product_{k=1..n+(m - (m mod 2))/2} (1 + t^2 + 2*t*T(k, x/2))`,
a polynomial in `t` with coefficients in `ℚ[x]`. -/
noncomputable def bigG (m n : ℕ) : Polynomial ℚ[X] :=
  (1 + X) * ∏ k ∈ Finset.Icc 1 (n + (m - m % 2) / 2), (1 + X ^ 2 + 2 * X * C (chebHalf k))

/-- The row polynomial `G(m;n,x) = (d^m/dt^m) G(m;n,t,x) / m! |_(t=0)`. -/
noncomputable def rowPoly (m n : ℕ) : ℚ[X] :=
  C ((m.factorial : ℚ)⁻¹) * (derivative^[m] (bigG m n)).eval 0

/-- `g(m;n) = m*n` if `m` is odd and `(2n + 1)*m/2` if `m` is even. -/
def g (m n : ℕ) : ℕ := if m % 2 = 1 then m * n else (2 * n + 1) * m / 2

/-- The conjecture for m = 3: `[2n+3,3]_q = Sum_{k=0..g} ([x^k] G(3;n,x)) * (1 + q^2)^k * q^(g - k)`
with `g = g(3;n)`. -/
theorem main :
    ∀ n : ℕ, ∑ k ∈ Finset.range (g 3 n + 1),
        C ((rowPoly 3 n).coeff k) * (1 + X ^ 2) ^ k * X ^ (g 3 n - k) =
      (gauss (2 * n + 3) 3).map (Int.castRingHom ℚ) := by
  sorry

end OMA.S_oeis_a267120
