import Mathlib

/-!
# A184878: Third column (negated) of triangle in A182971

Source: https://oeis.org/A184878
Credit: @jagong-cmu

Formalizes R. J. Mathar's OEIS A184878 conjecture (May 18 2026), offset 1:
`Conjectures: G.f.: x^5*(225+54*x+x^2)/(x-1)^10 .`
`a(n) = n *(n-1) *(n-2) *(n-3) *(n-4) *(n+2) *(n+1) *(35*n^2+182*n+240) /45360.`

Conventions:
* A182971 is the triangle of coefficients of `Q(n) = (x-n^2)*(x-(n-2)^2)*...*(x-(1 or 2)^2)`,
  highest powers first. Here `Q(n)` is the product over `0 <= i < floor((n+1)/2)` of
  `x - (n-2*i)^2` in `ℤ[x]`; it has degree `d = floor((n+1)/2)` (and `Q(0) = 1`).
* Row `n` of the triangle is `T(n,k) = [x^(d-k)] Q(n)` for `0 <= k <= d`. The columns are
  numbered from `k = 0` (the column of `1`s), and the third column is `k = 3`: this matches the
  OEIS data, e.g. `Q(5) = (x-1)(x-9)(x-25) = x^3 - 35x^2 + 259x - 225` and `a(5) = 225`.
  Where the row is too short (`k > d`) the entry is `0`, which gives the OEIS terms
  `a(1) = ... = a(4) = 0`.
* `a(n) = -T(n,3)` in `ℤ`. The closed form is stated in `ℚ` (so `n - 1`, ..., `n - 4` and the
  division by `45360` are the usual ones) for every `n >= 1` (the offset is 1).
* The closed form is a polynomial of degree 9 in `n` that vanishes at `n = 0, ..., 4`, and the
  stated g.f. is the g.f. of exactly this polynomial, so the closed form states both conjectures.
-/

namespace OMA.S_oeis_a184878

open Polynomial

/-- `Q(n) = (x-n^2)*(x-(n-2)^2)*...*(x-(1 or 2)^2)`. -/
noncomputable def Q (n : ℕ) : ℤ[X] :=
  ∏ i ∈ Finset.range ((n + 1) / 2), (X - C (((n - 2 * i : ℕ) : ℤ) ^ 2))

/-- Triangle A182971: `T(n,k)` is the coefficient of `x^(d-k)` in `Q(n)`, `d = deg Q(n)`. -/
noncomputable def T (n k : ℕ) : ℤ :=
  if k ≤ (n + 1) / 2 then (Q n).coeff ((n + 1) / 2 - k) else 0

/-- `a(n) = -T(n,3)`. -/
noncomputable def a (n : ℕ) : ℤ := -T n 3

/-- For every `n >= 1`:
`a(n) = n(n-1)(n-2)(n-3)(n-4)(n+2)(n+1)(35n^2+182n+240)/45360`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (a n : ℚ) = (n : ℚ) * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n + 2) * (n + 1) *
      (35 * n ^ 2 + 182 * n + 240) / 45360 := by
  sorry

end OMA.S_oeis_a184878
