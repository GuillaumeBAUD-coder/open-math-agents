import Mathlib

/-!
# A116078: Column 0 of triangle A116077.

Source: https://oeis.org/A116078
Credit: @thatoneguy006

The conjecture stated here, from the entry:

  Conjecture: a(n) = 2^(2*n)*(Sum_{j=1..n+2-floor((n+3)/2)} (cos(j*Pi/(n+3)))^(2*n)).
  - L. Edson Jeffery, Nov 23 2013

Definition of the sequence (offset 0). The triangle A116077 is defined through an
anticommutator with the Catalan matrix; its column 0 has the g.f.
1/sqrt(1-4x) + 4x^2/(1+sqrt(1-4x))^2/(1-4x)^(3/2), with the closed form
a(n) = (n+3)*C(2n-1,n) - 2^(2n-1) for n >= 1 and a(0) = 1 (Vaclav Kotesovec, in the entry; it is
also the Mathematica program of the entry). That closed form is the definition used here, in ℝ.
It reproduces the data 1, 2, 7, 28, 117, 496, 2110, ...

The upper limit n+2-floor((n+3)/2) is computed in ℕ, where it is a nonnegative integer.
-/

namespace OMA.S_oeis_a116078

/-- A116078 by the closed form of the entry: `a 0 = 1` and `a n = (n+3) C(2n-1,n) - 2^(2n-1)`. -/
noncomputable def a (n : ℕ) : ℝ :=
  if n = 0 then 1 else ((n : ℝ) + 3) * ((2 * n - 1).choose n : ℝ) - 2 ^ (2 * n - 1)

/-- Jeffery's conjecture. -/
theorem main : ∀ n : ℕ,
    a n = 2 ^ (2 * n) *
      ∑ j ∈ Finset.Icc 1 (n + 2 - (n + 3) / 2),
        Real.cos ((j : ℝ) * Real.pi / ((n : ℝ) + 3)) ^ (2 * n) := by
  sorry

end OMA.S_oeis_a116078
