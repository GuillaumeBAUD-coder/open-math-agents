import Mathlib

/-!
# A257290: Number of 3-Motzkin paths of length n with no level steps at even level.

Source: https://oeis.org/A257290
Credit: @vivanpoddar

The sequence (offset 0) is 1, 0, 1, 3, 11, 39, 140, 504, 1823, ... The entry gives the g.f.
(1 - 3*z - sqrt((1-3*z)*(1-3*z-4*z^2)))/(2*z^2), that is the power series A with A(0) = 1 and
z^2*A^2 - (1-3*z)*A + (1-3*z) = 0; equivalently a(0) = 1, a(1) = 0 and
a(n+2) = 3*a(n+1) + Sum_{k=0..n} a(k)*a(n-k). This recursion is used here as the definition
(it reproduces the data of the entry).

The conjecture (R. J. Mathar, Sep 24 2016) reads
(n+2)*a(n) + 3*(-2*n-1)*a(n-1) + 5*(n-1)*a(n-2) + 6*(2*n-5)*a(n-3) = 0.
It involves a(n-3), so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a257290

/-- A257290 (offset 0): a(0) = 1, a(1) = 0, a(n+2) = 3*a(n+1) + Sum_{k=0..n} a(k)*a(n-k). -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | (n + 2) => 3 * a (n + 1) + ∑ k : Fin (n + 1), a k * a (n - k)

/-- Mathar's conjectured recurrence for A257290. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 2) * a n + 3 * (-2 * (n : ℤ) - 1) * a (n - 1) + 5 * ((n : ℤ) - 1) * a (n - 2)
      + 6 * (2 * (n : ℤ) - 5) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a257290
