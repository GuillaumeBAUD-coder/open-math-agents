import Mathlib

/-!
# A257178: Number of 3-Motzkin paths of length n with no level steps at odd level.

Source: https://oeis.org/A257178
Credit: @vivanpoddar

The sequence (offset 0) is 1, 3, 10, 33, 110, 369, 1247, 4245, ... The entry records that the g.f. satisfies
A(x) = 1/(1 - 3*x) + x^2 * A(x)^2 (I. Gutkovskiy, Jun 30 2020), that is a(0) = 1, a(1) = 3 and
a(n+2) = 3^(n+2) + Sum_{k=0..n} a(k)*a(n-k). This recursion is used here as the definition
(it reproduces the data of the entry).

The conjecture (R. J. Mathar, Sep 24 2016) reads
(n+2)*a(n) + 6*(-n-1)*a(n-1) + (5*n+4)*a(n-2) + 6*(2*n-3)*a(n-3) = 0.
It involves a(n-3), so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a257178

/-- A257178 (offset 0): a(0) = 1, a(1) = 3, a(n+2) = 3^(n+2) + Sum_{k=0..n} a(k)*a(n-k). -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | (n + 2) => 3 ^ (n + 2) + ∑ k : Fin (n + 1), a k * a (n - k)

/-- Mathar's conjectured recurrence for A257178. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 2) * a n + 6 * (-(n : ℤ) - 1) * a (n - 1) + (5 * (n : ℤ) + 4) * a (n - 2)
      + 6 * (2 * (n : ℤ) - 3) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a257178
