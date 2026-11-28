import Mathlib

/-!
# A257388: Number of 4-Motzkin paths of length n with no level steps at odd level.

Source: https://oeis.org/A257388
Credit: @vivanpoddar

The sequence (offset 0) is 1, 4, 17, 72, 306, 1304, 5573, 23888, ... The entry records that the g.f. satisfies
A(x) = 1/(1 - 4*x) + x^2 * A(x)^2 (I. Gutkovskiy, Jun 30 2020), that is a(0) = 1, a(1) = 4 and
a(n+2) = 4^(n+2) + Sum_{k=0..n} a(k)*a(n-k). This recursion is used here as the definition
(it reproduces the data of the entry).

The conjecture (R. J. Mathar, Sep 24 2016) reads
(n+2)*a(n) + 8*(-n-1)*a(n-1) + 4*(3*n+1)*a(n-2) + 8*(2*n-3)*a(n-3) = 0.
It involves a(n-3), so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a257388

/-- A257388 (offset 0): a(0) = 1, a(1) = 4, a(n+2) = 4^(n+2) + Sum_{k=0..n} a(k)*a(n-k). -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 4
  | (n + 2) => 4 ^ (n + 2) + ∑ k : Fin (n + 1), a k * a (n - k)

/-- Mathar's conjectured recurrence for A257388. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 2) * a n + 8 * (-(n : ℤ) - 1) * a (n - 1) + 4 * (3 * (n : ℤ) + 1) * a (n - 2)
      + 8 * (2 * (n : ℤ) - 3) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a257388
