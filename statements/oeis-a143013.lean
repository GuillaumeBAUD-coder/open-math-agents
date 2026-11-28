import Mathlib

/-!
# A143013: Number of Motzkin n-paths with two kinds of level steps one of which is a final step.

Source: https://oeis.org/A143013
Credit: @vivanpoddar

The sequence (offset 0) is 1, 2, 3, 7, 17, 43, 114, 310, 861, ... The entry records the defining equation
A = 1 + F + LA + UADA, that is the g.f. satisfies A(x) = 1 + x + x*A(x) + (x*A(x))^2, which means
a(0) = 1, a(1) = 2 and a(n+2) = a(n+1) + Sum_{k=0..n} a(k)*a(n-k). This recursion is used here as the
definition (it reproduces the data of the entry).

The conjecture (R. J. Mathar) reads
(n+2)*a(n) - (2*n+1)*a(n-1) + 3*(1-n)*a(n-2) + 2*(5-2*n)*a(n-3) = 0.
It involves a(n-3), so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a143013

/-- A143013 (offset 0): a(0) = 1, a(1) = 2, a(n+2) = a(n+1) + Sum_{k=0..n} a(k)*a(n-k). -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | (n + 2) => a (n + 1) + ∑ k : Fin (n + 1), a k * a (n - k)

/-- Mathar's conjectured recurrence for A143013. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 2) * a n - (2 * (n : ℤ) + 1) * a (n - 1) + 3 * (1 - (n : ℤ)) * a (n - 2)
      + 2 * (5 - 2 * (n : ℤ)) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a143013
