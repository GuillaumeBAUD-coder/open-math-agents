import Mathlib

/-!
# A059279: G.f. is ((1-x)/(1-2*x)) * G(x*(1-x)/(1-2*x)) where G(x) is g.f. for Catalan numbers A000108.

Source: https://oeis.org/A059279
Credit: @vivanpoddar

The sequence (offset 0) is 1, 2, 6, 20, 72, 276, 1112, 4656, 20080, 88608, ... The entry records that the
g.f. satisfies A(x) = 1 + x*(1/(1-2*x) + A(x)^2) (I. Gutkovskiy, Jun 30 2020), that is
a(0) = 1 and a(n+1) = 2^n + Sum_{k=0..n} a(k)*a(n-k). This recursion is used here as the definition
(it reproduces the data of the entry).

The conjecture (R. J. Mathar, Nov 15 2011) reads
(n+1)*a(n) + 2*(1-4*n)*a(n-1) + 4*(4*n-5)*a(n-2) + 4*(5-2*n)*a(n-3) = 0.
It involves a(n-3), so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a059279

/-- A059279 (offset 0): a(0) = 1 and a(n+1) = 2^n + Sum_{k=0..n} a(k)*a(n-k). -/
def a : ℕ → ℤ
  | 0 => 1
  | (n + 1) => 2 ^ n + ∑ k : Fin (n + 1), a k * a (n - k)

/-- Mathar's conjectured recurrence for A059279. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 1) * a n + 2 * (1 - 4 * (n : ℤ)) * a (n - 1) + 4 * (4 * (n : ℤ) - 5) * a (n - 2)
      + 4 * (5 - 2 * (n : ℤ)) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a059279
