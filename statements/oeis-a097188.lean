import Mathlib

/-!
# A097188: Mathar's recurrence

Source: https://oeis.org/A097188
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A097188 (offset 0): g.f. A(x) satisfies A057083(x*A(x)) = A(x) and so equals the ratio of the g.f.s of any two adjacent diagonals of triangle A097186;
data 1, 3, 15, 90, 594, 4158, 30294, 227205, 1741905, 13586859, 107459703, 859677624, ...

Conjecture (R. J. Mathar, Nov 16 2012):
(n+1)*a(n) +3*(-3*n+1)*a(n-1) = 0.

Formalization: A057083 has g.f. 1/(1 - 3*x + 3*x^2), so the condition A057083(x*A(x)) = A(x) reads
1/(1 - 3*x*A + 3*x^2*A^2) = A. G is the formal power series over ℚ with G*(1 - 3*x*G + 3*x^2*G^2) = 1; this
equation determines G, and its constant term is 1;
a(n) = [x^n] G. The recurrence involves a(n-1), so it is stated for n ≥ 1; it is checked by the data, for
example at n = 1: (2)*(3) + (-6)*(1) = 0.
-/

namespace OMA.S_oeis_a097188

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A097188, for n ≥ 1. -/
theorem main : ∀ G : ℚ⟦X⟧, G * (1 - 3 * X * G + 3 * X ^ 2 * G ^ 2) = 1 →
    ∀ n : ℕ, 1 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (3 - 9 * (n : ℚ)) * coeff (n - 1) G = 0 := by
  sorry

end OMA.S_oeis_a097188
