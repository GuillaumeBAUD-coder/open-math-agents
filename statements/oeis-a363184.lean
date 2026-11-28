import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

namespace OMA.S_oeis_a363184

/-!
OEIS A363184: Expansion of g.f. A(x) satisfying
  4 = Sum_{n=-oo..+oo} (-1)^n * x^n * (4*A(x) + x^(2*n-1))^(n+1).
Splitting off n = 0 and n = -1 (whose x^(-1) poles cancel, leaving 4*A(x)) and pairing
n >= 1 with -(n+1) <= -2 gives the formal power series identity over Z[[x]].
Conjecture: g.f. A(x) == theta_3(x^2) (mod 4); for r > 0, a(r) == 2 (mod 4) iff
r = 2*k^2 for some k > 0, and a(r) == 0 (mod 4) otherwise.
-/

theorem main : ∀ (A : PowerSeries ℤ),
    PowerSeries.constantCoeff A = 1 →
    (∀ r : ℕ, (if r = 0 then (4 : ℤ) else 0) =
      4 * PowerSeries.coeff r A +
      ∑ n ∈ Finset.Icc 1 r,
        PowerSeries.coeff r
          ((-PowerSeries.X) ^ n * (4 * A + PowerSeries.X ^ (2 * n - 1)) ^ (n + 1) +
           (-1 : PowerSeries ℤ) ^ (n + 1) * PowerSeries.X ^ (2 * n ^ 2 + 2 * n - 1) *
             (Ring.inverse (1 + 4 * PowerSeries.X ^ (2 * n + 3) * A)) ^ n)) →
    (∀ k : ℕ, 0 < k → PowerSeries.coeff (2 * k ^ 2) A % 4 = 2) ∧
    (∀ r : ℕ, 0 < r → (∀ k : ℕ, 2 * k ^ 2 ≠ r) → PowerSeries.coeff r A % 4 = 0) := by
  sorry

end OMA.S_oeis_a363184
