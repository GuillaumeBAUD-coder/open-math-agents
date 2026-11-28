import Mathlib

/-!
# A289684: Mathar's recurrence, corrected to n ≥ 4

Source: https://oeis.org/A289684
Credit: @ivillar

Status: known result. The entry records: Conjecture verified (for n >= 4) using the differential equation (16*x^3 +
12*x^2 - 8*x + 1)*y' + (24*x^2 - 2)*y -12*x^2 + 2*x = 0 satisfied by the g.f.
It is false as stated at n = 3 (the left side is 12 at n = 3 on the OEIS data); `main` is the
corrected recurrence (n ≥ 4), which is proved.

A289684 (offset 0): mixing moments for the waiting time in an M/G/1 waiting queue;
data 1, 2, 9, 42, 199, 950, 4554, 21884, 105323, 507398, 2446022, 11796884, ...

Conjecture (R. J. Mathar):
n*a(n) + 2*(-4*n+3)*a(n-1) + 12*(n-2)*a(n-2) + 8*(2*n-3)*a(n-3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the Catalan g.f., determined by
2*x*c = 1 - S; and the g.f. G = 1/(2 - c^2) is determined by G*(2 - c^2) = 1;
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 4): on the data the left side of the recurrence as
stated is 12 at n = 3, and it vanishes from n = 4 on.
-/

namespace OMA.S_oeis_a289684

open PowerSeries

/-- The corrected recurrence (n ≥ 4): Mathar's recurrence, which fails at n = 3. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G * (2 - c ^ 2) = 1 →
    ∀ n : ℕ, 4 ≤ n →
      ((n : ℚ)) * coeff n G + (6 - 8 * (n : ℚ)) * coeff (n - 1) G +
        (-24 + 12 * (n : ℚ)) * coeff (n - 2) G + (-24 + 16 * (n : ℚ)) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a289684
