import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# A301483: a(n) = floor(a(n-1)/(2^(1/3)-1)) with a(1)=1.

Source: https://oeis.org/A301483
Credit: @SPatel2133

Conjectures of Colin Barker, 1 April 2018:
G.f.: x*(1 - x - x^2) / ((1 - x)*(1 - 3*x - 3*x^2 - x^3)), and
a(n) = 4*a(n-1) - 2*a(n-3) - a(n-4) for n > 4.

The sequence has offset one. It is padded with zero at index zero, which is the constant
coefficient of the conjectured generating function. The generating function is stated with
its denominator cleared.

The source also lists a(n) = A195350(n) + A303647(n-2) - A195339(n-4). That identity fails
as printed (at n = 4: 42 ≠ 37 + 5 - 1). Its corrected shift is the companion identity already
stated in `statements/oeis-a303647.lean`, so it is not repeated here.
-/

namespace OMA.S_oeis_a301483

open PowerSeries

noncomputable def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => ⌊(a (n + 1) : ℝ) / ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1)⌋

theorem main :
    ((1 - X) * (1 - 3 * X - 3 * X ^ 2 - X ^ 3) * PowerSeries.mk a =
      (X * (1 - X - X ^ 2) : PowerSeries ℤ)) ∧
    ∀ n : ℕ, 4 < n → a n = 4 * a (n - 1) - 2 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a301483
