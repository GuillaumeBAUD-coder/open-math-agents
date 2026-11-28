import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.Int.ModEq

/-!
# Congruences for the inverse of a lacunary series

OEIS A389537 gives its normalized generating function as the compositional
inverse of R(x) = x − x² + x⁴ − x⁸ + ⋯. Its coefficients start at degree one.
The conjecture concerns precisely the degrees greater than two.

Source: https://oeis.org/A389537
Credit: @hiattco
-/

open PowerSeries
open scoped PowerSeries

namespace OMA.S_oeis_a389537

/-- The coefficient at n in x−x²+x⁴−x⁸+⋯. -/
def r (n : ℕ) : ℤ :=
  if n = 2 ^ n.log2 then (-1 : ℤ) ^ n.log2 else 0

noncomputable def R : ℤ⟦X⟧ := mk r

/-- The compositional inverse of R, whose linear coefficient is one. -/
noncomputable def A : ℤ⟦X⟧ := R.substInvOfIsUnit (by
  rw [R, coeff_mk, show r 1 = 1 by decide +kernel]
  exact isUnit_one)

noncomputable def a (n : ℕ) : ℤ := coeff n A

theorem main : ∀ n : ℕ, 2 < n →
    ((∃ k : ℕ, n = 3 * 2 ^ k) → a n ≡ 2 [ZMOD 4]) ∧
    ((¬ ∃ k : ℕ, n = 3 * 2 ^ k) → 4 ∣ a n) := by
  sorry

end OMA.S_oeis_a389537
