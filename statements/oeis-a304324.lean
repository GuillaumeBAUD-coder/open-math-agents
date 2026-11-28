import Mathlib

/-!
# A304324: O.g.f. A(x) satisfies: [x^n] exp(n^4 x) / A(x) = 0 for n>0.

Source: https://oeis.org/A304324
Credit: @marcusbuffett

Comment of the entry: It is conjectured that the coefficients of o.g.f. A(x) consist entirely of
integers.

Formalization notes:
* A(x) is a formal power series with rational coefficients. The condition at n = 0 is not
  imposed, so every nonzero multiple of a solution is again a solution; the data begin
  a(0) = 1, and the normalization constantCoeff A = 1 picks the series of the entry. Then
  A(x) is invertible and 1 / A(x) is the inverse A⁻¹ in ℚ⟦X⟧.
* exp(n^4 x) is the series with coefficients (n^4)^j / j!.
* `main` states that such a series exists and that every such series has integer coefficients
  (the solution is unique, since the condition at n fixes the coefficient of x^n of 1 / A(x)
  from the lower ones).
* The entry also conjectures that the coefficient of x^n in A'(x)/A(x) is the number of
  connected n-state finite automata with 4 inputs. That is a statement about a second
  sequence, which this file does not define, and it is not stated here.
-/

namespace OMA.S_oeis_a304324

open PowerSeries

/-- The series exp(c x), with coefficients c^j / j!. -/
noncomputable def expSeries (c : ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun j => c ^ j / (j.factorial : ℚ)

/-- A(x) is normalized by A(0) = 1 and satisfies [x^n] exp(n^4 x) / A(x) = 0 for n > 0. -/
def IsSol (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 1 ∧
    ∀ n : ℕ, 0 < n → coeff n (expSeries ((n : ℚ) ^ 4) * A⁻¹) = 0

/-- The o.g.f. of A304324 exists, and its coefficients are integers. -/
theorem main :
    (∃ A : PowerSeries ℚ, IsSol A) ∧
      ∀ A : PowerSeries ℚ, IsSol A → ∀ m : ℕ, ∃ z : ℤ, coeff m A = (z : ℚ) := by
  sorry

end OMA.S_oeis_a304324
