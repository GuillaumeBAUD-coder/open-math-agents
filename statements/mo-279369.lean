import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs

namespace OMA.S_mo_279369

/-- The binomial form of the hook-content sum, with the factor
`h^(d-1)` in the denominator from the author's follow-up. -/
def hookSum (d : ℕ) (h : ℚ) : ℚ :=
  (∑ k ∈ Finset.range d,
    (-1 : ℚ)^k * ((d - 1).choose k : ℚ) *
      ∏ i ∈ Finset.range d, (1 + ((i : ℚ) - k)*h)^2) /
        ((d : ℚ) * (d.factorial : ℚ) * h^(d-1))

/-- The three-term recurrence at nonzero values of the polynomial parameter. -/
theorem main :
    ∀ (d : ℕ), 3 ≤ d → ∀ h : ℚ, h ≠ 0 →
      (d : ℚ) * ((d : ℚ) + 1) * hookSum d h =
        ((d : ℚ) - 1) * (4*(d : ℚ) - 2) * hookSum (d-1) h +
          h^2 * ((d : ℚ) - 1)^2 * ((d : ℚ) - 2)^2 * hookSum (d-2) h := by
  sorry

end OMA.S_mo_279369
