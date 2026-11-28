import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Basic

namespace OMA.S_mo_109975

noncomputable def harmonic (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, 1 / ((j + 1 : ℕ) : ℝ)

/-- The alternating binomial sum in the question. -/
noncomputable def alternatingLog (m n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m,
    (-1 : ℝ) ^ (j + 1) * (m.choose (j + 1) : ℝ) *
      (Real.log ((n : ℝ) - ((j + 1 : ℕ) : ℝ)) / ((j + 1 : ℕ) : ℝ))

noncomputable def error (m n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (m + 1) *
    (alternatingLog m n + harmonic m * Real.log n - 1 / (n : ℝ))

/-- A signed remainder estimate valid uniformly for `2 ≤ m < n`. -/
theorem main :
    ∀ m n : ℕ, 2 ≤ m → m < n →
      0 ≤ error m n ∧
        error m n ≤ (m.factorial : ℝ) /
          (((m + 1 : ℕ) : ℝ) * (n : ℝ) *
            ∏ j ∈ Finset.range m, ((n : ℝ) - ((j + 1 : ℕ) : ℝ))) := by
  sorry

end OMA.S_mo_109975
