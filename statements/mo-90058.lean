import Mathlib

namespace OMA.S_mo_90058

/-- Can a real special linear group in dimension at least three contain a
discrete simple subgroup that is not finitely generated? -/
theorem main :
    ∃ (n : ℕ) (G : Subgroup (Matrix.SpecialLinearGroup (Fin n) ℝ)),
      3 ≤ n ∧ DiscreteTopology G ∧ IsSimpleGroup G ∧ ¬ Group.FG G := by
  sorry

end OMA.S_mo_90058
