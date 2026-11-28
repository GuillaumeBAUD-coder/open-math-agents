import OMAStatements.S_mo_278672

-- Reduction mo-278672.R1 of mo-278672: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_mo_278672_R1

open OMA.S_mo_278672
open Matrix

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsBipartite ↔
      ∀ A : Mat n, pattern G A → ¬A.IsSymm → oddDiagonal A)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Mat n), G.IsBipartite →
      pattern G A → reflected (numRange A))

/-- Step H3 of the reduction. -/
def H3 : Prop := (pattern ⊤ exampleA ∧ ¬exampleA.IsSymm ∧
      (∀ i j, exampleA i j≠0 ↔ exampleA j.rev i.rev≠0) ∧
      (∃ B : Mat 3, pattern ⊤ B ∧ ¬B.IsSymm ∧ ¬oddDiagonal B))

/-- Step H4 of the reduction. -/
def H4 : Prop := ( oddDiagonal exampleA ∧ (4:ℂ)∈numRange exampleA ∧ (-4:ℂ)∉numRange exampleA )

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_mo_278672.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_mo_278672_R1
