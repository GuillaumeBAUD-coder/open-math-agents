import OMAStatements.S_opg_turans_problem_for_hypergraphs

-- Reduction opg-turans-problem-for-hypergraphs.R1 of opg-turans-problem-for-hypergraphs: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_opg_turans_problem_for_hypergraphs_R1

open OMA.S_opg_turans_problem_for_hypergraphs

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ (n : ℕ) (F : Finset (Finset (Fin (3 * n)))),
      (∀ e ∈ F, e.card = 3) →
      (∀ K : Finset (Fin (3 * n)), K.card = 4 → ¬ K.powersetCard 3 ⊆ F) →
      2 * F.card ≤ n ^ 2 * (5 * n - 3))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ (n : ℕ) (F : Finset (Finset (Fin (2 * n)))),
      (∀ e ∈ F, e.card = 3) →
      (∀ K : Finset (Fin (2 * n)), K.card = 5 → ¬ K.powersetCard 3 ⊆ F) →
      F.card ≤ n ^ 2 * (n - 1))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_opg_turans_problem_for_hypergraphs.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_opg_turans_problem_for_hypergraphs_R1
