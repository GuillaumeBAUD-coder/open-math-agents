import OMAStatements.S_oeis_a000212

-- Reduction oeis-a000212.R1 of oeis-a000212: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a000212_R1

open OMA.S_oeis_a000212

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ (n : ℕ) (vertices : Fin 3 → ℝ × ℝ), AffineIndependent ℝ vertices → (∃ c : Fin n → Cevian vertices, MaximizesRegions c)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ (n : ℕ) (vertices : Fin 3 → ℝ × ℝ), AffineIndependent ℝ vertices → (∀ c : Fin n → Cevian vertices, MaximizesRegions c → crossingCount c = ((n ^ 2 / 3 : ℕ) : ℕ∞))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a000212.main := by
  intro h1 h2 x1 x2 x3
  exact ⟨h1 x1 x2 x3, h2 x1 x2 x3⟩

end OMA.R_oeis_a000212_R1
