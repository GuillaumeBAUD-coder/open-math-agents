import OMAReductions.R_Erdos654_erdos_654_variants_general_position_R1

-- Step Erdos654.erdos_654.variants.general_position.R1.H2: hypothesis H2 of reduction Erdos654.erdos_654.variants.general_position.R1
-- Credit: @Raimo33

namespace Raimo654
open EuclideanGeometry

theorem col (y z : EuclideanSpace ℝ (Fin 2)) (hyz : y ≠ z) :
    Collinear ℝ ((AffineSubspace.perpBisector y z : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 2))) := by
  unfold Collinear
  change Module.rank ℝ (AffineSubspace.perpBisector y z).direction ≤ 1
  rw [AffineSubspace.direction_perpBisector]
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) := ⟨by simp⟩
  have hv : z -ᵥ y ≠ 0 := by
    intro h; exact hyz (eq_of_vsub_eq_zero h).symm
  have := Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (n := 1) hv
  rw [← Module.finrank_eq_rank, this]
  simp

theorem three (y z a b c : EuclideanSpace ℝ (Fin 2)) (hyz : y ≠ z)
    (ha : dist a y = dist a z) (hb : dist b y = dist b z) (hc : dist c y = dist c z) :
    Collinear ℝ {a, b, c} := by
  apply (col y z hyz).subset
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl <;>
    simpa [AffineSubspace.mem_perpBisector_iff_dist_eq]
end Raimo654

theorem OMA.solution : OMA.R_Erdos654_erdos_654_variants_general_position_R1.H2 := by
  intro A hA y _ z _ hyz
  by_contra hlt
  push_neg at hlt
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hlt
  simp only [Finset.mem_filter] at ha hb hc
  exact hA ha.1 hb.1 hc.1 hab hbc hac (Raimo654.three y z a b c hyz ha.2 hb.2 hc.2)
