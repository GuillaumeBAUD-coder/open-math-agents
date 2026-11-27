import OMAReductions.R_Erdos89_erdos_89_variants_n_dvd_log_n_R1

/-! The distance-fiber Cauchy–Schwarz inequality for ordered segments. -/

-- Step Erdos89.erdos_89.variants.n_dvd_log_n.R1.H2: hypothesis H2 of reduction Erdos89.erdos_89.variants.n_dvd_log_n.R1
-- Credit: @dk8827

open Finset EuclideanGeometry

theorem OMA.solution : OMA.R_Erdos89_erdos_89_variants_n_dvd_log_n_R1.H2 := by
  classical
  intro S
  let P := S.offDiag
  let distance (p : ℝ² × ℝ²) := dist p.1 p.2
  let D := P.image distance
  let E := (P ×ˢ P).filter fun z ↦ distance z.1 = distance z.2
  let fiber (d : ℝ) := P.filter fun p ↦ distance p = d
  have hP : P.card = ∑ d ∈ D, (fiber d).card :=
    card_eq_sum_card_image distance P
  have hE : E.card = ∑ d ∈ D, (fiber d).card ^ 2 := by
    calc
      E.card = ∑ d ∈ D, (E.filter fun z ↦ distance z.1 = d).card := by
        apply card_eq_sum_card_fiberwise
        intro z hz
        exact mem_image.mpr ⟨z.1, (mem_product.mp (mem_filter.mp hz).1).1, rfl⟩
      _ = ∑ d ∈ D, (fiber d).card ^ 2 := by
        apply sum_congr rfl
        intro d _
        have hfiber : (E.filter fun z ↦ distance z.1 = d) = fiber d ×ˢ fiber d := by
          ext z
          simp only [E, fiber, mem_filter, mem_product]
          constructor
          · rintro ⟨⟨⟨hx, hy⟩, hxy⟩, hd⟩
            exact ⟨⟨hx, hd⟩, ⟨hy, hxy.symm.trans hd⟩⟩
          · rintro ⟨⟨hx, hd⟩, ⟨hy, he⟩⟩
            exact ⟨⟨⟨hx, hy⟩, hd.trans he.symm⟩, hd⟩
        rw [hfiber, card_product, pow_two]
  change P.card ^ 2 ≤ D.card * E.card
  rw [hP, hE]
  exact sq_sum_le_card_mul_sum_sq
