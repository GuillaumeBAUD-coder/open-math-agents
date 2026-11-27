import OMAReductions.R_Erdos89_erdos_89_variants_n_dvd_log_n_R1

-- Step Erdos89.erdos_89.variants.n_dvd_log_n.R1.H2
-- Credit: @caa1982

open Finset EuclideanGeometry
open scoped Classical

theorem OMA.solution : OMA.R_Erdos89_erdos_89_variants_n_dvd_log_n_R1.H2 := by
  intro S
  let P := S.offDiag
  let D := distanceSet S
  let f : ℝ → ℕ := fun d => (P.filter fun p => dist p.1 p.2 = d).card
  have hsum : P.card = ∑ d ∈ D, f d := by
    apply Finset.card_eq_sum_card_fiberwise
    intro p hp
    exact Finset.mem_image_of_mem _ hp
  have hsq : ((P ×ˢ P).filter fun z => dist z.1.1 z.1.2 = dist z.2.1 z.2.2).card =
      ∑ d ∈ D, (f d) ^ 2 := by
    have hfib : ((P ×ˢ P).filter fun z => dist z.1.1 z.1.2 = dist z.2.1 z.2.2).card =
        ∑ d ∈ D, (((P ×ˢ P).filter fun z => dist z.1.1 z.1.2 = dist z.2.1 z.2.2).filter
          fun z => dist z.1.1 z.1.2 = d).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro z hz
      exact Finset.mem_image_of_mem _ (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1
    rw [hfib]
    apply Finset.sum_congr rfl
    intro d _
    have hprod : (((P ×ˢ P).filter fun z => dist z.1.1 z.1.2 = dist z.2.1 z.2.2).filter
        fun z => dist z.1.1 z.1.2 = d) =
        (P.filter fun p => dist p.1 p.2 = d) ×ˢ (P.filter fun p => dist p.1 p.2 = d) := by
      ext ⟨p, q⟩
      simp only [Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨⟨⟨hp, hq⟩, heq⟩, hd⟩
        exact ⟨⟨hp, hd⟩, ⟨hq, heq.symm.trans hd⟩⟩
      · rintro ⟨⟨hp, hpd⟩, ⟨hq, hqd⟩⟩
        exact ⟨⟨⟨hp, hq⟩, hpd.trans hqd.symm⟩, hpd⟩
    rw [hprod, Finset.card_product, sq]
  have hcs : (∑ d ∈ D, (f d : ℝ)) ^ 2 ≤ (D.card : ℝ) * ∑ d ∈ D, (f d : ℝ) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hcs_nat : (∑ d ∈ D, f d) ^ 2 ≤ D.card * ∑ d ∈ D, (f d) ^ 2 := by
    exact_mod_cast hcs
  change P.card ^ 2 ≤ D.card * ((P ×ˢ P).filter fun z => dist z.1.1 z.1.2 = dist z.2.1 z.2.2).card
  rw [hsum, hsq]
  exact hcs_nat
