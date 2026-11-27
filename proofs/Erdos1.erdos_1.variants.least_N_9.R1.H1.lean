import OMAReductions.R_Erdos1_erdos_1_variants_least_N_9_R1
import Mathlib

-- Step Erdos1.erdos_1.variants.least_N_9.R1.H1: hypothesis H1 of reduction Erdos1.erdos_1.variants.least_N_9.R1
-- Credit: @ivillar
--
-- The Conway-Guy set {77, 117, 137, 148, 154, 157, 159, 160, 161} is sum-distinct: its 512 subset
-- sums are pairwise different, checked by computing the image of the subset-sum map.

theorem OMA.solution : OMA.R_Erdos1_erdos_1_variants_least_N_9_R1.H1 := by
  unfold OMA.R_Erdos1_erdos_1_variants_least_N_9_R1.H1
  refine ⟨{77, 117, 137, 148, 154, 157, 159, 160, 161}, ⟨by decide, ?_⟩, by decide⟩
  have h : (({77, 117, 137, 148, 154, 157, 159, 160, 161} : Finset ℕ).powerset.image
      (fun S => S.sum id)).card =
      ({77, 117, 137, 148, 154, 157, 159, 160, 161} : Finset ℕ).powerset.card := by
    decide +kernel
  have hinj := Finset.injOn_of_card_image_eq h
  rintro ⟨S, hS⟩ ⟨T, hT⟩ hST
  exact Subtype.ext (hinj hS hT hST)
