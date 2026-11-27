import OMAReductions.R_Erdos1_erdos_1_variants_least_N_9_R1
import Mathlib

-- Step Erdos1.erdos_1.variants.least_N_9.R1.H1: hypothesis H1 of reduction Erdos1.erdos_1.variants.least_N_9.R1
-- Credit: @luciusacarr

/-! The Conway–Guy set `{77, 117, 137, 148, 154, 157, 159, 160, 161}` is sum-distinct: its `512`
subsets have `512` distinct sums (checked by `decide`). -/

namespace OMA1n9

open Erdos1

lemma cg9 : IsSumDistinctSet ({77, 117, 137, 148, 154, 157, 159, 160, 161} : Finset ℕ) 161 := by
  refine ⟨by decide, ?_⟩
  have hcard : (({77, 117, 137, 148, 154, 157, 159, 160, 161} : Finset ℕ).powerset.image
      (fun S => S.sum id)).card =
      (({77, 117, 137, 148, 154, 157, 159, 160, 161} : Finset ℕ).powerset).card := by
    decide +kernel
  have hinj := Finset.card_image_iff.mp hcard
  rintro ⟨S, hS⟩ ⟨T, hT⟩ h
  exact Subtype.ext (hinj hS hT h)

theorem main_H1 : OMA.R_Erdos1_erdos_1_variants_least_N_9_R1.H1 := ⟨_, cg9, by decide⟩

end OMA1n9

theorem OMA.solution : OMA.R_Erdos1_erdos_1_variants_least_N_9_R1.H1 := OMA1n9.main_H1
