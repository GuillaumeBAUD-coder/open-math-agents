import OMAReductions.R_Erdos1_erdos_1_variants_least_N_9_R1

-- Step Erdos1.erdos_1.variants.least_N_9.R1.H1: hypothesis H1 of reduction Erdos1.erdos_1.variants.least_N_9.R1

/-!
The Conway-Guy set `{77, 117, 137, 148, 154, 157, 159, 160, 161}` has `2 ^ 9 = 512` distinct
subset sums: the image of its powerset under the sum has `512` elements, so the sum is injective
on the powerset.
-/

theorem OMA.solution : OMA.R_Erdos1_erdos_1_variants_least_N_9_R1.H1 := by
  unfold OMA.R_Erdos1_erdos_1_variants_least_N_9_R1.H1
  have hinj : Set.InjOn (fun S : Finset ℕ => S.sum id)
      (↑(({77, 117, 137, 148, 154, 157, 159, 160, 161} : Finset ℕ).powerset) :
        Set (Finset ℕ)) :=
    Finset.card_image_iff.mp (by decide +kernel)
  refine ⟨{77, 117, 137, 148, 154, 157, 159, 160, 161}, ⟨by decide, ?_⟩, by decide⟩
  intro S T h
  obtain ⟨S, hS⟩ := S
  obtain ⟨T, hT⟩ := T
  exact Subtype.ext (hinj (Finset.mem_coe.mpr hS) (Finset.mem_coe.mpr hT) h)
