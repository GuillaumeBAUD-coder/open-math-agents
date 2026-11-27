import OMAReductions.R_Green17_green_17_variants_exponential_R1

/-! Concatenating coordinates preserves the absence of restricted progressions. -/

theorem OMA.solution : OMA.R_Green17_green_17_variants_exponential_R1.H1 := by
  classical
  intro m n A B hA hB
  let C := (A ×ˢ B).map (Fin.appendEquiv m n).toEmbedding
  refine ⟨C, by simp [C], ?_⟩
  rintro ⟨x,d,hd,h01,hx,h1,h2⟩
  let left (v : 𝔽₃ (m + n)) : 𝔽₃ m := fun i => v (Fin.castAdd n i)
  let right (v : 𝔽₃ (m + n)) : 𝔽₃ n := fun i => v (Fin.natAdd m i)
  have split {v : 𝔽₃ (m + n)} (hv : v ∈ C) : left v ∈ A ∧ right v ∈ B :=
    Finset.mem_product.mp (Finset.mem_map_equiv.mp hv)
  by_cases hl : left d = 0
  · have hr : right d ≠ 0 := by
      intro hr
      apply hd
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · exact congrFun hl j
      · exact congrFun hr j
    exact hB ⟨right x, right d, hr, fun i => h01 (Fin.natAdd m i),
      (split hx).2, (split h1).2, (split h2).2⟩
  · exact hA ⟨left x, left d, hl, fun i => h01 (Fin.castAdd n i),
      (split hx).1, (split h1).1, (split h2).1⟩
