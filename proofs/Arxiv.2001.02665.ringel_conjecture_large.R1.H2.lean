import OMAReductions.R_Arxiv_2001_02665_ringel_conjecture_large_R1

-- Step Arxiv.2001.02665.ringel_conjecture_large.R1.H2: hypothesis H2 of reduction Arxiv.2001.02665.ringel_conjecture_large.R1

/-!
The edge set of `T.map g` is the image of the edge set of `T` under the injective map on
unordered pairs induced by the embedding `g`, so the two edge sets have the same size.
-/

theorem OMA.solution : OMA.R_Arxiv_2001_02665_ringel_conjecture_large_R1.H2 := by
  unfold OMA.R_Arxiv_2001_02665_ringel_conjecture_large_R1.H2
  intro n V _ T g
  rw [SimpleGraph.edgeSet_map]
  exact Set.ncard_image_of_injective _ g.sym2Map.injective
