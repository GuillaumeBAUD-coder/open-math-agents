import OMAReductions.R_LovaszConjecture_lovasz_conjecture_variants_dense_R1

-- Step LovaszConjecture.lovasz_conjecture.variants.dense.R1.H2
-- Credit: @caa1982

theorem OMA.solution : OMA.R_LovaszConjecture_lovasz_conjecture_variants_dense_R1.H2 :=
  fun _ v c hc => ⟨c.getVert 1, v, c.tail, hc.isHamiltonian_tail⟩
