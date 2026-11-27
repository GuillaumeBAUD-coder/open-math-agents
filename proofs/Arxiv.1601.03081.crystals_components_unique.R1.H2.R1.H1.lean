import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1

/-! # Gcd normalization closes the shared-divisor H1 step -/

theorem OMA.solution :
    OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1.H1 := by
  intro a b c d ha hc hab hcop
  exact OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1.normalized_shared_divisor
    ha hc hab hcop
