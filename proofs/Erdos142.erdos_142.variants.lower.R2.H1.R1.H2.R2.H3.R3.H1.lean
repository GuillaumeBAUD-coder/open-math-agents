import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3

/-!
# Step H1 of the reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3.R3

The interval [1, 4N] splits into two halves of length 2N, and each of those into two
intervals of length N. The halving bound maxCard k (2 M) at most 2 maxCard k M from the
root reduction, applied with M = 2N and then with M = N, gives the factor four.
-/

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3.H1 := by
  intro k _ N
  have hA := OMA.R_Erdos142_erdos_142_variants_lower_R2.maxCard_double_le k (2 * N)
  have hB := OMA.R_Erdos142_erdos_142_variants_lower_R2.maxCard_double_le k N
  have h4 : 4 * N = 2 * (2 * N) := by ring
  show Set.IsAPOfLengthFree.maxCard k (4 * N) ≤ 4 * Set.IsAPOfLengthFree.maxCard k N
  rw [h4]
  omega
