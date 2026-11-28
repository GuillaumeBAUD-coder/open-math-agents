import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3
import Mathlib

/-!
Step H1 of the reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3.R3: r k (4 N) is at most 4 r k N.
Three applications of the subadditivity r k (M + N) <= r k M + r k N, proved as maxCard_add_le
in reduction R2 of this problem (splitting [1, 4N] into four translates of [1, N]).
-/

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3.H1 := by
  intro k _ N
  have h := OMA.R_Erdos142_erdos_142_variants_lower_R2.maxCard_add_le k
  have h1 := h N N
  have h2 := h (N + N) N
  have h3 := h (N + N + N) N
  show Set.IsAPOfLengthFree.maxCard k (4 * N) ≤ 4 * Set.IsAPOfLengthFree.maxCard k N
  rw [show 4 * N = N + N + N + N by ring]
  omega
