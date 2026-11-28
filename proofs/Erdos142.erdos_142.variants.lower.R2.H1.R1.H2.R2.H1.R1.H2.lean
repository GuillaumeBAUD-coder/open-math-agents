import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1
import Mathlib

/-!
Step H2 of the reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H1.R1: a set covered by q subsets of [1, N],
each free of 3-term progressions, has at most q * r 3 N elements. Union bound, then each piece
is at most the extremal number (card_le_maxCard from reduction R2 of this problem).
-/

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1.H2 := by
  intro N q S B hS hB
  calc S.card ≤ (Finset.univ.biUnion B).card := Finset.card_le_card hS
    _ ≤ ∑ i : Fin q, (B i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin q, Set.IsAPOfLengthFree.maxCard 3 N := Finset.sum_le_sum fun i _ =>
        OMA.R_Erdos142_erdos_142_variants_lower_R2.card_le_maxCard (hB i).1 (by exact_mod_cast (hB i).2)
    _ = q * Set.IsAPOfLengthFree.maxCard 3 N := by simp
