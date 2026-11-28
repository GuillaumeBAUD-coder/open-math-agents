import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1
import Mathlib

/-!
# Step H2 of the reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H1.R1

Each covering piece is a three-term-progression-free subset of the interval from 1 to N, so its
size is one of the numbers whose supremum defines r 3 N; that set of sizes is bounded by N, hence
each piece has at most r 3 N elements. The covered set is no larger than the union of the
pieces, which is no larger than the sum of their sizes.
-/

namespace OMA.Helpers

theorem e142cover_piece_le_r3 {N : ℕ} {T : Finset ℕ} (hT : T ⊆ Finset.Icc 1 N)
    (hfree : ((T : Finset ℕ) : Set ℕ).IsAPOfLengthFree 3) : T.card ≤ Erdos142.r 3 N := by
  unfold Erdos142.r Set.IsAPOfLengthFree.maxCard
  apply le_csSup
  · refine ⟨N, ?_⟩
    rintro n ⟨S, hS, -, rfl⟩
    exact (Finset.card_le_card hS).trans_eq (by simp)
  · exact ⟨T, hT, by exact_mod_cast hfree, rfl⟩

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1.H2 := by
  intro N q S B hsub hB
  calc S.card ≤ (Finset.univ.biUnion B).card := Finset.card_le_card hsub
    _ ≤ ∑ i, (B i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin q, Erdos142.r 3 N :=
        Finset.sum_le_sum fun i _ => OMA.Helpers.e142cover_piece_le_r3 (hB i).1 (hB i).2
    _ = q * Erdos142.r 3 N := by simp
