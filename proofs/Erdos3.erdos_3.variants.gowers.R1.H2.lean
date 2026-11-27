import OMAReductions.R_Erdos3_erdos_3_variants_gowers_R1
import Mathlib

/-!
Step H2 of Erdos3.erdos_3.variants.gowers.R1. A nontrivial arithmetic progression of length
l ≥ k ≥ 2 in the naturals has nonzero difference, so its first k terms form a progression of
length k. Hence a k-free set is l-free, and the supremum defining r k N is at most the one
defining r l N.
-/

namespace OMA.P1Erdos3H2

theorem free_mono {S : Set ℕ} {k l : ℕ} (hk : 2 ≤ k) (hkl : k ≤ l)
    (h : S.IsAPOfLengthFree k) : S.IsAPOfLengthFree l := by
  intro t ht hap
  exfalso
  obtain ⟨a, d, hcard, heq⟩ := hap
  have hd : d ≠ 0 := by
    rintro rfl
    have hsub : t ⊆ {a} := by
      rw [heq]
      rintro x ⟨n, _, rfl⟩
      simp
    have h1 : t.encard ≤ 1 := (Set.encard_le_encard hsub).trans (by rw [Set.encard_singleton])
    have h2 : t.encard = l := hcard
    rw [h2] at h1
    have h3 : l ≤ 1 := by exact_mod_cast h1
    omega
  let t' : Set ℕ := {a + n • d | (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞))}
  have hinj : Function.Injective (fun n : ℕ => a + n • d) := by
    intro m n hmn
    simp only [smul_eq_mul] at hmn
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hd) (by omega)
  have ht' : t' = (fun n : ℕ => a + n • d) '' ↑(Finset.range k) := by
    ext x
    simp [t', Finset.mem_range]
  have hcard' : ENat.card t' = k := by
    change t'.encard = k
    rw [ht', hinj.injOn.encard_image, Set.encard_coe_eq_coe_finsetCard, Finset.card_range]
  have hsub : t' ⊆ S := by
    rintro x ⟨n, hn, rfl⟩
    apply ht
    rw [heq]
    exact ⟨n, lt_of_lt_of_le hn (by exact_mod_cast hkl), rfl⟩
  have h4 := h t' hsub ⟨a, d, hcard', rfl⟩
  have h5 : k ≤ 1 := by exact_mod_cast h4
  omega

end OMA.P1Erdos3H2

open OMA.P1Erdos3H2 in
theorem OMA.solution : OMA.R_Erdos3_erdos_3_variants_gowers_R1.H2 := by
  unfold OMA.R_Erdos3_erdos_3_variants_gowers_R1.H2
  intro k l N hk hkl
  show Set.IsAPOfLengthFree.maxCard k N ≤ Set.IsAPOfLengthFree.maxCard l N
  unfold Set.IsAPOfLengthFree.maxCard
  apply csSup_le_csSup
  · refine ⟨N, ?_⟩
    rintro _ ⟨S, hS, _, rfl⟩
    calc S.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hS
      _ = N := by simp
  · refine ⟨0, ∅, Finset.empty_subset _, ?_, Finset.card_empty⟩
    intro t ht hap
    rw [Finset.coe_empty, Set.subset_empty_iff] at ht
    subst ht
    have h0 : (∅ : Set ℕ).encard = k := hap.card
    rw [Set.encard_empty] at h0
    rw [← h0]
    exact zero_le_one
  · rintro _ ⟨S, hS, hfree, rfl⟩
    exact ⟨S, hS, free_mono hk hkl hfree, rfl⟩
