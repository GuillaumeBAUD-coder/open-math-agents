import OMAReductions.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1
import Mathlib

-- Step Green3.green_3.R1.H2.R1.H2.R1.H2.R1.H1: hypothesis H1 of reduction Green3.green_3.R1.H2.R1.H2.R1.H2.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Packing argument: the sets `T ∩ [0, u + 2a)`, `(T ∩ [0, u + a)) + e` and `(T ∩ [0, u]) + (d + e)`
are pairwise disjoint subsets of `[a, u + 2a)`, which has `u + a` elements, and the third one has
`#(T ∩ [0, u)) + 1` elements because `u ∈ T`.
-/

namespace Green3StepPacking

open Finset

theorem three_prefix_lt (T : Finset ℕ) (a u d e : ℕ) (hTa : ∀ x ∈ T, a ≤ x) (hu : u ∈ T)
    (hea : e ≤ a) (hde : d + e < 2 * a)
    (h1 : ∀ x ∈ T, x ≤ u → x + d ∉ T) (h2 : ∀ x ∈ T, x < u + a → x + e ∉ T)
    (h3 : ∀ x ∈ T, x ≤ u → x + (d + e) ∉ T) :
    (T.filter (· < u)).card + (T.filter (· < u + a)).card + (T.filter (· < u + 2 * a)).card
      < u + a := by
  have hP : (T.filter (· ≤ u)).card = (T.filter (· < u)).card + 1 := by
    have e1 : T.filter (· ≤ u) = insert u (T.filter (· < u)) := by
      ext x
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨hx, hxu⟩
        rcases Nat.lt_or_eq_of_le hxu with h | h
        · exact Or.inr ⟨hx, h⟩
        · exact Or.inl h
      · rintro (h | ⟨hx, hxu⟩)
        · exact ⟨h ▸ hu, h.le⟩
        · exact ⟨hx, hxu.le⟩
    rw [e1, card_insert_of_notMem (by simp)]
  have hsub : (T.filter (· < u + 2 * a)) ∪ ((T.filter (· < u + a)).image (· + e)) ∪
      ((T.filter (· ≤ u)).image (· + (d + e))) ⊆ Finset.Ico a (u + 2 * a) := by
    intro y hy
    simp only [mem_union, mem_filter, mem_image, mem_Ico] at hy ⊢
    rcases hy with (⟨hy, hlt⟩ | ⟨x, ⟨hx, hlt⟩, rfl⟩) | ⟨x, ⟨hx, hle⟩, rfl⟩
    · exact ⟨hTa y hy, hlt⟩
    · have := hTa x hx
      omega
    · have := hTa x hx
      omega
  have hd1 : Disjoint (T.filter (· < u + 2 * a)) ((T.filter (· < u + a)).image (· + e)) := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    simp only [mem_filter, mem_image] at hy hy'
    obtain ⟨x, ⟨hx, hlt⟩, rfl⟩ := hy'
    exact h2 x hx hlt hy.1
  have hd2 : Disjoint ((T.filter (· < u + 2 * a)) ∪ ((T.filter (· < u + a)).image (· + e)))
      ((T.filter (· ≤ u)).image (· + (d + e))) := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    simp only [mem_union, mem_filter, mem_image] at hy hy'
    obtain ⟨x, ⟨hx, hle⟩, rfl⟩ := hy'
    rcases hy with ⟨hy, -⟩ | ⟨z, ⟨hz, -⟩, hzx⟩
    · exact h3 x hx hle hy
    · have hzd : z = x + d := by omega
      exact h1 x hx hle (hzd ▸ hz)
  have hcard := Finset.card_le_card hsub
  rw [card_union_of_disjoint hd2, card_union_of_disjoint hd1,
    card_image_of_injective _ (add_left_injective e),
    card_image_of_injective _ (add_left_injective (d + e)), hP, Nat.card_Ico] at hcard
  omega

end Green3StepPacking

theorem OMA.solution : OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1.H1 :=
  fun T a u d e hTa hu hea hde h1 h2 h3 =>
    Green3StepPacking.three_prefix_lt T a u d e hTa hu hea hde h1 h2 h3
