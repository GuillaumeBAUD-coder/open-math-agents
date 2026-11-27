import OMAReductions.R_Green37_green_37_lower_bound_R1
import Mathlib

-- Step Green37.green_37_lower_bound.R1.H2: hypothesis H2 of reduction Green37.green_37_lower_bound.R1
-- Credit: @ivillar
--
-- Proof. An arithmetic progression of length k2 and difference d contains the progression of
-- length k1 <= k2 with the same first term and difference, so every set covering (N, k2)
-- also covers (N, k1). The cover sizes for k2 form a nonempty subset of those for k1
-- (the interval {0, ..., k2 N} covers), so the infimum for k1 is at most the one for k2.

namespace OMA.Green37H2

theorem containsAP_mono (A : Set ℕ) (k₁ k₂ d : ℕ) (hk : k₁ ≤ k₂) (hd : 1 ≤ d)
    (h : A.ContainsAP k₂ d) : A.ContainsAP k₁ d := by
  obtain ⟨a, s, hsA, hcard, hs⟩ := h
  refine ⟨a, ((Finset.range k₁).image (fun i ↦ a + i * d) : Set ℕ), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    apply hsA
    rw [hs]
    refine ⟨i, ?_, by simp [smul_eq_mul]⟩
    exact_mod_cast lt_of_lt_of_le (Finset.mem_range.mp hi) hk
  · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective _
        (fun i j h ↦ Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel h)), Finset.card_range]
  · ext x
    simp [smul_eq_mul]

theorem cover_range (N k : ℕ) :
    Green37.IsAPCover ((Finset.range (k * N + 1) : Finset ℕ) : Set ℕ) N k := by
  intro d hd
  refine ⟨0, ((Finset.range k).image (fun i ↦ i * d) : Set ℕ), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_coe, Finset.mem_range] at hi ⊢
    exact Nat.lt_succ_of_le (Nat.mul_le_mul (Nat.le_of_lt hi) hd.2)
  · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective _
        (fun _ _ h ↦ Nat.eq_of_mul_eq_mul_right hd.1 h), Finset.card_range]
  · ext x
    simp

end OMA.Green37H2

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H2 := by
  unfold OMA.R_Green37_green_37_lower_bound_R1.H2
  intro N k₁ k₂ hk
  unfold Green37.m
  apply csInf_le_csInf (OrderBot.bddBelow _)
  · exact ⟨_, Finset.range (k₂ * N + 1), rfl, OMA.Green37H2.cover_range N k₂⟩
  · rintro m ⟨A, hA, hcov⟩
    exact ⟨A, hA, fun d hd => OMA.Green37H2.containsAP_mono _ k₁ k₂ d hk hd.1 (hcov d hd)⟩
