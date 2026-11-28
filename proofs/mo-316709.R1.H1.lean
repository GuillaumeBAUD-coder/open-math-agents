import OMAReductions.R_mo_316709_R1
import Mathlib

/-! Two subgroups of coprime finite index satisfy `A * B = G` (count cosets: `A ⧸ (A ⊓ B)` embeds
in `G ⧸ B` and both have `[G : B]` elements), so any two of their cosets meet. -/

namespace OMA.Step_mo_316709_R1_H1

open Subgroup
open scoped Pointwise

/-- Subgroups of coprime finite index: every element is a product `a * b`, `a ∈ A`, `b ∈ B`. -/
theorem mul_cover {G : Type*} [Group G] (A B : Subgroup G) (hA : A.index ≠ 0) (hB : B.index ≠ 0)
    (hc : Nat.Coprime A.index B.index) (x : G) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  -- index of the intersection is the product
  have hinf : (A ⊓ B).index = A.index * B.index := by
    apply le_antisymm index_inf_le
    apply Nat.le_of_dvd
    · exact Nat.pos_of_ne_zero (index_inf_ne_zero hA hB)
    · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hc (index_dvd_of_le inf_le_left)
        (index_dvd_of_le inf_le_right)
  have hrel : B.relIndex A = B.index := by
    have h := relIndex_mul_index (H := A ⊓ B) (K := A) inf_le_left
    rw [inf_relIndex_left, hinf] at h
    have hA0 : 0 < A.index := Nat.pos_of_ne_zero hA
    have : B.relIndex A * A.index = B.index * A.index := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right hA0 this
  -- the embedding A ⧸ (B ⊓ A) ↪ G ⧸ B is a bijection by cardinality
  let e := quotientSubgroupOfEmbeddingOfLE B (le_top : A ≤ ⊤)
  have hfin : Finite (↥(⊤ : Subgroup G) ⧸ B.subgroupOf ⊤) := by
    apply Nat.finite_of_card_ne_zero
    have : Nat.card (↥(⊤ : Subgroup G) ⧸ B.subgroupOf ⊤) = B.relIndex ⊤ := rfl
    rw [this, relIndex_top_right]; exact hB
  have hcard : Nat.card (↥A ⧸ B.subgroupOf A) = Nat.card (↥(⊤ : Subgroup G) ⧸ B.subgroupOf ⊤) := by
    have h1 : Nat.card (↥A ⧸ B.subgroupOf A) = B.relIndex A := rfl
    have h2 : Nat.card (↥(⊤ : Subgroup G) ⧸ B.subgroupOf ⊤) = B.relIndex ⊤ := rfl
    rw [h1, h2, hrel, relIndex_top_right]
  have hsurj : Function.Surjective e := by
    have := (Function.Injective.bijective_of_nat_card_le e.injective hcard.ge)
    exact this.2
  obtain ⟨q, hq⟩ := hsurj (QuotientGroup.mk (⟨x, mem_top x⟩ : ↥(⊤ : Subgroup G)))
  induction q using QuotientGroup.induction_on with
  | H a =>
    rw [quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq] at hq
    refine ⟨a, a.2, (a : G)⁻¹ * x, ?_, by group⟩
    simpa [mem_subgroupOf] using hq

theorem H1' : ∀ (G : Type) [Group G] (H : Fin 2 → Subgroup G) (a : Fin 2 → G),
    (∀ i, (H i).index ≠ 0) →
    Pairwise (fun i j => Disjoint (a i • (H i : Set G)) (a j • (H j : Set G))) →
    ∃ i j : Fin 2, i < j ∧ 2 ≤ Nat.gcd (H i).index (H j).index := by
  intro G _ H a hfin hdis
  refine ⟨0, 1, by decide, ?_⟩
  by_contra hlt
  have hpos : 0 < Nat.gcd (H 0).index (H 1).index := Nat.gcd_pos_of_pos_left _
    (Nat.pos_of_ne_zero (hfin 0))
  have hc : Nat.Coprime (H 0).index (H 1).index := by
    unfold Nat.Coprime; omega
  obtain ⟨h, hh, k, hk, hx⟩ := mul_cover (H 0) (H 1) (hfin 0) (hfin 1) hc ((a 0)⁻¹ * a 1)
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hx0 : a 0 * h ∈ a 0 • (H 0 : Set G) := ⟨h, hh, rfl⟩
  have hx1 : a 0 * h ∈ a 1 • (H 1 : Set G) := by
    refine ⟨k⁻¹, (H 1).inv_mem hk, ?_⟩
    have : a 1 = a 0 * (h * k) := by rw [← hx]; group
    simp only [smul_eq_mul]
    rw [this]; group
  exact Set.disjoint_left.mp (hdis h01) hx0 hx1

end OMA.Step_mo_316709_R1_H1

theorem OMA.solution : OMA.R_mo_316709_R1.H1 := OMA.Step_mo_316709_R1_H1.H1'
