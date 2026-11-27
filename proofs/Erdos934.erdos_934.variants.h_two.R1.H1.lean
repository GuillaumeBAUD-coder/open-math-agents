import OMAReductions.R_Erdos934_erdos_934_variants_h_two_R1
import Mathlib

-- Step Erdos934.erdos_934.variants.h_two.R1.H1: hypothesis H1 of reduction Erdos934.erdos_934.variants.h_two.R1
-- Credit: @luciusacarr

/-! The blow-up of the 5-cycle with `k` vertices per class (on `Fin (5 * k)`, class = index mod 5)
is `2k`-regular, has `5k²` edges, and any two of its edges are joined by an edge. -/

open Erdos934

namespace OMA934h2

/-- Blow-up of `C₅` on `Fin (5 * k)`: the class of `u` is `u % 5`, and classes `i`, `i + 1`
(mod `5`) are completely joined. -/
def B (k : ℕ) : SimpleGraph (Fin (5 * k)) where
  Adj u v := (u.val % 5 + 1) % 5 = v.val % 5 ∨ (v.val % 5 + 1) % 5 = u.val % 5
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun _ h => by omega⟩

instance (k : ℕ) : DecidableRel (B k).Adj := fun u v => by unfold B; infer_instance

/-- Each residue class mod `5` in `Fin (5 * k)` has `k` elements. -/
lemma card_class (k r : ℕ) (hr : r < 5) :
    ((Finset.univ : Finset (Fin (5 * k))).filter (fun u => u.val % 5 = r)).card = k := by
  have : ((Finset.univ : Finset (Fin (5 * k))).filter (fun u => u.val % 5 = r)) =
      (Finset.univ : Finset (Fin k)).image (fun i => (⟨5 * i.val + r, by omega⟩ : Fin (5 * k))) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hu
      exact ⟨⟨u.val / 5, by omega⟩, by ext; simp; omega⟩
    · rintro ⟨i, -, rfl⟩
      simp; omega
  rw [this, Finset.card_image_of_injective _ (fun i j hij => by
    simp only [Fin.mk.injEq] at hij; ext; omega)]
  simp

lemma degree_B (k : ℕ) (v : Fin (5 * k)) : (B k).degree v = 2 * k := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : (B k).neighborFinset v =
      ((Finset.univ : Finset (Fin (5 * k))).filter (fun u => u.val % 5 = (v.val % 5 + 1) % 5)) ∪
      ((Finset.univ : Finset (Fin (5 * k))).filter (fun u => u.val % 5 = (v.val % 5 + 4) % 5)) := by
    ext u
    rw [SimpleGraph.mem_neighborFinset]
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    show (_ ∨ _) ↔ _
    omega
  rw [this, Finset.card_union_of_disjoint, card_class _ _ (by omega), card_class _ _ (by omega)]
  · ring
  · rw [Finset.disjoint_filter]; intro u _ h1 h2; omega

lemma not_far (k : ℕ) : ¬ HasFarEdges (B k) 2 := by
  rintro ⟨u, v, w, x, huv, hwx, h⟩
  have key : (B k).Adj u w ∨ (B k).Adj u x ∨ (B k).Adj v w ∨ (B k).Adj v x := by
    simp only [B] at huv hwx ⊢
    omega
  have bad : ∀ a b, (B k).Adj a b → ¬ ((2 : ℕ∞) ≤ (B k).edist a b) := by
    intro a b hab hle
    rw [SimpleGraph.edist_eq_one_iff_adj.mpr hab] at hle
    norm_num at hle
  rcases key with hk | hk | hk | hk
  · exact bad _ _ hk (h u (by simp) w (by simp))
  · exact bad _ _ hk (h u (by simp) x (by simp))
  · exact bad _ _ hk (h v (by simp) w (by simp))
  · exact bad _ _ hk (h v (by simp) x (by simp))

theorem main_H1 : OMA.R_Erdos934_erdos_934_variants_h_two_R1.H1 := by
  unfold OMA.R_Erdos934_erdos_934_variants_h_two_R1.H1
  rintro d ⟨k, rfl⟩
  refine ⟨5 * k, B k, fun v => ?_, ?_, not_far k⟩
  · rw [Set.ncard_eq_toFinset_card', ← SimpleGraph.neighborFinset_def,
      SimpleGraph.card_neighborFinset_eq_degree, degree_B]
    omega
  · have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges (B k)
    simp only [degree_B, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    have : 5 * (k + k) ^ 2 / 4 = 5 * k ^ 2 := by ring_nf; omega
    rw [this]
    nlinarith

end OMA934h2

theorem OMA.solution : OMA.R_Erdos934_erdos_934_variants_h_two_R1.H1 := OMA934h2.main_H1
