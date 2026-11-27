import OMAReductions.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1
import Mathlib

-- Step WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.regularized.R1.H2: hypothesis H2 of reduction WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.regularized.R1
-- Credit: @ivillar
-- H2 := every tree T of order at least two has vertex cover number at most 2 * gamma_t(T).
-- Proof: take a minimum total dominating set D (univ is one, since a connected graph on at least
-- two vertices has no isolated vertex). Each vertex v outside D has a neighbour f v in D, and
-- v maps injectively to the edge s(v, f v), which meets D. A tree has n - 1 edges, so at most
-- |D| - 1 edges avoid D. D together with one endpoint of each edge avoiding D is a vertex cover
-- with at most 2 |D| vertices.

open SimpleGraph

namespace OMA.W372H2

theorem bound {α : Type} [Fintype α] [DecidableEq α] (T : SimpleGraph α) (hT : T.IsTree)
    (D : Finset α) (hD : T.IsTotalDominating (D : Set α)) :
    T.vertexCoverNum.toNat ≤ 2 * D.card := by
  classical
  have hf : ∀ v, ∃ w ∈ (D : Set α), T.Adj v w := hD
  choose f hfD hfadj using hf
  set E := T.edgeFinset with hEdef
  set Eout := E.filter (fun e => ∀ x ∈ e, x ∉ D) with hEout
  set Etouch := E.filter (fun e => ¬ ∀ x ∈ e, x ∉ D) with hEtouch
  have hsplit : Eout.card + Etouch.card = E.card :=
    Finset.card_filter_add_card_filter_not _
  have hinj : Dᶜ.card ≤ Etouch.card := by
    apply Finset.card_le_card_of_injOn (fun v => s(v, f v))
    · intro v _
      simp only [Etouch, Finset.coe_filter, Set.mem_ofPred_eq, E, mem_edgeFinset, mem_edgeSet]
      refine ⟨hfadj v, ?_⟩
      intro h
      exact h (f v) (Sym2.mem_mk_right _ _) (hfD v)
    · intro v hv w hw h
      simp only [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at hv hw
      simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
      rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h1
      · have hx := hfD w
        rw [← h1] at hx
        exact absurd (Finset.mem_coe.mp hx) hv
  have hE : E.card + 1 = Fintype.card α := hT.card_edgeFinset
  have hDc : Dᶜ.card = Fintype.card α - D.card := Finset.card_compl D
  have hDle : D.card ≤ Fintype.card α := Finset.card_le_univ D
  have hout : Eout.card ≤ D.card := by omega
  set C := D ∪ Eout.image (fun e => e.out.1) with hC
  have hCcard : C.card ≤ 2 * D.card := by
    have h1 := Finset.card_union_le D (Eout.image (fun e => e.out.1))
    have h2 : (Eout.image (fun e => e.out.1)).card ≤ Eout.card := Finset.card_image_le
    rw [hC]
    omega
  have hcover : T.IsVertexCover (C : Set α) := by
    intro u v huv
    by_cases hu : u ∈ D
    · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_union_left _ hu))
    by_cases hv : v ∈ D
    · exact Or.inr (Finset.mem_coe.mpr (Finset.mem_union_left _ hv))
    have he : s(u, v) ∈ Eout := by
      simp only [Eout, Finset.mem_filter, E, mem_edgeFinset, mem_edgeSet]
      refine ⟨huv, ?_⟩
      intro x hx
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact hu
      · exact hv
    have hmem : (s(u, v)).out.1 ∈ C :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)
    rcases Sym2.mem_iff.mp (Sym2.out_fst_mem (s(u, v))) with h | h
    · exact Or.inl (Finset.mem_coe.mpr (h ▸ hmem))
    · exact Or.inr (Finset.mem_coe.mpr (h ▸ hmem))
  have hle : T.vertexCoverNum ≤ (C.card : ℕ∞) := by
    have := hcover.vertexCoverNum_le
    rwa [Set.encard_coe_eq_coe_finsetCard] at this
  have : T.vertexCoverNum.toNat ≤ C.card := ENat.toNat_le_of_le_natCast hle
  omega

end OMA.W372H2

theorem OMA.solution :
    OMA.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1.H2 := by
  unfold OMA.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1.H2
  intro α _ _ T hT hcard
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hex : ∃ D : Finset α, T.IsTotalNDominatingSet (Fintype.card α) D := by
    refine ⟨Finset.univ, ⟨?_, Finset.card_univ⟩⟩
    intro v
    obtain ⟨u, hu⟩ := hT.connected.preconnected.exists_adj_of_nontrivial v
    exact ⟨u, by simp, hu⟩
  obtain ⟨D, hD⟩ := Nat.sInf_mem (s := {n | ∃ D : Finset α, T.IsTotalNDominatingSet n D})
    ⟨_, hex⟩
  have h := OMA.W372H2.bound T hT D hD.isTotalDominating
  rw [hD.card_eq] at h
  exact h
