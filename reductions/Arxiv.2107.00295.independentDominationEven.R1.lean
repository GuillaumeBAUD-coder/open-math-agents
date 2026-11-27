import FormalConjectures.Arxiv.«2107.00295».IndependentDomination
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Fintype.BigOperators

/-!
# Independent domination with an even degree bound

Separate the maximum-degree-two case and the connected case of Corollary 1.3
of Cho, Kim, Kim and Oum (https://arxiv.org/abs/2202.09594). Minimum independent
dominating sets of the components give a global independent dominating set.
The corresponding split for odd degrees appears in the companion reduction.
-/

namespace OMA.R_Arxiv_2107_00295_independentDominationEven_R1

open Finset SimpleGraph

private theorem exists_optimal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    ∃ S : Finset V, G.IsNIndepDominatingSet G.indepDominationNumber S := by
  classical
  obtain ⟨S, hS⟩ := G.maximumIndepSet_exists
  have hdom : G.IsDominating S := by
    intro v
    by_cases hv : v ∈ S
    · exact Or.inl hv
    · right
      by_contra hd
      have hins : G.IsIndepSet (insert v (S : Set V)) := by
        apply Set.Pairwise.insert_of_notMem hv hS.isIndepSet
        intro w hw
        exact ⟨fun h => hd ⟨w, hw, h⟩, fun h => hd ⟨w, hw, h.symm⟩⟩
      exact hv ((hS.isMaximalIndepSet S).2 hins (Set.subset_insert _ _) (Set.mem_insert _ _))
  have he : {n | ∃ T : Finset V, G.IsNIndepDominatingSet n T}.Nonempty :=
    ⟨S.card, S, hS.isIndepSet, hdom, rfl⟩
  exact Nat.sInf_mem he

private theorem indepDomination_le_iso {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} {K : SimpleGraph W}
    (e : G ≃g K) : K.indepDominationNumber ≤ G.indepDominationNumber := by
  obtain ⟨S, hS⟩ := exists_optimal G
  let T := S.map e.toEquiv.toEmbedding
  have hmem (x : W) : x ∈ T ↔ e.symm x ∈ S := by
    simp only [T, Finset.mem_map_equiv]
    rfl
  apply Nat.sInf_le
  refine ⟨T, ?_, ?_, ?_⟩
  · intro x hx y hy hxy hAdj
    exact hS.isIndep ((hmem x).mp hx) ((hmem y).mp hy)
      (fun h => hxy (e.symm.injective h)) (e.symm.map_rel_iff.mpr hAdj)
  · intro x
    rcases hS.isDominating (e.symm x) with hx | ⟨y, hy, hAdj⟩
    · exact Or.inl ((hmem x).mpr hx)
    · apply Or.inr
      refine ⟨e y, (hmem (e y)).mpr (by simpa using hy), ?_⟩
      apply e.symm.map_rel_iff.mp
      simpa using hAdj
  · exact (card_map _).trans hS.card_eq

private theorem component_degree {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : G.ConnectedComponent) [Fintype ↥c]
    [DecidableRel c.toSimpleGraph.Adj] (x : ↥c) :
    c.toSimpleGraph.degree x = G.degree x.val := by
  let f : c.toSimpleGraph.neighborSet x ≃ G.neighborSet x.val := {
    toFun := fun y => ⟨y.val.val, y.property⟩
    invFun := fun y => ⟨⟨y.val, c.mem_supp_of_adj_mem_supp x.property y.property⟩, y.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  exact Fintype.card_congr f

private theorem combine_components {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D A B : ℕ)
    (hmin : 0 < G.minDegree) (hmax : G.maxDegree ≤ D)
    (hConnected : ∀ (W : Type) [Fintype W] [DecidableEq W] (K : SimpleGraph W)
      [DecidableRel K.Adj], 0 < K.minDegree → K.maxDegree ≤ D → K.Connected →
        A * K.indepDominationNumber ≤ B * Fintype.card W) :
    A * G.indepDominationNumber ≤ B * Fintype.card V := by
  classical
  choose S hS using fun c : G.ConnectedComponent => exists_optimal c.toSimpleGraph
  let T (c : G.ConnectedComponent) : Finset V := (S c).map ⟨Subtype.val, Subtype.val_injective⟩
  let U := (univ : Finset G.ConnectedComponent).biUnion T
  have hmem (x : V) : x ∈ U ↔ ∃ (c : G.ConnectedComponent) (y : ↥c), y ∈ S c ∧ y.val = x := by
    constructor
    · intro hx
      obtain ⟨c, _, hc⟩ := mem_biUnion.mp hx
      obtain ⟨y, hy, he⟩ := mem_map.mp hc
      exact ⟨c, y, hy, he⟩
    · rintro ⟨c, y, hy, rfl⟩
      exact mem_biUnion.mpr ⟨c, mem_univ _, mem_map.mpr ⟨y, hy, rfl⟩⟩
  have hind : G.IsIndepSet U := by
    intro x hx y hy hne hAdj
    obtain ⟨c, x', hx', rfl⟩ := (hmem x).mp hx
    obtain ⟨d, y', hy', rfl⟩ := (hmem y).mp hy
    have hc : G.connectedComponentMk x'.val = c := x'.property
    have hd : G.connectedComponentMk y'.val = d := y'.property
    have he : c = d := hc.symm.trans ((ConnectedComponent.sound hAdj.reachable).trans hd)
    subst d
    exact (hS c).isIndep hx' hy' (fun h => hne (congrArg Subtype.val h)) hAdj
  have hdom : G.IsDominating U := by
    intro x
    let c := G.connectedComponentMk x
    let x' : ↥c := ⟨x, rfl⟩
    rcases (hS c).isDominating x' with hx | ⟨y, hy, hAdj⟩
    · exact Or.inl ((hmem x).mpr ⟨c, x', hx, rfl⟩)
    · exact Or.inr ⟨y.val, (hmem y.val).mpr ⟨c, y, hy, rfl⟩, hAdj⟩
  have hopt : G.indepDominationNumber ≤ U.card := Nat.sInf_le ⟨U, hind, hdom, rfl⟩
  have hcard : U.card ≤ ∑ c : G.ConnectedComponent, c.toSimpleGraph.indepDominationNumber := by
    refine card_biUnion_le.trans_eq ?_
    apply sum_congr rfl
    intro c _
    exact (card_map _).trans (hS c).card_eq
  have hbound (c : G.ConnectedComponent) :
      A * c.toSimpleGraph.indepDominationNumber ≤ B * Fintype.card (↥c) := by
    have hc := c.connected_toSimpleGraph
    have : Nonempty (↥c) := hc.nonempty
    apply hConnected (↥c) c.toSimpleGraph _ _ hc
    · apply c.toSimpleGraph.le_minDegree_of_forall_le_degree 1
      intro v
      exact hmin.trans_le ((G.minDegree_le_degree v.val).trans_eq (component_degree G c v).symm)
    · apply c.toSimpleGraph.maxDegree_le_of_forall_degree_le
      intro v
      exact (component_degree G c v).le.trans ((G.degree_le_maxDegree v.val).trans hmax)
  calc
    _ ≤ A * (∑ c : G.ConnectedComponent, c.toSimpleGraph.indepDominationNumber) :=
      Nat.mul_le_mul_left _ (hopt.trans hcard)
    _ = ∑ c : G.ConnectedComponent, A * c.toSimpleGraph.indepDominationNumber :=
      mul_sum _ _ _
    _ ≤ ∑ c : G.ConnectedComponent, B * Fintype.card (↥c) :=
      sum_le_sum fun c _ => hbound c
    _ = _ := by
      have e : (Σ c : G.ConnectedComponent, ↥c) ≃ V := Equiv.sigmaFiberEquiv G.connectedComponentMk
      rw [← mul_sum, ← Fintype.card_sigma, Fintype.card_congr e]

/-- The sharp independent domination bound in isolate-free graphs of maximum degree at most two. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    0 < G.minDegree → G.maxDegree ≤ 2 → 2 * G.indepDominationNumber ≤ Fintype.card V

/-- The connected case of Corollary 1.3 with an even degree bound of at least four. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ),
    4 ≤ D → Even D → 0 < G.minDegree → G.maxDegree ≤ D → G.Connected →
    (D + 2)^2 * G.indepDominationNumber ≤ (D^2 + 4) * Fintype.card V

theorem main : H1 → H2 → type_of% @Arxiv.«2107.00295».independentDominationEven := by
  intro small connected V _ _ G _ hIso hEven
  classical
  let e := Fintype.equivFin V
  let K := G.map e.toEmbedding
  have hIsoK : G ≃g K := SimpleGraph.Iso.map e G
  let D := G.maxDegree
  have hD : K.maxDegree = D := hIsoK.maxDegree_eq.symm
  have hP : 0 < K.minDegree := hIsoK.minDegree_eq ▸ hIso
  have hc : Fintype.card (Fin (Fintype.card V)) = Fintype.card V := Fintype.card_fin _
  have hDom : G.indepDominationNumber ≤ K.indepDominationNumber :=
    indepDomination_le_iso hIsoK.symm
  change (D+2)^2 * G.indepDominationNumber ≤ (D^2+4) * Fintype.card V
  apply (Nat.mul_le_mul_left _ hDom).trans
  by_cases hsmall : D ≤ 2
  · have hd0 : 0 < D := hIso.trans_le (G.minDegree_le_maxDegree)
    have hd : D = 2 := by
      obtain ⟨n, hn⟩ := hEven
      change D = n + n at hn
      omega
    have h := small _ K hP (hD.trans_le hsmall)
    rw [hc] at h
    rw [hd]
    norm_num
    omega
  · have hlarge : 4 ≤ D := by
      obtain ⟨n, hn⟩ := hEven
      change D = n + n at hn
      omega
    have h := combine_components K D ((D+2)^2) (D^2+4) hP hD.le
      (fun W _ _ F _ hp hd hconn => connected W F D hlarge hEven hp hd hconn)
    rw [hc] at h
    exact h

end OMA.R_Arxiv_2107_00295_independentDominationEven_R1
