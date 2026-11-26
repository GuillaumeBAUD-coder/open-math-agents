import OMAReductions.R_Arxiv_2107_00295_independentDominationOdd_R1
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Fintype.BigOperators

/-! An independent dominating set can be assembled from minimum sets in the components. -/

lemma OMA.exists_minimal_independent_dominating_set {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    ∃ s : Finset V, G.IsNIndepDominatingSet G.indepDominationNumber s := by
  classical
  obtain ⟨s, hs⟩ := G.maximumIndepSet_exists
  have hmax := hs.isMaximalIndepSet s
  have hdom : G.IsDominating s := by
    intro v
    by_cases hv : v ∈ (s : Set V)
    · exact Or.inl hv
    · right
      by_contra hmissing
      have hins : G.IsIndepSet (insert v (s : Set V)) := by
        apply Set.Pairwise.insert_of_notMem hv hs.isIndepSet
        intro w hw
        exact ⟨fun h ↦ hmissing ⟨w, hw, h⟩, fun h ↦ hmissing ⟨w, hw, h.symm⟩⟩
      have hsub : insert v (s : Set V) ⊆ s := hmax.2 hins (Set.subset_insert _ _)
      exact hv (hsub (Set.mem_insert _ _))
  have hnonempty : {n | ∃ s : Finset V, G.IsNIndepDominatingSet n s}.Nonempty :=
    ⟨s.card, s, hs.isIndepSet, hdom, rfl⟩
  exact Nat.sInf_mem hnonempty

lemma OMA.degree_in_component {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.ConnectedComponent) [Fintype ↥c] [DecidableRel c.toSimpleGraph.Adj] (v : ↥c) :
    c.toSimpleGraph.degree v = G.degree v.val := by
  classical
  let e : c.toSimpleGraph.neighborSet v ≃ G.neighborSet v.val :=
    { toFun := fun w ↦ ⟨w.val.val, w.property⟩
      invFun := fun w ↦ ⟨⟨w.val, c.mem_supp_of_adj_mem_supp v.property w.property⟩, w.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using Fintype.card_congr e

set_option maxHeartbeats 1000000 in
theorem OMA.solution : OMA.R_Arxiv_2107_00295_independentDominationOdd_R1.H3 := by
  intro D A B bound V _ _ G _ hmin hmax
  classical
  have hcomponent (c : G.ConnectedComponent) :
      A * c.toSimpleGraph.indepDominationNumber ≤ B * Fintype.card (↥c) := by
    have hconn := c.connected_toSimpleGraph
    have : Nonempty (↥c) := hconn.nonempty
    have hpos : 0 < c.toSimpleGraph.minDegree := by
      apply c.toSimpleGraph.le_minDegree_of_forall_le_degree 1
      intro v
      rw [OMA.degree_in_component G c v]
      exact hmin.trans_le (G.minDegree_le_degree v.val)
    have hdegree : c.toSimpleGraph.maxDegree ≤ D := by
      apply c.toSimpleGraph.maxDegree_le_of_forall_degree_le
      intro v
      rw [OMA.degree_in_component G c v]
      exact (G.degree_le_maxDegree v.val).trans hmax
    exact bound (↥c) c.toSimpleGraph hpos hdegree hconn
  choose sets hsets using
    fun c : G.ConnectedComponent ↦ OMA.exists_minimal_independent_dominating_set c.toSimpleGraph
  let e : (Σ c : G.ConnectedComponent, ↥c) ≃ V :=
    Equiv.sigmaFiberEquiv G.connectedComponentMk
  let s : Finset V := (Finset.univ.sigma sets).map e.toEmbedding
  have hmem (c : G.ConnectedComponent) (v : ↥c) : v.val ∈ s ↔ v ∈ sets c := by
    change e ⟨c, v⟩ ∈ (Finset.univ.sigma sets).map e.toEmbedding ↔ _
    rw [Finset.mem_map_equiv, e.symm_apply_apply]
    simp
  have hindep : G.IsIndepSet s := by
    intro v hv w hw hne hadj
    let c := G.connectedComponentMk v
    let v' : ↥c := ⟨v, rfl⟩
    let w' : ↥c := ⟨w, c.mem_supp_of_adj_mem_supp v'.property hadj⟩
    have hv' : v' ∈ sets c := (hmem c v').mp hv
    have hw' : w' ∈ sets c := (hmem c w').mp hw
    exact (hsets c).isIndep hv' hw' (fun h ↦ hne (congrArg Subtype.val h)) hadj
  have hdom : G.IsDominating s := by
    intro v
    let c := G.connectedComponentMk v
    let v' : ↥c := ⟨v, rfl⟩
    rcases (hsets c).isDominating v' with hv | ⟨w, hw, hadj⟩
    · exact Or.inl ((hmem c v').mpr hv)
    · exact Or.inr ⟨w.val, (hmem c w).mpr hw, hadj⟩
  have hle : G.indepDominationNumber ≤ s.card :=
    Nat.sInf_le ⟨s, hindep, hdom, rfl⟩
  have hcard : s.card = ∑ c : G.ConnectedComponent, c.toSimpleGraph.indepDominationNumber := by
    simp only [s, Finset.card_map, Finset.card_sigma, fun c ↦ (hsets c).card_eq]
  have hpartition : (∑ c : G.ConnectedComponent, Fintype.card (↥c)) = Fintype.card V := by
    rw [← Fintype.card_sigma, Fintype.card_congr e]
  calc
    _ ≤ A * s.card := Nat.mul_le_mul_left A hle
    _ = ∑ c : G.ConnectedComponent, A * c.toSimpleGraph.indepDominationNumber := by
      rw [hcard, Finset.mul_sum]
    _ ≤ ∑ c : G.ConnectedComponent, B * Fintype.card (↥c) :=
      Finset.sum_le_sum (fun c _ ↦ hcomponent c)
    _ = _ := by rw [← Finset.mul_sum, hpartition]
