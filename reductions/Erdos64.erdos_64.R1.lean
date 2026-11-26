import FormalConjectures.ErdosProblems.«64»
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-! Reduce to cubic graphs and graphs in which every edge and every neighborhood meets a degree-three vertex. -/

namespace OMA.R_Erdos64_erdos_64_R1

open SimpleGraph

-- The cubic case.
def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    Nonempty V → (∀ v, G.degree v = 3) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

-- The noncubic case after removing dispensable edges and vertices.
def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    3 ≤ G.minDegree → (∃ v, 3 < G.degree v) →
    (∀ ⦃a b⦄, G.Adj a b → G.degree a = 3 ∨ G.degree b = 3) →
    (∀ a, ∃ b, G.Adj a b ∧ G.degree b = 3) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

theorem nonempty_of_min_degree {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (minimum : 3 ≤ G.minDegree) : Nonempty V := by
  rcases isEmpty_or_nonempty V with hv | hv
  · haveI := hv
    have hz := G.minDegree_of_subsingleton
    omega
  · exact hv

theorem delete_edge_degree {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (a b : V) (minimum : 3 ≤ G.minDegree)
    (ha : 3 < G.degree a) (hb : 3 < G.degree b) (x : V) :
    3 ≤ (G.deleteEdges {s(a, b)}).degree x := by
  let H := G.deleteEdges {s(a, b)}
  change 3 ≤ H.degree x
  let removed : Finset V := if x = a then {b} else if x = b then {a} else ∅
  have inclusion : G.neighborFinset x ⊆ H.neighborFinset x ∪ removed := by
    intro y hy
    have adj := (G.mem_neighborFinset x y).mp hy
    apply Finset.mem_union.mpr
    by_cases h : s(x, y) = s(a, b)
    · right
      rcases (Sym2.mk_eq_mk_iff (p := (x, y)) (q := (a, b))).mp h with hd | hd
      · have hx : x = a := congrArg Prod.fst hd
        have hyb : y = b := congrArg Prod.snd hd
        simp [removed, hx, hyb]
      · have hx : x = b := congrArg Prod.fst hd
        have hya : y = a := congrArg Prod.snd hd
        by_cases hab : a = b <;> simp [removed, hx, hya, hab, eq_comm]
    · left
      apply (H.mem_neighborFinset x y).mpr
      exact SimpleGraph.deleteEdges_adj.mpr ⟨adj, by simpa using h⟩
  have cardinal : G.degree x ≤ H.degree x + removed.card := by
    simpa only [card_neighborFinset_eq_degree] using
      (Finset.card_le_card inclusion).trans (Finset.card_union_le _ _)
  have loss : removed.card ≤ 1 := by
    dsimp [removed]
    split
    · simp
    · split <;> simp
  by_cases endpoints : x = a ∨ x = b
  · have larger : 3 < G.degree x := endpoints.elim (fun hx => hx.symm ▸ ha)
      (fun hx => hx.symm ▸ hb)
    omega
  · have noLoss : removed.card = 0 := by simp [removed, (not_or.mp endpoints).1,
      (not_or.mp endpoints).2]
    have lower := minimum.trans (G.minDegree_le_degree x)
    omega

theorem solve_restricted (cubic : H1) (mixed : H2) (n : ℕ) :
    ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      Fintype.card V + G.edgeFinset.card = n → 3 ≤ G.minDegree →
      ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V G finite dec measure minimum
    classical
    haveI : Nonempty V := nonempty_of_min_degree G minimum
    by_cases uniform : ∀ v, G.degree v = 3
    · exact cubic V G inferInstance uniform
    have mixedDegrees : ∃ v, 3 < G.degree v := by
      rw [not_forall] at uniform
      obtain ⟨v, hv⟩ := uniform
      have lower := minimum.trans (G.minDegree_le_degree v)
      exact ⟨v, by omega⟩
    by_cases edgeCondition : ∀ ⦃a b⦄, G.Adj a b → G.degree a = 3 ∨ G.degree b = 3
    · by_cases vertexCondition : ∀ a, ∃ b, G.Adj a b ∧ G.degree b = 3
      · exact mixed V G minimum mixedDegrees edgeCondition vertexCondition
      · rw [not_forall] at vertexCondition
        obtain ⟨a, bad⟩ := vertexCondition
        let S : Set V := {v | v ≠ a}
        let H := G.induce S
        have positive : 0 < G.degree a := Nat.lt_of_lt_of_le (by decide)
          (minimum.trans (G.minDegree_le_degree a))
        obtain ⟨neighbor, hneighbor⟩ := (G.degree_pos_iff_exists_adj a).mp positive
        haveI : Nonempty S := ⟨⟨neighbor, hneighbor.ne.symm⟩⟩
        have minimumH : 3 ≤ H.minDegree := by
          apply H.le_minDegree_of_forall_le_degree
          intro x
          have lower := minimum.trans (G.minDegree_le_degree x.val)
          by_cases hx : G.Adj x.val a
          · have higher : 3 < G.degree x.val := by
              have ne : G.degree x.val ≠ 3 := fun eq => bad ⟨x.val, hx.symm, eq⟩
              omega
            have erased : (H.neighborFinset x).map (.subtype (· ∈ S)) =
                (G.neighborFinset x.val).erase a := by
              rw [SimpleGraph.map_neighborFinset_induce]
              ext y
              simp [S, and_comm]
            have cards := congrArg Finset.card erased
            rw [Finset.card_map, card_neighborFinset_eq_degree,
              Finset.card_erase_of_mem ((G.mem_neighborFinset x.val a).mpr hx),
              card_neighborFinset_eq_degree] at cards
            omega
          · have unchanged : H.degree x = G.degree x.val :=
              SimpleGraph.degree_induce_of_neighborSet_subset
                (fun y hy eq => hx (eq ▸ hy))
            omega
        have hv : Fintype.card S < Fintype.card V :=
          Fintype.card_lt_of_injective_of_notMem Subtype.val Subtype.val_injective
            (b := a) (fun ⟨x, eq⟩ => x.property eq)
        have he : H.edgeFinset.card ≤ G.edgeFinset.card := by
          have mapped := SimpleGraph.map_edgeFinset_induce (s := S) (G := G)
          rw [← Finset.card_map (f := (Function.Embedding.subtype (· ∈ S)).sym2Map), mapped]
          exact Finset.card_le_card Finset.inter_subset_left
        have smaller : Fintype.card S + H.edgeFinset.card < n := by omega
        obtain ⟨k, v, c, hk, hc, hl⟩ := ih _ smaller S H rfl minimumH
        let lift : H →g G := ⟨Subtype.val, fun h => h⟩
        exact ⟨k, v.val, c.map lift, hk, hc.map Subtype.val_injective, by simpa using hl⟩
    · push Not at edgeCondition
      obtain ⟨a, b, hadj, ha, hb⟩ := edgeCondition
      have hda := minimum.trans (G.minDegree_le_degree a)
      have hdb := minimum.trans (G.minDegree_le_degree b)
      let H := G.deleteEdges {s(a, b)}
      have minimumH : 3 ≤ H.minDegree :=
        H.le_minDegree_of_forall_le_degree 3
          (delete_edge_degree G a b minimum (by omega) (by omega))
      have reduced : H.edgeFinset = G.edgeFinset.erase s(a, b) := by
        ext e
        simp [H, edgeSet_deleteEdges, and_comm]
      have edgeOf : s(a, b) ∈ G.edgeFinset := G.mem_edgeFinset.mpr hadj
      have strict : H.edgeFinset.card < G.edgeFinset.card := by
        rw [reduced]
        exact Finset.card_erase_lt_of_mem edgeOf
      have smaller : Fintype.card V + H.edgeFinset.card < n := by omega
      obtain ⟨k, v, c, hk, hc, hl⟩ := ih _ smaller V H rfl minimumH
      let leG : H ≤ G := G.deleteEdges_le _
      exact ⟨k, v, c.mapLe leG, hk, hc.mapLe leG, by simpa using hl⟩

theorem main : H1 → H2 → type_of% @Erdos64.erdos_64 := by
  intro cubic mixed V G finite dec minimum
  classical
  let e := (Fintype.equivFin V).symm
  let H := G.comap e
  let i : H ≃g G := SimpleGraph.Iso.comap e G
  have minimumH : 3 ≤ H.minDegree := i.minDegree_eq ▸ minimum
  obtain ⟨k, v, c, hk, hc, hl⟩ := solve_restricted cubic mixed _ _ H rfl minimumH
  exact ⟨k, i v, c.map i.toHom, hk, hc.map i.injective, by simpa using hl⟩

end OMA.R_Erdos64_erdos_64_R1
