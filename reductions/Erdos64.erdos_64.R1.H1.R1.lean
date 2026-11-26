import OMAReductions.R_Erdos64_erdos_64_R1
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Split the cubic Erdős–Gyárfás case at a bridge. -/

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1

open SimpleGraph

def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.Connected → (∀ v, G.degree v = 3) →
    (∀ ⦃a b⦄, G.Adj a b → ¬ G.IsBridge s(a, b)) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.Connected → ∀ root : V, G.degree root = 2 →
    (∀ v, v ≠ root → G.degree v = 3) →
    (∀ ⦃a b⦄, G.Adj a b → ¬ G.IsBridge s(a, b)) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

theorem degree_component {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (C : G.ConnectedComponent)
    [DecidablePred (· ∈ C.supp)] (v : C.supp) :
    (G.induce C.supp).degree v = G.degree v.val := by
  exact degree_induce_of_neighborSet_subset fun _ h => C.mem_supp_of_adj_mem_supp v.property h

theorem root_degree_after_edge_delete {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V} (adj : G.Adj a b) :
    (G.deleteEdges {s(a, b)}).degree a = G.degree a - 1 := by
  let D := G.deleteEdges {s(a, b)}
  have erased : D.neighborFinset a = (G.neighborFinset a).erase b := by
    ext v
    simp [D, adj.ne, and_comm]
  rw [← card_neighborFinset_eq_degree, erased,
    Finset.card_erase_of_mem ((G.mem_neighborFinset a b).mpr adj),
    card_neighborFinset_eq_degree]

theorem nonendpoint_degree_after_edge_delete {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {a b v : V} (ha : v ≠ a) (hb : v ≠ b) :
    (G.deleteEdges {s(a, b)}).degree v = G.degree v := by
  let D := G.deleteEdges {s(a, b)}
  have unchanged : D.neighborFinset v = G.neighborFinset v := by
    ext w
    simp [D, ha, hb]
  rw [← card_neighborFinset_eq_degree, unchanged, card_neighborFinset_eq_degree]

theorem bridge_side_cycle {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {a b : V} (adj : G.Adj a b) (bridge : G.IsBridge s(a, b))
    (sideCubic : ∀ v, (G.deleteEdges {s(a, b)}).Reachable a v → G.degree v = 3)
    (solve : ∀ (W : Type) (K : SimpleGraph W) [Fintype W] [DecidableRel K.Adj],
      Fintype.card W < Fintype.card V → K.Connected → ∀ root : W, K.degree root = 2 →
      (∀ v, v ≠ root → K.degree v = 3) →
      ∃ (k : ℕ) (v : W) (c : K.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k) :
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  classical
  let D := G.deleteEdges {s(a, b)}
  let C := D.connectedComponentMk a
  let H := D.induce C.supp
  let root : C.supp := ⟨a, rfl⟩
  have notInComponent : b ∉ C.supp := by
    intro hb
    exact (isBridge_iff.mp bridge) (C.reachable_of_mem_supp root.property hb)
  have smaller : Fintype.card C.supp < Fintype.card V :=
    Fintype.card_lt_of_injective_of_notMem Subtype.val Subtype.val_injective
      (b := b) (fun ⟨v, eq⟩ => notInComponent (eq ▸ v.property))
  have hconn : H.Connected := C.connected_toSimpleGraph
  have originalDegree (v : C.supp) : G.degree v.val = 3 :=
    sideCubic _ (C.reachable_of_mem_supp root.property v.property)
  have rootDegree : H.degree root = 2 := by
    rw [degree_component D C root]
    change D.degree a = 2
    rw [root_degree_after_edge_delete G adj, originalDegree root]
  have otherDegree (v : C.supp) (hv : v ≠ root) : H.degree v = 3 := by
    have hva : v.val ≠ a := fun eq => hv (Subtype.ext eq)
    have hvb : v.val ≠ b := fun eq => notInComponent (eq ▸ v.property)
    rw [degree_component D C v, nonendpoint_degree_after_edge_delete G hva hvb, originalDegree]
  obtain ⟨k, v, c, hk, hc, hl⟩ := solve C.supp H smaller hconn root rootDegree otherDegree
  let lift : H →g G := ⟨Subtype.val, fun h => (deleteEdges_adj.mp h).1⟩
  exact ⟨k, v.val, c.map lift, hk, hc.map Subtype.val_injective, by simpa using hl⟩

theorem rooted_case (rooted : H2) (n : ℕ) :
    ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      Fintype.card V = n → G.Connected → ∀ root : V, G.degree root = 2 →
      (∀ v, v ≠ root → G.degree v = 3) →
      ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V G finite dec size connected root degreeRoot cubic
    classical
    by_cases hasBridge : ∃ a b, G.Adj a b ∧ G.IsBridge s(a, b)
    · obtain ⟨a, b, adj, bridge⟩ := hasBridge
      let D := G.deleteEdges {s(a, b)}
      have solveSmaller (W : Type) (K : SimpleGraph W) [Fintype W] [DecidableRel K.Adj]
          (smaller : Fintype.card W < Fintype.card V) (hconn : K.Connected)
          (r : W) (hr : K.degree r = 2) (other : ∀ v, v ≠ r → K.degree v = 3) :
          ∃ (k : ℕ) (v : W) (c : K.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k :=
        ih _ (size ▸ smaller) W K rfl hconn r hr other
      by_cases rootOnSide : D.Reachable a root
      · have swapped : s(b, a) = s(a, b) := Sym2.eq_swap
        refine bridge_side_cycle G adj.symm (swapped ▸ bridge) ?_ solveSmaller
        intro v reachable
        apply cubic v
        intro eq
        have otherPath : D.Reachable b root := by
          simpa only [D, swapped, eq] using reachable
        exact (isBridge_iff.mp bridge) (rootOnSide.trans otherPath.symm)
      · refine bridge_side_cycle G adj bridge ?_ solveSmaller
        intro v reachable
        exact cubic v (fun eq => rootOnSide (eq ▸ reachable))
    · apply rooted V G connected root degreeRoot cubic
      intro a b adj bridge
      exact hasBridge ⟨a, b, adj, bridge⟩

theorem connected_case (bridgeless : H1) (rooted : H2) {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (connected : G.Connected)
    (cubic : ∀ v, G.degree v = 3) :
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  classical
  by_cases hasBridge : ∃ a b, G.Adj a b ∧ G.IsBridge s(a, b)
  · obtain ⟨a, b, adj, bridge⟩ := hasBridge
    apply bridge_side_cycle G adj bridge (fun v _ => cubic v)
    intro W K finite dec smaller
    exact rooted_case rooted _ W K rfl
  · apply bridgeless V G connected cubic
    intro a b adj bridge
    exact hasBridge ⟨a, b, adj, bridge⟩

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1.H1 := by
  intro bridgeless rooted V G finite dec nonempty cubic
  classical
  obtain ⟨start⟩ := nonempty
  let C := G.connectedComponentMk start
  let H := G.induce C.supp
  have hconn : H.Connected := C.connected_toSimpleGraph
  have hregular (v : C.supp) : H.degree v = 3 := (degree_component G C v).trans (cubic v.val)
  obtain ⟨k, v, c, hk, hc, hl⟩ := connected_case bridgeless rooted H hconn hregular
  let lift : H →g G := ⟨Subtype.val, fun h => h⟩
  exact ⟨k, v.val, c.map lift, hk, hc.map Subtype.val_injective, by simpa using hl⟩

end OMA.R_Erdos64_erdos_64_R1_H1_R1
