import OMAStatements.S_mo_263706
import Mathlib

/-
A 16-vertex witness in Hamiltonian cycle order, identified in the House of Graphs
connected cubic census (order 16, graph6 row 3278, one-based). The graph contains
two copies of K(3,3) with one edge removed. A cycle through 15 vertices would have
to traverse both blocks through their two ports. Balancing the two sides of each
block and checking the four vertices between the blocks rules this out.
-/

namespace Min16Positive

def nbrs : Fin 16 → List (Fin 16) := ![[1,3,15],
    [0,2,4],
    [1,3,15],
    [0,2,4],
    [1,3,5],
    [4,6,13],
    [5,7,14],
    [6,8,10],
    [7,9,11],
    [8,10,12],
    [7,9,11],
    [8,10,12],
    [9,11,13],
    [5,12,14],
    [6,13,15],
    [0,2,14]]

def G : SimpleGraph (Fin 16) where
  Adj x y := y ∈ nbrs x
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

theorem adj_of (x y : Fin 16) (h : y ∈ nbrs x) : G.Adj x y := h

theorem cubic (v : Fin 16) : (G.neighborSet v).ncard = 3 := by
  have h : G.neighborSet v = ↑(nbrs v).toFinset := by
    ext w
    change w ∈ nbrs v ↔ w ∈ (nbrs v).toFinset
    simp
  rw [h, Set.ncard_coe_finset]
  clear h
  revert v
  decide

def hamPath : G.Walk 0 15 :=
  .cons (adj_of 0 1 (by decide)) <|
  .cons (adj_of 1 2 (by decide)) <|
  .cons (adj_of 2 3 (by decide)) <|
  .cons (adj_of 3 4 (by decide)) <|
  .cons (adj_of 4 5 (by decide)) <|
  .cons (adj_of 5 6 (by decide)) <|
  .cons (adj_of 6 7 (by decide)) <|
  .cons (adj_of 7 8 (by decide)) <|
  .cons (adj_of 8 9 (by decide)) <|
  .cons (adj_of 9 10 (by decide)) <|
  .cons (adj_of 10 11 (by decide)) <|
  .cons (adj_of 11 12 (by decide)) <|
  .cons (adj_of 12 13 (by decide)) <|
  .cons (adj_of 13 14 (by decide)) <|
  .cons (adj_of 14 15 (by decide)) .nil

theorem hamPath_support : hamPath.support = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] := rfl

theorem hamPath_edges : hamPath.edges = [s(0,1),s(1,2),s(2,3),s(3,4),s(4,5),s(5,6),s(6,7),s(7,8),s(8,9),s(9,10),s(10,11),s(11,12),s(12,13),s(13,14),s(14,15)] := rfl

theorem hamiltonian : G.IsHamiltonian := by
  intro _
  refine ⟨15, SimpleGraph.Walk.cons (adj_of 15 0 (by decide)) hamPath, ?_⟩
  rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def, hamPath_support,
      hamPath_edges]
    refine ⟨by decide, ?_⟩
    simp only [List.mem_cons, Sym2.eq_iff, List.not_mem_nil, or_false, not_or]
    and_intros <;> decide
  · rw [SimpleGraph.Walk.support_cons, List.tail_cons, hamPath_support]
    decide

theorem notBip : ¬ G.IsBipartite := by
  rintro ⟨C⟩
  have e0 := Fin.val_ne_of_ne (C.valid (adj_of 0 1 (by decide)))
  have e1 := Fin.val_ne_of_ne (C.valid (adj_of 1 4 (by decide)))
  have e2 := Fin.val_ne_of_ne (C.valid (adj_of 4 5 (by decide)))
  have e3 := Fin.val_ne_of_ne (C.valid (adj_of 5 6 (by decide)))
  have e4 := Fin.val_ne_of_ne (C.valid (adj_of 6 14 (by decide)))
  have e5 := Fin.val_ne_of_ne (C.valid (adj_of 14 15 (by decide)))
  have e6 := Fin.val_ne_of_ne (C.valid (adj_of 15 0 (by decide)))
  have b0 := (C 0).isLt
  have b1 := (C 1).isLt
  have b2 := (C 4).isLt
  have b3 := (C 5).isLt
  have b4 := (C 6).isLt
  have b5 := (C 14).isLt
  have b6 := (C 15).isLt
  omega

end Min16Positive



namespace Min16Structural
open Min16Positive

private noncomputable def edge (H : G.Subgraph) (u w : Fin 16) : ℕ := by
  classical
  exact if H.Adj u w then 1 else 0

private theorem edge_comm (H : G.Subgraph) (a b : Fin 16) :
    edge H a b = edge H b a := by
  classical
  simp only [edge, H.adj_comm a b]

private theorem edge_le (H : G.Subgraph) (a b : Fin 16) : edge H a b ≤ 1 := by
  classical
  unfold edge
  split <;> omega

private theorem local_count (H : G.Subgraph) (u : Fin 16) :
    ((nbrs u).map (edge H u)).sum = (H.neighborSet u).ncard := by
  classical
  have nd : ∀ a, (nbrs a).Nodup := by decide
  have h : H.neighborSet u = ↑(((nbrs u).filter (fun x => decide (H.Adj u x))).toFinset) := by
    ext x
    simp only [SetLike.mem_coe, List.mem_toFinset, List.mem_filter,
      decide_eq_true_eq, SimpleGraph.Subgraph.mem_neighborSet]
    constructor
    · intro hx
      exact ⟨hx.adj_sub,hx⟩
    · exact And.right
  rw [h, Set.ncard_coe_finset, List.toFinset_card_of_nodup ((nd u).filter _)]
  generalize nbrs u = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : H.Adj u a <;> simp [edge, ha, ih, Nat.add_comm]

private theorem balance4 (H : G.Subgraph) (v : Fin 16)
    (equation : ∀ u, ((nbrs u).map (edge H u)).sum = (if u = v then 0 else 2)) :
    edge H 4 5 + ((if (1 : Fin 16) = v then 0 else 2) + (if (3 : Fin 16) = v then 0 else 2) + (if (15 : Fin 16) = v then 0 else 2)) =
      edge H 14 15 + ((if (0 : Fin 16) = v then 0 else 2) + (if (2 : Fin 16) = v then 0 else 2) + (if (4 : Fin 16) = v then 0 else 2)) := by
  have d0 : edge H 0 1 + edge H 0 3 + edge H 0 15 = (if (0 : Fin 16) = v then 0 else 2) := by
    have h := equation 0
    change edge H 0 1 + (edge H 0 3 + (edge H 0 15 + 0)) = _ at h
    simpa only [add_zero, add_assoc] using h
  have d2 : edge H 1 2 + edge H 2 3 + edge H 2 15 = (if (2 : Fin 16) = v then 0 else 2) := by
    have h := equation 2
    change edge H 2 1 + (edge H 2 3 + (edge H 2 15 + 0)) = _ at h
    simpa only [add_zero, add_assoc, edge_comm H (2 : Fin 16) 1] using h
  have d4 : edge H 1 4 + edge H 3 4 + edge H 4 5 = (if (4 : Fin 16) = v then 0 else 2) := by
    have h := equation 4
    change edge H 4 1 + (edge H 4 3 + (edge H 4 5 + 0)) = _ at h
    simpa only [add_zero, add_assoc, edge_comm H (4 : Fin 16) 1, edge_comm H (4 : Fin 16) 3] using h
  have d1 : edge H 0 1 + edge H 1 2 + edge H 1 4 = (if (1 : Fin 16) = v then 0 else 2) := by
    have h := equation 1
    change edge H 1 0 + (edge H 1 2 + (edge H 1 4 + 0)) = _ at h
    simpa only [add_zero, add_assoc, edge_comm H (1 : Fin 16) 0] using h
  have d3 : edge H 0 3 + edge H 2 3 + edge H 3 4 = (if (3 : Fin 16) = v then 0 else 2) := by
    have h := equation 3
    change edge H 3 0 + (edge H 3 2 + (edge H 3 4 + 0)) = _ at h
    simpa only [add_zero, add_assoc, edge_comm H (3 : Fin 16) 0, edge_comm H (3 : Fin 16) 2] using h
  have d15 : edge H 0 15 + edge H 2 15 + edge H 14 15 = (if (15 : Fin 16) = v then 0 else 2) := by
    have h := equation 15
    change edge H 15 0 + (edge H 15 2 + (edge H 15 14 + 0)) = _ at h
    simpa only [add_zero, add_assoc, edge_comm H (15 : Fin 16) 0, edge_comm H (15 : Fin 16) 2, edge_comm H (15 : Fin 16) 14] using h
  omega

private theorem balance12 (H : G.Subgraph) (v : Fin 16)
    (equation : ∀ u, ((nbrs u).map (edge H u)).sum = (if u = v then 0 else 2)) :
    edge H 12 13 + ((if (7 : Fin 16) = v then 0 else 2) + (if (9 : Fin 16) = v then 0 else 2) + (if (11 : Fin 16) = v then 0 else 2)) =
      edge H 6 7 + ((if (8 : Fin 16) = v then 0 else 2) + (if (10 : Fin 16) = v then 0 else 2) + (if (12 : Fin 16) = v then 0 else 2)) := by
  have d8 : edge H 7 8 + edge H 8 9 + edge H 8 11 = (if (8 : Fin 16) = v then 0 else 2) := by
    have h := equation 8
    change edge H 8 7 + (edge H 8 9 + (edge H 8 11 + 0)) = _ at h
    simpa only [add_zero, add_assoc, edge_comm H (8 : Fin 16) 7] using h
  have d10 : edge H 7 10 + edge H 9 10 + edge H 10 11 = (if (10 : Fin 16) = v then 0 else 2) := by
    have h := equation 10
    change edge H 10 7 + (edge H 10 9 + (edge H 10 11 + 0)) = _ at h
    simpa only [add_zero, add_assoc, edge_comm H (10 : Fin 16) 7, edge_comm H (10 : Fin 16) 9] using h
  have d12 : edge H 9 12 + edge H 11 12 + edge H 12 13 = (if (12 : Fin 16) = v then 0 else 2) := by
    have h := equation 12
    change edge H 12 9 + (edge H 12 11 + (edge H 12 13 + 0)) = _ at h
    simpa only [add_zero, add_assoc, edge_comm H (12 : Fin 16) 9, edge_comm H (12 : Fin 16) 11] using h
  have d7 : edge H 6 7 + edge H 7 8 + edge H 7 10 = (if (7 : Fin 16) = v then 0 else 2) := by
    have h := equation 7
    change edge H 7 6 + (edge H 7 8 + (edge H 7 10 + 0)) = _ at h
    simpa only [add_zero, add_assoc, edge_comm H (7 : Fin 16) 6] using h
  have d9 : edge H 8 9 + edge H 9 10 + edge H 9 12 = (if (9 : Fin 16) = v then 0 else 2) := by
    have h := equation 9
    change edge H 9 8 + (edge H 9 10 + (edge H 9 12 + 0)) = _ at h
    simpa only [add_zero, add_assoc, edge_comm H (9 : Fin 16) 8] using h
  have d11 : edge H 8 11 + edge H 10 11 + edge H 11 12 = (if (11 : Fin 16) = v then 0 else 2) := by
    have h := equation 11
    change edge H 11 8 + (edge H 11 10 + (edge H 11 12 + 0)) = _ at h
    simpa only [add_zero, add_assoc, edge_comm H (11 : Fin 16) 8, edge_comm H (11 : Fin 16) 10] using h
  omega

private theorem outside_edge (H : G.Subgraph) (hc : H.Connected)
    (S : Finset (Fin 16)) (u v : Fin 16) (hu : u ∈ H.verts) (hv : v ∈ H.verts)
    (hus : u ∈ S) (hvs : v ∉ S) :
    ∃ a b, a ∈ S ∧ b ∉ S ∧ H.Adj a b := by
  by_contra! h
  obtain ⟨q⟩ := hc.coe.preconnected ⟨u, hu⟩ ⟨v, hv⟩
  have propagate : ∀ (x y : H.verts) (_ : H.coe.Walk x y), x.val ∈ S → y.val ∈ S := by
    intro x y w
    induction w with
    | nil => exact id
    | cons e _ ih =>
      intro hx
      apply ih
      by_contra hy
      exact h _ _ hx hy e
  exact hvs (propagate _ _ q hus)

private def leftBlock : Finset (Fin 16) := {0,1,2,3,4,15}
private def rightBlock : Finset (Fin 16) := {7,8,9,10,11,12}

private theorem ports (H : G.Subgraph) (hc : H.Connected)
    (h1 : (0 : Fin 16) ∈ H.verts) (h2 : (7 : Fin 16) ∈ H.verts) :
    (edge H 4 5 = 1 ∨ edge H 14 15 = 1) ∧
    (edge H 6 7 = 1 ∨ edge H 12 13 = 1) := by
  classical
  have leftcut : ∀ a b : Fin 16, a ∈ leftBlock → b ∉ leftBlock → b ∈ nbrs a →
      (a = 4 ∧ b = 5) ∨ (a = 15 ∧ b = 14) := by decide
  have rightcut : ∀ a b : Fin 16, a ∈ rightBlock → b ∉ rightBlock → b ∈ nbrs a →
      (a = 7 ∧ b = 6) ∨ (a = 12 ∧ b = 13) := by decide
  constructor
  · obtain ⟨a,b,ha,hb,hab⟩ := outside_edge H hc leftBlock 0 7 h1 h2 (by decide) (by decide)
    rcases leftcut a b ha hb hab.adj_sub with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl (if_pos hab)
    · exact Or.inr (if_pos hab.symm)
  · obtain ⟨a,b,ha,hb,hab⟩ := outside_edge H hc rightBlock 7 0 h2 h1 (by decide) (by decide)
    rcases rightcut a b ha hb hab.adj_sub with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl (if_pos hab.symm)
    · exact Or.inr (if_pos hab)

private theorem impossible (H : G.Subgraph) (v : Fin 16) (hc : H.Connected)
    (hverts : ∀ x, x ∈ H.verts ↔ x ≠ v)
    (hdeg : ∀ x ∈ H.verts, (H.neighborSet x).ncard = 2) : False := by
  classical
  have missing : v ∉ H.verts := fun h => (hverts v).mp h rfl
  have eqns (x : Fin 16) : ((nbrs x).map (edge H x)).sum = (if x = v then 0 else 2) := by
    rw [local_count]
    split
    · next h =>
      subst x
      have em : H.neighborSet v = ∅ := by
        ext b
        constructor
        · exact fun h => (missing (H.edge_vert h)).elim
        · simp
      rw [em, Set.ncard_empty]
    · next h => exact hdeg x ((hverts x).mpr h)
  have ha := balance4 H v eqns
  have hb := balance12 H v eqns
  have h45 := edge_le H 4 5
  have h1415 := edge_le H 14 15
  have h67 := edge_le H 6 7
  have h1213 := edge_le H 12 13
  have zero_left (b : Fin 16) : edge H v b = 0 :=
    if_neg (fun h => missing (H.edge_vert h))
  have zero_right (a : Fin 16) : edge H a v = 0 := by rw [edge_comm]; exact zero_left a
  have hp (h0 : (0 : Fin 16) ≠ v) (h7 : (7 : Fin 16) ≠ v) :=
    ports H hc ((hverts _).mpr h0) ((hverts _).mpr h7)
  fin_cases v <;> norm_num [Fin.ext_iff] at ha hb
  · omega
  · omega
  · omega
  · omega
  · omega
  · obtain ⟨hl, hr⟩ := hp (by decide) (by decide)
    have hz : edge H 4 5 = 0 := zero_right 4
    rcases hl with h | h <;> omega
  · obtain ⟨hl, hr⟩ := hp (by decide) (by decide)
    have hz : edge H 6 7 = 0 := zero_left 7
    rcases hr with h | h <;> omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · obtain ⟨hl, hr⟩ := hp (by decide) (by decide)
    have hz : edge H 12 13 = 0 := zero_right 12
    rcases hr with h | h <;> omega
  · obtain ⟨hl, hr⟩ := hp (by decide) (by decide)
    have hz : edge H 14 15 = 0 := zero_left 15
    rcases hl with h | h <;> omega
  · omega

theorem no15 (u : Fin 16) (p : G.Walk u u) (hp : p.IsCycle) (hl : p.length = 15) : False := by
  have hconn : p.toSubgraph.Connected := p.toSubgraph_connected
  have h2 : ∀ w ∈ p.toSubgraph.verts, (p.toSubgraph.neighborSet w).ncard = 2 := fun w hw =>
    hp.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp hw)
  have hnd : p.support.tail.Nodup := hp.support_nodup
  have hlen : p.support.tail.length = 15 := by
    rw [List.length_tail, SimpleGraph.Walk.length_support, hl]
  have hcard : p.support.tail.toFinset.card = 15 := by
    rw [List.toFinset_card_of_nodup hnd, hlen]
  have hcompl : (p.support.tail.toFinset)ᶜ.card = 1 := by
    rw [Finset.card_compl, hcard, Fintype.card_fin]
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcompl
  apply impossible p.toSubgraph v hconn _ h2
  intro w
  rw [p.mem_verts_toSubgraph]
  have h1 : w ∈ (p.support.tail.toFinset)ᶜ ↔ w = v := by rw [hv]; simp
  simp only [Finset.mem_compl, List.mem_toFinset] at h1
  have h3 : w ∈ p.support ↔ w ∈ p.support.tail := by
    constructor
    · intro h
      rw [← p.cons_tail_support] at h
      rcases List.mem_cons.mp h with h | h
      · rw [h]; exact p.end_mem_tail_support hp.not_nil
      · exact h
    · exact List.mem_of_mem_tail
  rw [h3]
  tauto

end Min16Structural


theorem OMA.solution : type_of% @OMA.S_mo_263706.main := by
  exact ⟨16, Min16Positive.G, Min16Positive.cubic, Min16Positive.hamiltonian,
    fun u p hp hl => Min16Structural.no15 u p hp hl, Min16Positive.notBip⟩
