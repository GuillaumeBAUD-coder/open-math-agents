import OMAReductions.R_SnakeInBox_coil_small_dimensions_R1
import Mathlib

-- Induced-path tail and endpoint arguments adapted from @dk8827.
namespace FiveCoil
open SimpleGraph Finset symmDiff SnakeInBox

variable {V : Type} {G : SimpleGraph V}

private theorem no_neighbors_of_not_mem {a b x : V} (p : G.Walk a b)
    (hx : x ∉ p.support) : p.toSubgraph.neighborSet x = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  exact hx (p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hy))

private theorem start_neighbors {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    p.toSubgraph.neighborSet a = if p.Nil then ∅ else {p.snd} := by
  cases p with
  | nil => simp [neighborSet_singletonSubgraph]
  | cons h p =>
    rw [Walk.cons_isPath_iff] at hp
    simp [Subgraph.neighborSet_sup, no_neighbors_of_not_mem p hp.2]

private theorem tail_induced {a b c : V} (h : G.Adj a b) (p : G.Walk b c)
    (hp : (Walk.cons h p).IsPath) (hi : (Walk.cons h p).toSubgraph.IsInduced) :
    p.toSubgraph.IsInduced := by
  have ha := ((Walk.cons_isPath_iff h p).mp hp).2
  intro x hx y hy hxy
  have hfull : (Walk.cons h p).toSubgraph.Adj x y :=
    hi ((Walk.cons h p).mem_verts_toSubgraph.mpr (by simp [p.mem_verts_toSubgraph.mp hx]))
      ((Walk.cons h p).mem_verts_toSubgraph.mpr (by simp [p.mem_verts_toSubgraph.mp hy])) hxy
  rw [Walk.toSubgraph, Subgraph.sup_adj] at hfull
  refine hfull.resolve_left ?_
  have hxa : x ≠ a := fun e => ha (e ▸ p.mem_verts_toSubgraph.mp hx)
  have hya : y ≠ a := fun e => ha (e ▸ p.mem_verts_toSubgraph.mp hy)
  simp [subgraphOfAdj_adj, Sym2.eq, hxa.symm, hya.symm]

private theorem cube_adj {n : ℕ} (a b : Finset (Fin n)) :
    (SnakeInBox.Hypercube n).Adj a b ↔ (a ∆ b).card = 1 := by
  rw [SnakeInBox.Hypercube, SimpleGraph.fromRel_adj, symmDiff_comm b a, or_self]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rintro rfl
  simp at h


abbrev Vertex := Finset (Fin 5)

def code (v : Vertex) : ℕ := ∑ i ∈ v, 2^i.val

def steps (x : ℕ) : List ℕ := [x ^^^ 1, x ^^^ 2, x ^^^ 4, x ^^^ 8, x ^^^ 16]

def star (x : ℕ) : ℕ :=
  (steps x).foldl (fun m i => m ||| (1 <<< i)) (1 <<< x)

def dfs : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | k+1, x, banned => (steps x).any fun y =>
      !banned.testBit y && dfs k y (banned ||| star x)

set_option maxHeartbeats 10000000 in
private theorem moves : ∀ x y : Vertex,
    code y ∈ steps (code x) ↔ (x ∆ y).card = 1 := by decide +kernel

set_option maxHeartbeats 10000000 in
private theorem blocks : ∀ x y : Vertex,
    (star (code x)).testBit (code y) = true ↔ x = y ∨ (x ∆ y).card = 1 := by decide +kernel

private lemma translate (s x y : Vertex) : (x ∆ s) ∆ (y ∆ s) = x ∆ y := by
  rw [← symmDiff_assoc, symmDiff_right_comm x s y, symmDiff_symmDiff_cancel_right]

private lemma complete (s : Vertex) {k : ℕ} {a b : Vertex} (p : (Hypercube 5).Walk a b)
    (hp : p.IsPath) (hi : p.toSubgraph.IsInduced) (hk : k ≤ p.length) (ban : ℕ)
    (hb : ∀ x ∈ p.support, x ≠ a → ban.testBit (code (x ∆ s)) = false) :
    dfs k (code (a ∆ s)) ban = true := by
  induction k generalizing a b ban with
  | zero => rfl
  | succ k ih =>
    cases p with
    | nil => simp at hk
    | @cons a b c h p =>
      obtain ⟨hpath, ha⟩ := (Walk.cons_isPath_iff h p).mp hp
      apply List.any_eq_true.mpr
      refine ⟨code (b ∆ s), (moves _ _).mpr ?_, ?_⟩
      · rw [translate]
        exact (cube_adj _ _).mp h
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨hb b (by simp) h.ne.symm, ih p hpath (tail_induced h p hp hi) (by simpa using hk) _ ?_⟩
      intro x hx hxb
      have hxa : x ≠ a := fun e => ha (e ▸ hx)
      have hn : ¬ (Hypercube 5).Adj a x := by
        intro hax
        have hf := hi (Walk.start_mem_verts_toSubgraph (Walk.cons h p))
          ((Walk.cons h p).mem_verts_toSubgraph.mpr (by simp [hx])) hax
        change x ∈ (Walk.cons h p).toSubgraph.neighborSet a at hf
        rw [start_neighbors _ hp] at hf
        exact hxb (by simpa using hf)
      rw [Nat.testBit_or, hb x (by simp [hx]) hxa, Bool.false_or]
      apply Bool.eq_false_iff.mpr
      intro hit
      have hh := (blocks _ _).mp hit
      rw [translate, symmDiff_left_inj] at hh
      exact hh.elim hxa.symm (fun edge => hn ((cube_adj _ _).mpr edge))

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 10000 in
private theorem checked : dfs 14 0 0 = false := by decide +kernel

private lemma bound {a b : Vertex} (p : (Hypercube 5).Walk a b)
    (hp : p.IsPath) (hi : p.toSubgraph.IsInduced) : p.length < 14 := by
  by_contra! h
  have hf := complete a p hp hi h 0 (by simp)
  simpa [code, checked] using hf

private lemma evenCycle {a : Vertex} (p : (Hypercube 5).Walk a a) : Even p.length := by
  have different : ∀ x y : Vertex, (x ∆ y).card = 1 →
      decide (Even x.card) ≠ decide (Even y.card) := by decide +kernel
  let c : (Hypercube 5).Coloring Bool :=
    Coloring.mk (fun x => decide (Even x.card)) (fun h => different _ _ ((cube_adj _ _).mp h))
  exact (c.even_length_iff_congr p).mpr Iff.rfl

private lemma cycleBound {u : Vertex} (p : (Hypercube 5).Walk u u)
    (hc : p.IsCycle) (hi : p.toSubgraph.IsInduced) : p.length ≤ 14 := by
  have he := evenCycle p
  cases p with
  | nil => simp
  | @cons a b c h q =>
    have hq : q.IsPath := by simpa using hc.isPath_tail
    have hlen := hc.three_le_length
    have hn : ¬ q.Nil := by
      intro hz
      have := Walk.length_eq_zero_iff.mpr hz
      simp_all
    let e := q.adj_penultimate hn
    have spec := q.concat_dropLast e
    have hnot : u ∉ q.dropLast.support := by
      have hnodup := hq.support_nodup
      rw [← spec, Walk.support_concat, List.nodup_append] at hnodup
      exact fun hx => hnodup.2.2 u hx u (by simp) rfl
    have hind : q.dropLast.toSubgraph.IsInduced := by
      intro x hx y hy hxy
      have hxa : x ≠ u := fun hh => hnot (hh ▸ q.dropLast.mem_verts_toSubgraph.mp hx)
      have hya : y ≠ u := fun hh => hnot (hh ▸ q.dropLast.mem_verts_toSubgraph.mp hy)
      have hsub : q.dropLast.toSubgraph ≤ (Walk.cons h q).toSubgraph := by
        change _ ≤ _ ⊔ q.toSubgraph
        apply le_trans _ le_sup_right
        conv_rhs => rw [← spec, Walk.concat_eq_append, Walk.toSubgraph_append]
        exact le_sup_left
      have hf := hi (hsub.1 hx) (hsub.1 hy) hxy
      rw [Walk.toSubgraph, Subgraph.sup_adj] at hf
      have hr : q.toSubgraph.Adj x y := hf.resolve_left (by
        simp [subgraphOfAdj_adj, Sym2.eq, hxa.symm, hya.symm])
      rw [← spec, Walk.concat_eq_append, Walk.toSubgraph_append, Subgraph.sup_adj] at hr
      exact hr.resolve_right (by simp [Walk.toSubgraph, subgraphOfAdj_adj, Sym2.eq, hxa, hya, hxa.symm, hya.symm])
    have short := bound q.dropLast hq.dropLast hind
    rw [Walk.length_dropLast] at short
    simp only [Walk.length_cons] at he ⊢
    obtain ⟨m, hm⟩ := he
    omega

end FiveCoil

theorem OMA.solution : OMA.R_SnakeInBox_coil_small_dimensions_R1.H1 := by
  apply csSup_le'
  rintro k ⟨S, hi, u, p, hc, rfl, rfl⟩
  exact FiveCoil.cycleBound p hc hi
