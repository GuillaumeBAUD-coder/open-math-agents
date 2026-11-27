import FormalConjectures.Wikipedia.SnakeInTheBox
import Mathlib

/-! Verify the path witnesses and the upper bounds through dimension five.
The transition lists are from https://minortriad.com/snake/ (Davies, Potter, Carlson).
The walk realization argument is adapted from @Deldor14, and the induced path lemmas
from @dk8827. -/
namespace OMA.R_SnakeInBox_snake_small_dimensions_R1
open SimpleGraph Finset symmDiff SnakeInBox

def H1 : Prop := LongestSnakeInTheBox 6 ≤ 26

def H2 : Prop := LongestSnakeInTheBox 7 ≤ 50

def H3 : Prop := LongestSnakeInTheBox 8 ≤ 98
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



private lemma upper {n k : ℕ} :
    let code (v : Finset (Fin n)) : ℕ := ∑ i ∈ v, 2^i.val
    let steps (x : ℕ) := (List.range n).map (fun j => x ^^^ (1 <<< j))
    let star (x : ℕ) := (steps x).foldl (fun m i => m ||| (1 <<< i)) (1 <<< x)
    let dfs : ℕ → ℕ → ℕ → Bool := Nat.rec (fun _ _ => true)
      (fun _ prev x ban => (steps x).any (fun y => !ban.testBit y && prev y (ban ||| star x)))
    (∀ x y : Finset (Fin n), code y ∈ steps (code x) ↔ (x ∆ y).card = 1) →
    (∀ x y : Finset (Fin n), (star (code x)).testBit (code y) = true ↔ x = y ∨ (x ∆ y).card = 1) →
    dfs (k+1) 0 0 = false → LongestSnakeInTheBox n ≤ k := by
  intro code steps star dfs moves blocks checked
  have translate (s x y : Finset (Fin n)) : (x ∆ s) ∆ (y ∆ s) = x ∆ y := by
    rw [← symmDiff_assoc, symmDiff_right_comm x s y, symmDiff_symmDiff_cancel_right]
  have complete (s : Finset (Fin n)) {k : ℕ} {a b : Finset (Fin n)} (p : (Hypercube n).Walk a b)
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
        have hn : ¬ (Hypercube n).Adj a x := by
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

  apply csSup_le'
  rintro l ⟨S, hi, a, b, p, hp, rfl, rfl⟩
  by_contra! h
  have hf := complete a p hp hi h 0 (by simp)
  simpa [code, checked] using hf
private lemma realize {V : Type*} [DecidableEq V] (G : SimpleGraph V) (adj : V → V → Bool)
    (ha : ∀ u v, adj u v = true ↔ G.Adj u v) (check : List V → V → Bool)
    (step : ∀ u v zs, check (v::zs) u =
      ((adj u v && zs.all (fun z => z != u && !(adj u z))) && check zs v))
    (xs : List V) (u : V)
    (hc : check xs u = true) :
    ∃ v, ∃ p : G.Walk u v, p.support = u::xs ∧ p.IsPath ∧ p.toSubgraph.IsInduced := by
  induction xs generalizing u with
  | nil =>
    refine ⟨u,.nil,rfl,Walk.IsPath.nil,?_⟩
    intro x hx y hy hxy
    simp only [Walk.mem_verts_toSubgraph,Walk.support_nil,List.mem_singleton] at hx hy
    exact (hxy.ne (hx.trans hy.symm)).elim
  | cons v xs ih =>
    simp only [step,Bool.and_eq_true] at hc
    obtain ⟨w,p,hs,hp,hi⟩ := ih v hc.2
    have huv := (ha u v).mp hc.1.1
    have none (z : V) (hz : z ∈ xs) : z ≠ u ∧ ¬G.Adj u z := by
      have H := List.all_eq_true.mp hc.1.2 z hz
      have H' : z ≠ u ∧ adj u z = false := by simpa using H
      exact ⟨H'.1,fun hadj => Bool.noConfusion (H'.2.symm.trans ((ha u z).mpr hadj))⟩
    refine ⟨w,.cons huv p,by simp [hs],hp.cons ?_,?_⟩
    · rw [hs,List.mem_cons]
      rintro (h|h)
      · exact huv.ne h
      · exact (none _ h).1 rfl
    · intro x hx y hy hxy
      rw [Walk.mem_verts_toSubgraph] at hx hy
      simp only [Walk.support_cons,List.mem_cons] at hx hy
      change (G.subgraphOfAdj huv ⊔ p.toSubgraph).Adj x y
      have unique (z : V) (hz : z ∈ p.support) (hadj : G.Adj u z) : z = v := by
        rw [hs,List.mem_cons] at hz
        exact hz.elim id fun h => ((none _ h).2 hadj).elim
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact (hxy.ne rfl).elim
      · rw [unique _ hy hxy]
        exact Or.inl (subgraphOfAdj_adj_self huv)
      · rw [unique _ hx hxy.symm]
        exact Or.inl (subgraphOfAdj_adj_self huv).symm
      · exact Or.inr (hi (p.mem_verts_toSubgraph.mpr hx) (p.mem_verts_toSubgraph.mpr hy) hxy)


private lemma lower (n : ℕ) (xs : List (Finset (Fin n))) :
    let adj (a b : Finset (Fin n)) := decide ((a ∆ b).card = 1)
    let check : List (Finset (Fin n)) → Finset (Fin n) → Bool := List.rec (fun _ => true)
      (fun v zs prev u => (adj u v && zs.all (fun z => z != u && !(adj u z))) && prev v)
    check xs ∅ = true → xs.length ≤ LongestSnakeInTheBox n := by
  intro adj check cert
  obtain ⟨v,p,hs,hp,hi⟩ := realize (Hypercube n) adj
    (fun x y => by simp [adj,cube_adj]) check (fun _ _ _ => rfl) xs ∅ cert
  have hlen := congrArg List.length hs
  rw [Walk.length_support, List.length_cons] at hlen
  apply le_csSup (s := {k | ∃ S, IsSnakeInGraphOfLength (Hypercube n) S k})
  · refine ⟨Fintype.card (Finset (Fin n)),?_⟩
    rintro k ⟨S,_,a,b,q,hq,_,rfl⟩
    exact hq.length_lt.le
  · exact ⟨p.toSubgraph,hi,∅,v,p,hp,rfl,Nat.succ.inj hlen⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private lemma low1 : 1 ≤ LongestSnakeInTheBox 1 :=
  lower 1 [{0}] (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 100000000 in
private lemma hi1 : LongestSnakeInTheBox 1 ≤ 1 :=
  upper (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private lemma low2 : 2 ≤ LongestSnakeInTheBox 2 :=
  lower 2 [{0}, {0,1}] (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 100000000 in
private lemma hi2 : LongestSnakeInTheBox 2 ≤ 2 :=
  upper (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private lemma low3 : 4 ≤ LongestSnakeInTheBox 3 :=
  lower 3 [{0}, {0,1}, {0,1,2}, {1,2}] (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 100000000 in
private lemma hi3 : LongestSnakeInTheBox 3 ≤ 4 :=
  upper (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private lemma low4 : 7 ≤ LongestSnakeInTheBox 4 :=
  lower 4 [{0}, {0,1}, {0,1,2}, {1,2}, {1,2,3}, {2,3}, {0,2,3}] (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 100000000 in
private lemma hi4 : LongestSnakeInTheBox 4 ≤ 7 :=
  upper (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private lemma low5 : 13 ≤ LongestSnakeInTheBox 5 :=
  lower 5 [{0}, {0,1}, {0,1,2}, {0,1,2,3}, {1,2,3}, {1,3}, {1,3,4}, {1,4}, {1,2,4}, {2,4}, {2,3,4}, {0,2,3,4}, {0,3,4}] (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 100000000 in
private lemma hi5 : LongestSnakeInTheBox 5 ≤ 13 :=
  upper (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private lemma low6 : 26 ≤ LongestSnakeInTheBox 6 :=
  lower 6 [{0}, {0,1}, {0,1,2}, {0,1,2,3}, {0,2,3}, {2,3}, {2,3,4}, {2,4}, {0,2,4}, {0,2,4,5}, {0,2,5}, {2,5}, {1,2,5}, {1,2,3,5}, {1,2,3,4,5}, {0,1,2,3,4,5}, {0,1,3,4,5}, {0,1,3,5}, {0,3,5}, {3,5}, {3,4,5}, {4,5}, {1,4,5}, {1,4}, {1,3,4}, {1,3}] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private lemma low7 : 50 ≤ LongestSnakeInTheBox 7 :=
  lower 7 [{0}, {0,1}, {0,1,2}, {1,2}, {1,2,3}, {2,3}, {0,2,3}, {0,2,3,4}, {0,3,4}, {0,1,3,4}, {1,3,4}, {1,4}, {1,4,5}, {0,1,4,5}, {0,4,5}, {0,2,4,5}, {0,2,5}, {2,5}, {2,5,6}, {2,6}, {0,2,6}, {0,2,4,6}, {0,4,6}, {4,6}, {3,4,6}, {3,6}, {0,3,6}, {0,1,3,6}, {0,1,2,3,6}, {0,1,2,3,4,6}, {1,2,3,4,6}, {1,2,4,6}, {1,2,4,5,6}, {0,1,2,4,5,6}, {0,1,2,5,6}, {0,1,5,6}, {1,5,6}, {1,3,5,6}, {1,3,4,5,6}, {0,1,3,4,5,6}, {0,3,4,5,6}, {0,2,3,4,5,6}, {2,3,4,5,6}, {2,3,4,5}, {3,4,5}, {3,5}, {0,3,5}, {0,1,3,5}, {0,1,2,3,5}, {0,1,2,3,4,5}] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private lemma low8 : 98 ≤ LongestSnakeInTheBox 8 :=
  lower 8 [{0}, {0,1}, {0,1,2}, {0,1,2,3}, {0,2,3}, {2,3}, {2,3,4}, {1,2,3,4}, {1,2,3,4,5}, {1,2,3,5}, {1,2,5}, {2,5}, {2,4,5}, {2,4,5,6}, {2,3,4,5,6}, {2,3,5,6}, {0,2,3,5,6}, {0,1,2,3,5,6}, {0,1,2,5,6}, {0,1,2,4,5,6}, {0,1,2,4,5}, {0,1,2,4,5,7}, {0,1,2,5,7}, {0,1,2,3,5,7}, {0,2,3,5,7}, {2,3,5,7}, {2,3,4,5,7}, {3,4,5,7}, {3,4,5}, {3,5}, {0,3,5}, {0,1,3,5}, {0,1,3,4,5}, {0,1,3,4,5,7}, {0,1,3,4,7}, {0,3,4,7}, {0,3,7}, {3,7}, {1,3,7}, {1,3,6,7}, {1,6,7}, {6,7}, {0,6,7}, {0,4,6,7}, {0,1,4,6,7}, {0,1,4,5,6,7}, {0,1,5,6,7}, {0,1,3,5,6,7}, {0,3,5,6,7}, {0,3,4,5,6,7}, {0,2,3,4,5,6,7}, {0,2,4,5,6,7}, {0,2,5,6,7}, {2,5,6,7}, {1,2,5,6,7}, {1,2,3,5,6,7}, {1,2,3,4,5,6,7}, {1,3,4,5,6,7}, {1,3,4,5,6}, {1,3,5,6}, {1,5,6}, {5,6}, {0,5,6}, {0,4,5,6}, {0,4,5}, {0,4,5,7}, {0,5,7}, {5,7}, {1,5,7}, {1,4,5,7}, {1,4,5}, {1,4}, {1,4,6}, {4,6}, {3,4,6}, {3,6}, {0,3,6}, {0,1,3,6}, {0,1,3,4,6}, {0,1,2,3,4,6}, {0,1,2,3,4,6,7}, {0,1,2,3,6,7}, {0,2,3,6,7}, {2,3,6,7}, {2,3,4,6,7}, {2,4,6,7}, {1,2,4,6,7}, {1,2,4,7}, {1,2,7}, {2,7}, {0,2,7}, {0,2,4,7}, {0,2,4}, {0,2,4,6}, {0,2,6}, {2,6}, {1,2,6}, {1,2,3,6}] (by decide +kernel)

theorem main : H1 → H2 → H3 → type_of% @SnakeInBox.snake_small_dimensions := by
  intro hi6 hi7 hi8
  change [LongestSnakeInTheBox 0, LongestSnakeInTheBox 1, LongestSnakeInTheBox 2, LongestSnakeInTheBox 3, LongestSnakeInTheBox 4, LongestSnakeInTheBox 5, LongestSnakeInTheBox 6, LongestSnakeInTheBox 7, LongestSnakeInTheBox 8] = _
  rw [snake_zero_zero, le_antisymm hi1 low1, le_antisymm hi2 low2, le_antisymm hi3 low3, le_antisymm hi4 low4, le_antisymm hi5 low5, le_antisymm hi6 low6, le_antisymm hi7 low7, le_antisymm hi8 low8]

end OMA.R_SnakeInBox_snake_small_dimensions_R1
