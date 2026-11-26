import FormalConjectures.Wikipedia.SnakeInTheBox

/-! The first nine-dimensional 191-edge witness of Orland, Fagan et al.,
“A census of new snake-in-the-box records”, arXiv:2607.15270, from
Math-AI-Caltech/Snake-in-the-Box, record_snakes.csv.zip. Credit: @Deldor14. -/
open SimpleGraph SnakeInBox symmDiff

namespace OMA.Snake
private def check {V : Type*} [DecidableEq V] (adj : V → V → Bool) : List V → Bool
  | u::v::xs => adj u v && xs.all (fun z => z != u && !(adj u z)) && check adj (v::xs)
  | _ => true

private lemma realize {V : Type*} [DecidableEq V] (G : SimpleGraph V) (adj : V → V → Bool)
    (ha : ∀ u v, adj u v = true ↔ G.Adj u v) (xs : List V) (u : V)
    (hc : check adj (u::xs) = true) :
    ∃ v, ∃ p : G.Walk u v, p.support = u::xs ∧ p.IsPath ∧ p.toSubgraph.IsInduced := by
  induction xs generalizing u with
  | nil =>
    refine ⟨u,.nil,rfl,Walk.IsPath.nil,?_⟩
    intro x hx y hy hxy
    simp only [Walk.mem_verts_toSubgraph,Walk.support_nil,List.mem_singleton] at hx hy
    exact (hxy.ne (hx.trans hy.symm)).elim
  | cons v xs ih =>
    simp only [check,Bool.and_eq_true] at hc
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

private def adj (a b : Finset (Fin 9)) := decide ((a ∆ b).card = 1)
private theorem adj_iff (a b : Finset (Fin 9)) : adj a b = true ↔ (Hypercube 9).Adj a b := by
  simp only [adj,decide_eq_true_eq,Hypercube,fromRel_adj]
  rw [symmDiff_comm b a]
  constructor
  · intro h
    refine ⟨?_,Or.inl h⟩
    rintro rfl
    simp at h
  · exact fun h => h.2.elim id id

private def tail : List (Finset (Fin 9)) := [
  {0},
  {0,4},
  {0,1,4},
  {1,4},
  {1,3,4},
  {1,2,3,4},
  {2,3,4},
  {0,2,3,4},
  {0,2,3},
  {0,1,2,3},
  {0,1,2},
  {1,2},
  {1,2,6},
  {1,2,3,6},
  {2,3,6},
  {3,6},
  {3,6,7},
  {6,7},
  {0,6,7},
  {0,4,6,7},
  {0,1,4,6,7},
  {1,4,6,7},
  {1,2,4,6,7},
  {1,2,3,4,6,7},
  {2,3,4,6,7},
  {0,2,3,4,6,7},
  {0,2,3,6,7},
  {0,1,2,3,6,7},
  {0,1,2,6,7},
  {0,1,2,6,7,8},
  {0,1,2,4,6,7,8},
  {0,2,4,6,7,8},
  {2,4,6,7,8},
  {2,6,7,8},
  {2,3,6,7,8},
  {1,2,3,6,7,8},
  {1,3,6,7,8},
  {1,3,4,6,7,8},
  {0,1,3,4,6,7,8},
  {0,3,4,6,7,8},
  {0,3,6,7,8},
  {0,3,7,8},
  {0,2,3,7,8},
  {0,2,3,4,7,8},
  {2,3,4,7,8},
  {1,2,3,4,7,8},
  {1,2,4,7,8},
  {1,4,7,8},
  {4,7,8},
  {4,7},
  {3,4,7},
  {0,3,4,7},
  {0,1,3,4,7},
  {0,1,2,3,4,7},
  {0,1,2,4,7},
  {0,2,4,7},
  {0,2,7},
  {2,7},
  {2,3,7},
  {1,2,3,7},
  {1,3,7},
  {1,7},
  {0,1,7},
  {0,1,7,8},
  {0,1,8},
  {1,8},
  {1,3,8},
  {1,2,3,8},
  {2,3,8},
  {2,8},
  {2,4,8},
  {0,2,4,8},
  {0,1,2,4,8},
  {0,1,2,3,4,8},
  {0,1,3,4,8},
  {0,3,4,8},
  {3,4,8},
  {3,4,6,8},
  {2,3,4,6,8},
  {1,2,3,4,6,8},
  {1,2,4,6,8},
  {1,4,6,8},
  {0,1,4,6,8},
  {0,4,6,8},
  {0,6,8},
  {0,2,6,8},
  {0,2,3,6,8},
  {0,1,2,3,6,8},
  {0,1,3,6,8},
  {0,1,3,6},
  {0,1,3,4,6},
  {0,1,2,3,4,6},
  {0,1,2,4,6},
  {0,2,4,6},
  {2,4,6},
  {4,6},
  {4,5,6},
  {1,4,5,6},
  {1,2,4,5,6},
  {1,2,3,4,5,6},
  {2,3,4,5,6},
  {0,2,3,4,5,6},
  {0,2,3,5,6},
  {0,3,5,6},
  {0,3,5,6,8},
  {0,3,4,5,6,8},
  {0,1,3,4,5,6,8},
  {1,3,4,5,6,8},
  {1,3,5,6,8},
  {1,2,3,5,6,8},
  {2,3,5,6,8},
  {2,5,6,8},
  {2,4,5,6,8},
  {0,2,4,5,6,8},
  {0,1,2,4,5,6,8},
  {0,1,2,5,6,8},
  {0,1,2,5,8},
  {0,1,2,3,5,8},
  {0,2,3,5,8},
  {0,2,3,4,5,8},
  {2,3,4,5,8},
  {1,2,3,4,5,8},
  {1,2,4,5,8},
  {1,4,5,8},
  {0,1,4,5,8},
  {0,4,5,8},
  {0,5,8},
  {5,8},
  {3,5,8},
  {3,5,7,8},
  {3,5,7},
  {5,7},
  {0,5,7},
  {0,4,5,7},
  {0,1,4,5,7},
  {1,4,5,7},
  {1,3,4,5,7},
  {1,2,3,4,5,7},
  {2,3,4,5,7},
  {0,2,3,4,5,7},
  {0,2,3,5,7},
  {0,1,2,3,5,7},
  {0,1,2,5,7},
  {1,2,5,7},
  {1,2,5,7,8},
  {2,5,7,8},
  {2,4,5,7,8},
  {0,2,4,5,7,8},
  {0,1,2,4,5,7,8},
  {0,1,2,3,4,5,7,8},
  {0,1,3,4,5,7,8},
  {0,1,3,5,7,8},
  {0,1,3,5,6,7,8},
  {0,1,2,3,5,6,7,8},
  {0,2,3,5,6,7,8},
  {0,2,5,6,7,8},
  {0,5,6,7,8},
  {0,4,5,6,7,8},
  {0,1,4,5,6,7,8},
  {1,4,5,6,7,8},
  {1,2,4,5,6,7,8},
  {1,2,3,4,5,6,7,8},
  {2,3,4,5,6,7,8},
  {3,4,5,6,7,8},
  {3,4,5,6,7},
  {0,3,4,5,6,7},
  {0,1,3,4,5,6,7},
  {0,1,2,3,4,5,6,7},
  {0,1,2,4,5,6,7},
  {0,2,4,5,6,7},
  {2,4,5,6,7},
  {2,5,6,7},
  {2,3,5,6,7},
  {1,2,3,5,6,7},
  {1,3,5,6,7},
  {1,5,6,7},
  {0,1,5,6,7},
  {0,1,5,6},
  {0,1,5},
  {1,5},
  {1,3,5},
  {1,2,3,5},
  {2,3,5},
  {2,5},
  {0,2,5},
  {0,2,4,5},
  {0,1,2,4,5},
  {0,1,2,3,4,5},
  {0,1,3,4,5},
  {0,3,4,5},
  {3,4,5}]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem certificate : check adj (∅::tail) = true := by decide +kernel

end OMA.Snake
open OMA.Snake in
set_option maxRecDepth 20000 in
theorem OMA.solution : type_of% @SnakeInBox.snake_dim_nine_lower_bound := by
  obtain ⟨v,p,hs,hp,hi⟩ := realize (Hypercube 9) adj adj_iff tail ∅ certificate
  have hlen := congrArg List.length hs
  rw [Walk.length_support, List.length_cons] at hlen
  have hl : p.length = 191 := by simpa only [show tail.length = 191 from rfl] using Nat.succ.inj hlen
  apply Nat.le_trans (show 190 ≤ 191 by decide)
  apply le_csSup (s := {k | ∃ S, IsSnakeInGraphOfLength (Hypercube 9) S k})
  · refine ⟨Fintype.card (Finset (Fin 9)),?_⟩
    rintro k ⟨S,_,a,b,q,hq,_,rfl⟩
    exact hq.length_lt.le
  · exact ⟨p.toSubgraph,hi,∅,v,p,hp,rfl,hl⟩
