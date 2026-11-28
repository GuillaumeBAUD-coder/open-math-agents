import OMAReductions.R_opg_directed_cycle_of_length_twice_the_minimum_outdegree_R1
import Mathlib

namespace OMA.S_opg_directed_cycle_of_length_twice_the_minimum_outdegree

open Finset
open scoped BigOperators

private theorem insert_in_path {V : Type} (G : Digraph V)
    (ht : ∀ u v, u ≠ v → G.Adj u v ∨ G.Adj v u) (a : V) (l : List V)
    (hc : l.IsChain G.Adj) (hn : l.Nodup) (ha : a ∉ l) :
    ∃ l' : List V, l'.IsChain G.Adj ∧ l'.Nodup ∧
      (∀ v, v ∈ l' ↔ v = a ∨ v ∈ l) ∧
      ∀ v ∈ l'.head?, v = a ∨ v ∈ l.head? := by
  classical
  induction l with
  | nil => exact ⟨[a], by simp, by simp, by simp, by simp⟩
  | cons x l ih =>
    by_cases hax : G.Adj a x
    · refine ⟨a :: x :: l, hc.cons (by simpa using hax), List.nodup_cons.mpr ⟨ha, hn⟩,
        ?_, ?_⟩
      · simp
      · simp
    · have hne : a ≠ x := fun h => ha (List.mem_cons.mpr (Or.inl h))
      have hxa := (ht a x hne).resolve_left hax
      obtain ⟨l', hc', hn', hm', hh'⟩ :=
        ih hc.tail (List.nodup_cons.mp hn).2 (fun h => ha (List.mem_cons.mpr (Or.inr h)))
      have hx : x ∉ l' := by
        rw [hm']
        exact fun h => h.elim hne.symm (List.nodup_cons.mp hn).1
      refine ⟨x :: l', hc'.cons ?_, List.nodup_cons.mpr ⟨hx, hn'⟩, ?_, ?_⟩
      · intro v hv
        rcases hh' v hv with rfl | hv'
        · exact hxa
        · exact hc.rel_head? hv'
      · intro v
        simp only [List.mem_cons, hm']
        tauto
      · simp

private theorem list_path {V : Type} [Fintype V] (G : Digraph V)
    (ht : ∀ u v, u ≠ v → G.Adj u v ∨ G.Adj v u) :
    ∃ l : List V, l.IsChain G.Adj ∧ l.Nodup ∧ l.length = Fintype.card V := by
  classical
  have hpath (s : Finset V) :
      ∃ l : List V, l.IsChain G.Adj ∧ l.Nodup ∧ ∀ v, v ∈ l ↔ v ∈ s := by
    induction s using Finset.induction_on with
    | empty => exact ⟨[], by simp, by simp, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨l, hc, hn, hm⟩ := ih
      obtain ⟨l', hchain, hnodup, hmem, _⟩ :=
        insert_in_path G ht a l hc hn (fun h => ha ((hm a).mp h))
      exact ⟨l', hchain, hnodup, fun v => by simp [hmem, hm]⟩
  obtain ⟨l, hc, hn, hm⟩ := hpath Finset.univ
  have he : l.toFinset = Finset.univ := by ext v; simp [hm]
  exact ⟨l, hc, hn, by rw [← List.toFinset_card_of_nodup hn, he, Finset.card_univ]⟩

/-- Summing the two orientations of each ordered pair counts every arc twice. -/
private theorem order_bound {V : Type} [Fintype V] [Nonempty V]
    (G : Digraph V) [DecidableRel G.Adj] (k : ℕ) (hor : IsOriented G)
    (ht : ∀ u v, u ≠ v → G.Adj u v ∨ G.Adj v u) (hk : ∀ v, k ≤ outdegree G v) :
    2 * k + 1 ≤ Fintype.card V := by
  let : DecidableEq V := Classical.decEq V
  let b (u v : V) : ℕ := if G.Adj u v then 1 else 0
  let S := ∑ u : V, outdegree G u
  let n := Fintype.card V
  have hrow (u : V) : (∑ v : V, b u v) = outdegree G u := by
    change (∑ v : V, if G.Adj u v then (1 : ℕ) else 0) = outdegree G u
    rw [Finset.sum_boole, outdegree] <;> rfl
  have hp (u v : V) : b u v + b v u = if u ≠ v then 1 else 0 := by
    by_cases he : u = v
    · subst v
      have hh : ¬ G.Adj u u := fun h => hor u u h h
      simp [b, hh]
    · rcases ht u v he with h | h
      · simp [b, he, h, hor u v h]
      · simp [b, he, h, hor v u h]
  have hne (u : V) : (∑ v : V, if u ≠ v then (1 : ℕ) else 0) = n - 1 := by
    rw [Finset.sum_boole]
    have he : (univ : Finset V).filter (fun v => u ≠ v) = univ.erase u := by
      ext v
      simp [eq_comm]
    simp [he, n, Finset.card_erase_of_mem (mem_univ _)]
  have hA : (∑ u : V, ∑ v : V, b u v) = S := Finset.sum_congr rfl fun u _ => hrow u
  have hB : (∑ u : V, ∑ v : V, b v u) = S := Finset.sum_comm.trans hA
  have hS : 2 * S = n * (n - 1) := by
    calc
      _ = S + S := by omega
      _ = ∑ u : V, ∑ v : V, (b u v + b v u) := by
        simp only [Finset.sum_add_distrib, hA, hB]
      _ = _ := by simp only [hp, hne, sum_const, card_univ, Nat.nsmul_eq_mul, n]
  have hkS : n * k ≤ S := by
    simpa [S, n, nsmul_eq_mul] using
      (Finset.sum_le_sum (s := (univ : Finset V)) fun v _ => hk v)
  have hmul : n * (2 * k) ≤ n * (n - 1) := by
    calc
      _ = 2 * (n * k) := by ring
      _ ≤ 2 * S := Nat.mul_le_mul_left _ hkS
      _ = _ := hS
  have hn : 0 < n := Fintype.card_pos
  have hkn : 2 * k ≤ n - 1 := Nat.le_of_mul_le_mul_left hmul hn
  change 2 * k + 1 ≤ n
  omega

end OMA.S_opg_directed_cycle_of_length_twice_the_minimum_outdegree

open OMA.S_opg_directed_cycle_of_length_twice_the_minimum_outdegree in
theorem OMA.solution : OMA.R_opg_directed_cycle_of_length_twice_the_minimum_outdegree_R1.H1 := by
  intro V _ _ G _ k hor ht hk
  obtain ⟨l, hc, hn, hl⟩ := list_path G ht
  have hb : 2*k+1 ≤ l.length := hl ▸ order_bound G k hor ht hk
  let p (i : Fin (2*k+1)) := l.get (Fin.castLE hb i)
  refine ⟨p, ?_, ?_⟩
  · intro i j h
    have he : Fin.castLE hb i = Fin.castLE hb j := hn.injective_get h
    exact Fin.ext (congrArg (fun u : Fin l.length => u.val) he)
  · intro i
    have hi : i.val + 1 < l.length := by omega
    exact List.isChain_iff_getElem.mp hc i.val hi