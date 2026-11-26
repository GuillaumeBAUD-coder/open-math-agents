import FormalConjectures.Wikipedia.SumnerUniversalTournamentConjecture
import Mathlib.Combinatorics.SimpleGraph.Star

/-! The cyclic tournament on 2m+1 vertices has only m out-neighbors at
each vertex, so it excludes the out-star with m+1 leaves. Credit: @Deldor14. -/
open Digraph SimpleGraph SumnerUniversalTournamentConjecture

namespace OMA.Cyclic
private def offset {m : ℕ} (u v : Fin (2*m+1)) : ℕ :=
  if u.val < v.val then v.val - u.val else v.val + (2*m+1) - u.val

private lemma positive {m} (u v : Fin (2*m+1)) : 0 < offset u v := by
  have := u.isLt
  unfold offset
  split <;> omega

private lemma injective_offset {m} (u : Fin (2*m+1)) : Function.Injective (offset u) := by
  intro v w h
  have := u.isLt
  have := v.isLt
  have := w.isLt
  apply Fin.ext
  unfold offset at h
  split at h <;> split at h <;> omega

private lemma tournament (m : ℕ) :
    (Digraph.mk (fun u v : Fin (2*m+1) => offset u v ≤ m)).IsTournament := by
  constructor
  · intro u
    change ¬offset u u ≤ m
    simp [offset]
    omega
  · intro u v huv
    have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
    have := u.isLt
    have := v.isLt
    change offset u v ≤ m ↔ ¬offset v u ≤ m
    unfold offset
    split <;> split <;> omega
end OMA.Cyclic

open OMA.Cyclic in
theorem OMA.solution : type_of% @SumnerUniversalTournamentConjecture.sumner_conjecture.variants.sharp := by
  classical
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m+2 := ⟨n-2, by omega⟩
  let W := Option (Fin (m+1))
  let D : Digraph W := ⟨fun u v => u = none ∧ v ≠ none⟩
  let V := Fin (2*m+1)
  let G : Digraph V := ⟨fun u v => offset u v ≤ m⟩
  refine ⟨W,inferInstance,inferInstance,D,Classical.decRel _,by simp [W],?_,
    V,inferInstance,inferInstance,G,Classical.decRel _,by simp [V]; omega,tournament m,?_⟩
  · refine ⟨starGraph none, isTree_starGraph _, ?_, ?_⟩
    · rintro u v ⟨rfl,hv⟩
      exact starGraph_center_adj hv.symm
    · intro u v h
      rw [starGraph_adj] at h
      change (u = none ∧ v ≠ none) ↔ ¬ (v = none ∧ u ≠ none)
      grind
  · rintro ⟨f,hf⟩
    have hbound (i : Fin (m+1)) : offset (f none) (f (some i)) ≤ m :=
      f.map_adj' (show D.Adj none (some i) from ⟨rfl,by simp⟩)
    let g (i : Fin (m+1)) : Fin m := ⟨offset (f none) (f (some i)) - 1, by
      have := hbound i
      have := positive (f none) (f (some i))
      omega⟩
    have hg : Function.Injective g := by
      intro i j h
      have he := congrArg Fin.val h
      change offset (f none) (f (some i)) - 1 = offset (f none) (f (some j)) - 1 at he
      have hi := positive (f none) (f (some i))
      have hj := positive (f none) (f (some j))
      exact Option.some.inj (hf (injective_offset (f none) (by omega)))
    have hc := Fintype.card_le_of_injective g hg
    simpa using hc
