import FormalConjectures.Wikipedia.RamseyNumbers
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.FinCases

open RamseyNumbers SimpleGraph

namespace RamseyThreeFive

-- Once the least vertex of a clique is fixed, all remaining vertices are larger neighbours.
lemma exclude_by_least (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj] (k : ℕ)
    (cert : ∀ v : Fin 13, ∀ t ∈ (Finset.univ.filter (fun w => v < w ∧ G.Adj v w)).powersetCard k,
      ¬ G.IsClique t) : G.CliqueFree (k + 1) := by
  intro s hs
  have nonempty : s.Nonempty := Finset.card_pos.mp (by rw [hs.card_eq]; omega)
  let v := s.min' nonempty
  have hv : v ∈ s := s.min'_mem nonempty
  have ht := hs.erase_of_mem hv
  apply cert v (s.erase v) _ ht.isClique
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_, by simpa using ht.card_eq⟩
  intro w hw
  obtain ⟨hne, hw⟩ := Finset.mem_erase.mp hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    lt_of_le_of_ne (s.min'_le _ hw) hne.symm, hs.isClique hv hw hne.symm⟩

-- The circulant on 13 vertices joins residues with difference ±1 or ±5.
set_option maxRecDepth 18000 in
set_option maxHeartbeats 8000000 in
lemma thirteen_fails : ¬ IsGraphRamsey 13 3 5 := by
  let G : SimpleGraph (Fin 13) :=
    { Adj := fun u v => Nat.dist u.val v.val = 1 ∨ Nat.dist u.val v.val = 5 ∨
          Nat.dist u.val v.val = 8 ∨ Nat.dist u.val v.val = 12
      symm := ⟨by decide⟩
      loopless := ⟨by decide⟩ }
  let : DecidableRel G.Adj := fun u v => by
    dsimp [G]
    infer_instance
  intro h
  apply h G
  constructor
  · apply exclude_by_least G 2
    intro v
    fin_cases v <;> exact @of_decide_eq_true _ Finset.decidableDforallFinset rfl
  · apply exclude_by_least Gᶜ 4
    intro v
    fin_cases v <;> exact @of_decide_eq_true _ Finset.decidableDforallFinset rfl

-- With no triangle and no independent k-set, each vertex has fewer than k neighbours.
lemma degree_lt {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hc : Gᶜ.CliqueFree k) (v : Fin n) : G.degree v < k := by
  by_contra! h
  apply hc.mono h (G.neighborFinset v)
  refine ⟨?_, rfl⟩
  rw [G.coe_neighborFinset, G.isClique_compl]
  exact G.isIndepSet_neighborSet_of_triangleFree hG v

-- An independent k-set among non-neighbours extends to an independent (k+1)-set.
lemma nonneighbors_lt {n k m : ℕ} (hr : IsGraphRamsey m 3 k)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hc : Gᶜ.CliqueFree (k + 1)) (v : Fin n) : Gᶜ.degree v < m := by
  classical
  by_contra! h
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin m) (s := Gᶜ.neighborFinset v) (by simpa using h)
  have hv (i : Fin m) : Gᶜ.Adj v (f i) :=
    (Gᶜ.mem_neighborFinset v (f i)).mp (hf ⟨i, rfl⟩)
  let H := G.comap f
  let e : H ↪g G := SimpleGraph.Embedding.comap f G
  let ec : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv e
  apply hr H
  refine ⟨CliqueFree.comap e.isContained hG, ?_⟩
  intro t ht
  have hs : Gᶜ.IsNClique k (t.map f) := by
    refine ⟨?_, (Finset.card_map _).trans ht.card_eq⟩
    intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
    exact ec.map_adj_iff.mpr (ht.isClique hi hj (fun he => hxy (congrArg f he)))
  apply hc _ (hs.insert (a := v) ?_)
  intro w hw
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hw
  exact hv i

lemma six_works : IsGraphRamsey 6 3 3 := by
  classical
  rintro G ⟨hG, hc⟩
  have hd := degree_lt G hG hc 0
  have hdc := degree_lt Gᶜ hc (by simpa using hG : Gᶜᶜ.CliqueFree 3) 0
  rw [G.degree_compl, Fintype.card_fin] at hdc
  omega

lemma nine_works : IsGraphRamsey 9 3 4 := by
  classical
  rintro G ⟨hG, hc⟩
  have hdegree (v : Fin 9) : G.degree v = 3 := by
    have hd := degree_lt G hG hc v
    have hdc := nonneighbors_lt six_works G hG hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp [hdegree] at hsum
  omega

lemma fourteen_works : IsGraphRamsey 14 3 5 := by
  classical
  rintro G ⟨hG, hc⟩
  have hd := degree_lt G hG hc 0
  have hdc := nonneighbors_lt nine_works G hG hc 0
  rw [G.degree_compl, Fintype.card_fin] at hdc
  omega

end RamseyThreeFive

theorem OMA.solution : type_of% @RamseyNumbers.ramsey_number_three_five := by
  rw [classicalRamsey_eq_sInf]
  apply IsLeast.csInf_eq
  refine ⟨RamseyThreeFive.fourteen_works, ?_⟩
  intro n hn
  by_contra! hlt
  have hmono : Monotone (fun m => IsGraphRamsey m 3 5) :=
    monotone_nat_of_le_succ fun m => IsGraphRamsey.succ m 3 5
  exact RamseyThreeFive.thirteen_fails (hmono (show n ≤ 13 by omega) hn)
