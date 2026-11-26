import FormalConjectures.Wikipedia.RamseyNumbers
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.FinCases

/-!
# A reduction of R(3,6) = 18

The lower witness is the first graph from Brendan McKay’s Ramsey(3,6) collection.
The upper-bound split follows the regularity step of Cariolaro’s proof.
For an earlier full Lean formalisation, see zariuq/ai-agents, lean-projects/ramsey36.
The smaller Ramsey upper bounds reuse TheWaler’s previously checked proofs.
-/

open RamseyNumbers SimpleGraph

namespace OMA.R_RamseyNumbers_ramsey_number_three_six_R1

-- A clique search branches on its least vertex, retaining only larger neighbours.
lemma exclude_search {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (cert : (Nat.rec (motive := fun _ => List (Fin n) → Bool) (fun _ => true)
      (fun _ rec vs => vs.any fun v => rec (vs.filter fun w => decide (v < w ∧ G.Adj v w)))
      k (List.finRange n)) = false) : G.CliqueFree k := by
  let search := Nat.rec (motive := fun _ => List (Fin n) → Bool) (fun _ => true)
    (fun _ rec vs => vs.any fun v => rec (vs.filter fun w => decide (v < w ∧ G.Adj v w)))
  have found (j : ℕ) (vs : List (Fin n)) (s : Finset (Fin n)) (hs : G.IsNClique j s)
      (hsub : ∀ x ∈ s, x ∈ vs) : search j vs = true := by
    induction j generalizing vs s with
    | zero => rfl
    | succ j ih =>
      have hne : s.Nonempty := Finset.card_pos.mp (by rw [hs.card_eq]; omega)
      let v := s.min' hne
      have hv : v ∈ s := s.min'_mem hne
      change (vs.any _) = true
      apply List.any_eq_true.mpr
      refine ⟨v, hsub v hv, ih _ (s.erase v) (hs.erase_of_mem hv) ?_⟩
      intro w hw
      obtain ⟨hne, hw⟩ := Finset.mem_erase.mp hw
      exact List.mem_filter.mpr ⟨hsub w hw, decide_eq_true
        ⟨lt_of_le_of_ne (s.min'_le _ hw) hne.symm, hs.isClique hv hw hne.symm⟩⟩
  intro s hs
  have yes := found k (List.finRange n) s hs (by simp)
  change search k (List.finRange n) = false at cert
  simp_all

-- First 17-vertex graph in Brendan McKay's collection of Ramsey(3,6) graphs.
-- The table lists each vertex's larger neighbours.
set_option maxRecDepth 50000 in
set_option maxHeartbeats 16000000 in
lemma seventeen_fails : ¬ IsGraphRamsey 17 3 6 := by
  let edge (i j : ℕ) : Bool :=
    match i with
    | 0 => j == 9 || j == 14 || j == 15 || j == 16
    | 1 => j == 7 || j == 11 || j == 13 || j == 16
    | 2 => j == 8 || j == 10 || j == 12 || j == 15
    | 3 => j == 6 || j == 8 || j == 13 || j == 15 || j == 16
    | 4 => j == 5 || j == 7 || j == 12 || j == 14 || j == 16
    | 5 => j == 9 || j == 10 || j == 11 || j == 13
    | 6 => j == 10 || j == 11 || j == 12 || j == 14
    | 7 => j == 9 || j == 10 || j == 15
    | 8 => j == 9 || j == 11 || j == 14
    | 9 => j == 12
    | 10 => j == 16
    | 11 => j == 15
    | 12 => j == 13
    | 13 => j == 14
    | _ => false
  let G : SimpleGraph (Fin 17) :=
    { Adj := fun u v => u ≠ v ∧ edge (min u.val v.val) (max u.val v.val) = true
      symm := ⟨fun {u v} h => ⟨h.1.symm, by simpa only [min_comm v.val u.val, max_comm v.val u.val] using h.2⟩⟩
      loopless := ⟨fun u h => h.1 rfl⟩ }
  let : DecidableRel G.Adj := fun u v =>
    inferInstanceAs (Decidable (u ≠ v ∧ edge (min u.val v.val) (max u.val v.val) = true))
  intro h
  apply h G
  constructor
  · exact exclude_search G 3 (by rfl)
  · exact exclude_search Gᶜ 6 (by rfl)

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

-- This split mirrors the regularity step in Cariolaro’s upper-bound proof.
-- In the degree-four case only degrees four and five can occur.
def H1 : Prop :=
  ∀ (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj], G.CliqueFree 3 →
    (∀ v, G.degree v = 4 ∨ G.degree v = 5) → (∃ v, G.degree v = 4) → ¬ Gᶜ.CliqueFree 6

-- The remaining case is a 5-regular triangle-free graph.
def H2 : Prop :=
  ∀ (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj], G.CliqueFree 3 →
    (∀ v, G.degree v = 5) → ¬ Gᶜ.CliqueFree 6

theorem main : H1 → H2 → type_of% @RamseyNumbers.ramsey_number_three_six := by
  classical
  intro irregular regular
  have upper : IsGraphRamsey 18 3 6 := by
    rintro G ⟨ht, hc⟩
    have degrees (v : Fin 18) : G.degree v = 4 ∨ G.degree v = 5 := by
      have hd := degree_lt G ht hc v
      have hdc := nonneighbors_lt fourteen_works G ht hc v
      rw [G.degree_compl, Fintype.card_fin] at hdc
      omega
    by_cases h : ∃ v, G.degree v = 4
    · exact irregular G ht degrees h hc
    · exact regular G ht (fun v => (degrees v).resolve_left (fun hv => h ⟨v, hv⟩)) hc
  rw [classicalRamsey_eq_sInf]
  apply IsLeast.csInf_eq
  refine ⟨upper, ?_⟩
  intro n hn
  by_contra! hlt
  have hmono : Monotone (fun m => IsGraphRamsey m 3 6) :=
    monotone_nat_of_le_succ fun m => IsGraphRamsey.succ m 3 6
  exact seventeen_fails (hmono (show n ≤ 17 by omega) hn)

end OMA.R_RamseyNumbers_ramsey_number_three_six_R1
