import OMAStatements.S_mo_239951
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open OMA.S_mo_239951
open scoped BigOperators

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_239951.main) := by
  intro h
  let G : SimpleGraph (Fin 8) := {
    Adj i j := i.val % 2 ≠ j.val % 2
    symm := ⟨fun _ _ h => h.symm⟩
    loopless := ⟨fun _ h => h rfl⟩ }
  let : DecidableRel G.Adj := fun i j =>
    inferInstanceAs (Decidable (i.val % 2 ≠ j.val % 2))
  have hdegree : ∀ i, G.degree i = 4 := by decide +revert
  have hconnected : G.Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨0, fun w => ?_⟩
    by_cases hw : w.val % 2 = 0
    · have h01 : G.Adj 0 1 := by decide +revert
      have h1w : G.Adj 1 w := by
        change 1 ≠ w.val % 2
        rw [hw]
        decide
      exact h01.reachable.trans h1w.reachable
    · exact (show G.Adj 0 w from fun e => hw e.symm).reachable
  have hweights (i : Fin 8) :
      (∑ k ∈ G.neighborFinset i, (1 : ℝ) / ((max (G.degree i) (G.degree k) : ℕ) + 1)) =
        (4 : ℝ) / 5 := by
    simp only [hdegree, max_self, Nat.cast_ofNat, Finset.sum_const]
    change G.degree i • ((1 : ℝ) / (4 + 1)) = 4 / 5
    rw [hdegree]
    norm_num
  have htransition (i j : Fin 8) : transition G i j =
      if i = j then (1 : ℝ) / 5 else if i.val % 2 ≠ j.val % 2 then 1 / 5 else 0 := by
    unfold transition
    rw [hweights, hdegree, hdegree, max_self]
    change (if i = j then 1 - (4 : ℝ) / 5
      else if i.val % 2 ≠ j.val % 2 then 1 / (4 + 1) else 0) = _
    split_ifs <;> norm_num
  let v : Fin 8 → ℝ := fun i => if i.val % 2 = 0 then 1 else -1
  have hv : v ≠ 0 := by
    intro e
    have hv0 := congrArg (fun u : Fin 8 → ℝ => u 0) e
    norm_num [v] at hv0
  have heigen : (transition G).mulVec v = (-(3 / 5) : ℝ) • v := by
    funext i
    simp only [Matrix.mulVec, dotProduct, htransition, Pi.smul_apply, smul_eq_mul]
    have huniv : (Finset.univ : Finset (Fin 8)) = {0, 1, 2, 3, 4, 5, 6, 7} := by decide
    rw [huniv]
    fin_cases i <;> norm_num [Finset.sum_insert, Fin.ext_iff, v]
  have hf := h (Fin 8) G hconnected (-(3 / 5)) v hv heigen
  norm_num at hf