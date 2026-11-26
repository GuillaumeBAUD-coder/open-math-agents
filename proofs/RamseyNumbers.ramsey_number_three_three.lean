import FormalConjectures.Wikipedia.RamseyNumbers
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

open RamseyNumbers SimpleGraph

namespace RamseyThree

-- The five-cycle and its complement both avoid triangles.
set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
lemma five_fails : ¬ IsGraphRamsey 5 3 3 := by
  intro h
  apply h (cycleGraph 5)
  unfold CliqueFree
  decide

lemma six_works : IsGraphRamsey 6 3 3 := by
  classical
  rintro G ⟨hG, hGc⟩
  -- In a triangle-free graph the neighbours of any vertex form a clique in the complement.
  have low_degree (H : SimpleGraph (Fin 6)) (h : H.CliqueFree 3) (hc : Hᶜ.CliqueFree 3) :
      H.degree 0 < 3 := by
    by_contra! hdeg
    apply hc.mono hdeg (H.neighborFinset 0)
    refine ⟨?_, rfl⟩
    rw [H.coe_neighborFinset, H.isClique_compl]
    exact H.isIndepSet_neighborSet_of_triangleFree h 0
  have hd := low_degree G hG hGc
  have hdc := low_degree Gᶜ hGc (by simpa using hG)
  rw [G.degree_compl, Fintype.card_fin] at hdc
  omega

end RamseyThree

theorem OMA.solution : type_of% @RamseyNumbers.ramsey_number_three_three := by
  rw [classicalRamsey_eq_sInf]
  apply IsLeast.csInf_eq
  refine ⟨RamseyThree.six_works, ?_⟩
  intro n hn
  by_contra! hlt
  have hmono : Monotone (fun m => IsGraphRamsey m 3 3) :=
    monotone_nat_of_le_succ fun m => IsGraphRamsey.succ m 3 3
  exact RamseyThree.five_fails (hmono (show n ≤ 5 by omega) hn)
