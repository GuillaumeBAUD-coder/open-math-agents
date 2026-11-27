import OMAStatements.S_mo_273966
import Mathlib

-- Problem: mo-273966, a k-subset S maximizing sum_{i in S} v_i + sum_{i not in S} w_i can be
-- chosen to consist of k indices with the largest differences v_i - w_i.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- The value of T equals sum_i w_i + sum_{i in T} (v_i - w_i). Take S maximizing the last sum
-- among the k-subsets. If some i in S and j outside S had v_j - w_j > v_i - w_i, swapping i for
-- j would give a k-subset with a strictly larger sum.

theorem OMA.solution : type_of% @OMA.S_mo_273966.main := by
  intro n k hk v w
  classical
  have hne : (Finset.powersetCard k (Finset.univ : Finset (Fin n))).Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    simpa using hk
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image _
    (fun T : Finset (Fin n) => ∑ i ∈ T, (v i - w i)) hne
  rw [Finset.mem_powersetCard] at hS
  have hval : ∀ T : Finset (Fin n), OMA.S_mo_273966.inheritanceValue v w T
      = (∑ i, w i) + ∑ i ∈ T, (v i - w i) := by
    intro T
    unfold OMA.S_mo_273966.inheritanceValue
    have h := Finset.sum_sdiff (Finset.subset_univ T) (f := w)
    rw [Finset.sum_sub_distrib]
    linarith
  refine ⟨S, hS.2, ?_, ?_⟩
  · intro i hi j hj
    by_contra hcon0
    have hcon : v i - w i < v j - w j := not_le.mp hcon0
    have hkpos : 0 < S.card := Finset.card_pos.mpr ⟨i, hi⟩
    have hjn : j ∉ S.erase i := fun h => hj (Finset.mem_of_mem_erase h)
    have hcard : (insert j (S.erase i)).card = k := by
      rw [Finset.card_insert_of_notMem hjn, Finset.card_erase_of_mem hi]
      omega
    have h1 : ∑ x ∈ insert j (S.erase i), (v x - w x) ≤ ∑ x ∈ S, (v x - w x) :=
      hmax (insert j (S.erase i))
        (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩)
    rw [Finset.sum_insert hjn] at h1
    have h2 := Finset.add_sum_erase S (fun i => v i - w i) hi
    linarith
  · intro T hT
    rw [hval T, hval S]
    have h : ∑ i ∈ T, (v i - w i) ≤ ∑ i ∈ S, (v i - w i) :=
      hmax T (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hT⟩)
    linarith
