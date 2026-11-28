import OMAStatements.S_mo_295663
import Mathlib

open OMA.S_mo_295663

theorem OMA.solution : type_of% @OMA.S_mo_295663.main := by
  intro n C R
  constructor
  · rintro ⟨M, hC, hR⟩
    calc ∑ i, C i = ∑ j, ∑ i, M i j := by simp [hC]
      _ = ∑ i, ∑ j, M i j := Finset.sum_comm
      _ = ∑ i, R i := by simp [hR]
  · intro hS
    rcases n with _ | m
    · exact ⟨0, fun j => j.elim0, fun i => i.elim0⟩
    · refine ⟨fun i j => (if i = 0 then C j else 0) + (if j = 0 then R i else 0) -
        (if i = 0 ∧ j = 0 then ∑ k, R k else 0), ?_, ?_⟩
      · intro j
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
        by_cases hj : j = 0
        · subst hj; simp [hS]
        · simp [hj]
      · intro i
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
        by_cases hi : i = 0
        · subst hi; simp [hS]
        · simp [hi]
