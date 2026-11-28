import OMAStatements.S_mo_295663
import Mathlib

-- Problem: mo-295663, integer vectors C, R are the column and row sums of an integer matrix
-- if and only if they have the same total.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- The total of the column sums and the total of the row sums are both the sum of all entries.
-- Conversely, if the totals agree (and n > 0), put R in column 0 and C in row 0 and subtract
-- the common total S at position (0, 0): M_ij = [j = 0] R_i + [i = 0] C_j - [i = j = 0] S.

theorem OMA.solution : type_of% @OMA.S_mo_295663.main := by
  intro n C R
  unfold OMA.S_mo_295663.Representable
  constructor
  · rintro ⟨M, hC, hR⟩
    calc ∑ j, C j = ∑ j, ∑ i, M i j := Finset.sum_congr rfl (fun j _ => (hC j).symm)
      _ = ∑ i, ∑ j, M i j := Finset.sum_comm
      _ = ∑ i, R i := Finset.sum_congr rfl (fun i _ => hR i)
  · intro h
    cases n with
    | zero => exact ⟨0, fun j => j.elim0, fun i => i.elim0⟩
    | succ k =>
      refine ⟨Matrix.of fun i j => (if j = 0 then R i else 0) + (if i = 0 then C j else 0) -
        (if i = 0 ∧ j = 0 then ∑ l, C l else 0), ?_, ?_⟩
      · intro j
        by_cases hj : j = 0
        · subst hj
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', h]
        · simp [hj, Finset.sum_ite_eq']
      · intro i
        by_cases hi : i = 0
        · subst hi
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq']
        · simp [hi, Finset.sum_ite_eq']
