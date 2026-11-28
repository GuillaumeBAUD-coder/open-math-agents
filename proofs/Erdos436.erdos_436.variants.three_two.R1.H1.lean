import OMAReductions.R_Erdos436_erdos_436_variants_three_two_R1
import Mathlib

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 0 in
theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_three_two_R1.H1 := by
  intro w
  suffices ∃ n ∈ [1, 5, 6, 7, 8, 11, 12, 14, 20, 21, 25, 27, 63, 77],
      (n.primeFactorsList.map w).sum = 0 ∧ ((n + 1).primeFactorsList.map w).sum = 0 by
    obtain ⟨n, hn, h⟩ := this
    exact ⟨n, Finset.mem_Icc.2 (by simp at hn; omega), h⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, exists_eq_or_imp, exists_eq_left, Nat.reduceAdd,
    Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, true_and]
  generalize w 2 = a, w 3 = b, w 5 = c, w 7 = d, w 11 = e, w 13 = f
  revert a b c d e f
  decide
