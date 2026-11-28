import OMAStatements.S_oeis_a161869

-- A161869: the OEIS entry says the conjectured binomial transform is incorrect
-- (calculating more terms of the sequence shows the above conjecture is incorrect).
-- The formalized statement is the original conjecture; it fails at n = 24:
--   a 24 = 258566402,  transform 24 = 258566401.
-- The computation below evaluates the well-founded recursion `columnTail` step by step.

namespace OMA.S_oeis_a161869

lemma ct_zero (k : ℕ) : columnTail k 0 = 1 := by
  rw [columnTail.eq_def]
  simp

lemma ct_6_0 : columnTail 6 0 = 1 := ct_zero 6

lemma ct_6_1 : columnTail 6 1 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_5_0 : columnTail 5 0 = 1 := ct_zero 5

lemma ct_5_1 : columnTail 5 1 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_5_2 : columnTail 5 2 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_5_3 : columnTail 5 3 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_5_4 : columnTail 5 4 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_5_5 : columnTail 5 5 = 1 := by
  rw [columnTail.eq_def]
  norm_num
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.choose 1 i * columnTail 6 i) 2]
  norm_num [Finset.sum_range_succ, Nat.choose, ct_6_0, ct_6_1]

lemma ct_4_0 : columnTail 4 0 = 1 := ct_zero 4

lemma ct_4_1 : columnTail 4 1 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_4_2 : columnTail 4 2 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_4_3 : columnTail 4 3 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_4_4 : columnTail 4 4 = 1 := by
  rw [columnTail.eq_def]
  norm_num
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.choose 1 i * columnTail 5 i) 2]
  norm_num [Finset.sum_range_succ, Nat.choose, ct_5_0, ct_5_1]

lemma ct_3_0 : columnTail 3 0 = 1 := ct_zero 3

lemma ct_3_1 : columnTail 3 1 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_3_2 : columnTail 3 2 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_3_3 : columnTail 3 3 = 1 := by
  rw [columnTail.eq_def]
  norm_num
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.choose 1 i * columnTail 4 i) 2]
  norm_num [Finset.sum_range_succ, Nat.choose, ct_4_0, ct_4_1]

lemma ct_3_4 : columnTail 3 4 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_3_5 : columnTail 3 5 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_3_6 : columnTail 3 6 = 1 := by
  rw [columnTail.eq_def]
  norm_num
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.choose 2 i * columnTail 4 i) 3]
  norm_num [Finset.sum_range_succ, Nat.choose, ct_4_0, ct_4_1, ct_4_2]

lemma ct_3_7 : columnTail 3 7 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_3_8 : columnTail 3 8 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_3_9 : columnTail 3 9 = 1 := by
  rw [columnTail.eq_def]
  norm_num
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.choose 3 i * columnTail 4 i) 4]
  norm_num [Finset.sum_range_succ, Nat.choose, ct_4_0, ct_4_1, ct_4_2, ct_4_3]

lemma ct_3_10 : columnTail 3 10 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_3_11 : columnTail 3 11 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_3_12 : columnTail 3 12 = 2 := by
  rw [columnTail.eq_def]
  norm_num
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.choose 4 i * columnTail 4 i) 5]
  norm_num [Finset.sum_range_succ, Nat.choose, ct_4_0, ct_4_1, ct_4_2, ct_4_3, ct_4_4]

lemma ct_2_0 : columnTail 2 0 = 1 := ct_zero 2

lemma ct_2_1 : columnTail 2 1 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_2_2 : columnTail 2 2 = 1 := by
  rw [columnTail.eq_def]
  norm_num
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.choose 1 i * columnTail 3 i) 2]
  norm_num [Finset.sum_range_succ, Nat.choose, ct_3_0, ct_3_1]

lemma ct_2_3 : columnTail 2 3 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_2_4 : columnTail 2 4 = 1 := by
  rw [columnTail.eq_def]
  norm_num
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.choose 2 i * columnTail 3 i) 3]
  norm_num [Finset.sum_range_succ, Nat.choose, ct_3_0, ct_3_1, ct_3_2]

lemma ct_2_5 : columnTail 2 5 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_2_6 : columnTail 2 6 = 2 := by
  rw [columnTail.eq_def]
  norm_num
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.choose 3 i * columnTail 3 i) 4]
  norm_num [Finset.sum_range_succ, Nat.choose, ct_3_0, ct_3_1, ct_3_2, ct_3_3]

lemma ct_2_7 : columnTail 2 7 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_2_8 : columnTail 2 8 = 5 := by
  rw [columnTail.eq_def]
  norm_num
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.choose 4 i * columnTail 3 i) 5]
  norm_num [Finset.sum_range_succ, Nat.choose, ct_3_0, ct_3_1, ct_3_2, ct_3_3, ct_3_4]

lemma ct_2_9 : columnTail 2 9 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_2_10 : columnTail 2 10 = 11 := by
  rw [columnTail.eq_def]
  norm_num
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.choose 5 i * columnTail 3 i) 6]
  norm_num [Finset.sum_range_succ, Nat.choose, ct_3_0, ct_3_1, ct_3_2, ct_3_3, ct_3_4, ct_3_5]

lemma ct_2_11 : columnTail 2 11 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_2_12 : columnTail 2 12 = 22 := by
  rw [columnTail.eq_def]
  norm_num
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.choose 6 i * columnTail 3 i) 7]
  norm_num [Finset.sum_range_succ, Nat.choose, ct_3_0, ct_3_1, ct_3_2, ct_3_3, ct_3_4, ct_3_5, ct_3_6]

lemma ct_2_13 : columnTail 2 13 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_2_14 : columnTail 2 14 = 43 := by
  rw [columnTail.eq_def]
  norm_num
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.choose 7 i * columnTail 3 i) 8]
  norm_num [Finset.sum_range_succ, Nat.choose, ct_3_0, ct_3_1, ct_3_2, ct_3_3, ct_3_4, ct_3_5, ct_3_6, ct_3_7]

lemma ct_2_15 : columnTail 2 15 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_2_16 : columnTail 2 16 = 85 := by
  rw [columnTail.eq_def]
  norm_num
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.choose 8 i * columnTail 3 i) 9]
  norm_num [Finset.sum_range_succ, Nat.choose, ct_3_0, ct_3_1, ct_3_2, ct_3_3, ct_3_4, ct_3_5, ct_3_6, ct_3_7, ct_3_8]

lemma ct_2_17 : columnTail 2 17 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_2_18 : columnTail 2 18 = 170 := by
  rw [columnTail.eq_def]
  norm_num
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.choose 9 i * columnTail 3 i) 10]
  norm_num [Finset.sum_range_succ, Nat.choose, ct_3_0, ct_3_1, ct_3_2, ct_3_3, ct_3_4, ct_3_5, ct_3_6, ct_3_7, ct_3_8, ct_3_9]

lemma ct_2_19 : columnTail 2 19 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_2_20 : columnTail 2 20 = 341 := by
  rw [columnTail.eq_def]
  norm_num
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.choose 10 i * columnTail 3 i) 11]
  norm_num [Finset.sum_range_succ, Nat.choose, ct_3_0, ct_3_1, ct_3_2, ct_3_3, ct_3_4, ct_3_5, ct_3_6, ct_3_7, ct_3_8, ct_3_9, ct_3_10]

lemma ct_2_21 : columnTail 2 21 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_2_22 : columnTail 2 22 = 683 := by
  rw [columnTail.eq_def]
  norm_num
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.choose 11 i * columnTail 3 i) 12]
  norm_num [Finset.sum_range_succ, Nat.choose, ct_3_0, ct_3_1, ct_3_2, ct_3_3, ct_3_4, ct_3_5, ct_3_6, ct_3_7, ct_3_8, ct_3_9, ct_3_10, ct_3_11]

lemma ct_2_23 : columnTail 2 23 = 0 := by
  rw [columnTail.eq_def]
  norm_num

lemma ct_2_24 : columnTail 2 24 = 1367 := by
  rw [columnTail.eq_def]
  norm_num
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.choose 12 i * columnTail 3 i) 13]
  norm_num [Finset.sum_range_succ, Nat.choose, ct_3_0, ct_3_1, ct_3_2, ct_3_3, ct_3_4, ct_3_5, ct_3_6, ct_3_7, ct_3_8, ct_3_9, ct_3_10, ct_3_11, ct_3_12]

lemma a24 : a 24 = 258566402 := by
  rw [a]
  norm_num [Finset.sum_range_succ, Nat.choose, ct_2_0, ct_2_1, ct_2_2, ct_2_3, ct_2_4, ct_2_5, ct_2_6, ct_2_7, ct_2_8, ct_2_9, ct_2_10, ct_2_11, ct_2_12, ct_2_13, ct_2_14, ct_2_15, ct_2_16, ct_2_17, ct_2_18, ct_2_19, ct_2_20, ct_2_21, ct_2_22, ct_2_23, ct_2_24]

lemma tr24 : transform 24 = 258566401 := by
  simp only [transform, b]
  norm_num [Finset.sum_range_succ, Nat.choose]


end OMA.S_oeis_a161869

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a161869.main) := by
  intro h
  have h24 := h 24
  rw [OMA.S_oeis_a161869.a24, OMA.S_oeis_a161869.tr24] at h24
  norm_num at h24
