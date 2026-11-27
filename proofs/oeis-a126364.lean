import OMAStatements.S_oeis_a126364
import Mathlib

namespace A126364Aux
open OMA.S_oeis_a126364

lemma row_0 : row 0 = ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  funext i; fin_cases i <;> rfl
lemma row_1 : row 1 = ![2, 3, 3, 3, 3, 3, 3, 3, 3, 2] := by
  have h : row 1 = adjacency.mulVec (row 0) := rfl
  rw [h, row_0]
  decide
lemma row_2 : row 2 = ![5, 8, 9, 9, 9, 9, 9, 9, 8, 5] := by
  have h : row 2 = adjacency.mulVec (row 1) := rfl
  rw [h, row_1]
  decide
lemma row_3 : row 3 = ![13, 22, 26, 27, 27, 27, 27, 26, 22, 13] := by
  have h : row 3 = adjacency.mulVec (row 2) := rfl
  rw [h, row_2]
  decide
lemma row_4 : row 4 = ![35, 61, 75, 80, 81, 81, 80, 75, 61, 35] := by
  have h : row 4 = adjacency.mulVec (row 3) := rfl
  rw [h, row_3]
  decide
lemma row_5 : row 5 = ![96, 171, 216, 236, 242, 242, 236, 216, 171, 96] := by
  have h : row 5 = adjacency.mulVec (row 4) := rfl
  rw [h, row_4]
  decide
lemma row_6 : row 6 = ![267, 483, 623, 694, 720, 720, 694, 623, 483, 267] := by
  have h : row 6 = adjacency.mulVec (row 5) := rfl
  rw [h, row_5]
  decide
lemma row_7 : row 7 = ![750, 1373, 1800, 2037, 2134, 2134, 2037, 1800, 1373, 750] := by
  have h : row 7 = adjacency.mulVec (row 6) := rfl
  rw [h, row_6]
  decide
lemma row_8 : row 8 = ![2123, 3923, 5210, 5971, 6305, 6305, 5971, 5210, 3923, 2123] := by
  have h : row 8 = adjacency.mulVec (row 7) := rfl
  rw [h, row_7]
  decide
lemma row_9 : row 9 = ![6046, 11256, 15104, 17486, 18581, 18581, 17486, 15104, 11256, 6046] := by
  have h : row 9 = adjacency.mulVec (row 8) := rfl
  rw [h, row_8]
  decide
lemma row_10 : row 10 = ![17302, 32406, 43846, 51171, 54648, 54648, 51171, 43846, 32406, 17302] := by
  have h : row 10 = adjacency.mulVec (row 9) := rfl
  rw [h, row_9]
  decide
lemma row_11 : row 11 = ![49708, 93554, 127423, 149665, 160467, 160467, 149665, 127423, 93554, 49708] := by
  have h : row 11 = adjacency.mulVec (row 10) := rfl
  rw [h, row_10]
  decide

lemma T_neg : ∀ (n : ℕ) (k : ℤ), k < 0 → T n k = 0
  | 0, k, hk => by rw [T]; split_ifs <;> omega
  | 1, k, hk => by rw [T]; split_ifs <;> omega
  | n + 2, k, hk => by
    rw [T, T_neg (n + 1) (k - 2) (by omega), T_neg (n + 1) (k - 1) (by omega), T_neg (n + 1) k hk]

lemma T_big : ∀ (n : ℕ) (k : ℤ), 2 * (n : ℤ) < k → T n k = 0
  | 0, k, hk => by rw [T]; split_ifs <;> omega
  | 1, k, hk => by rw [T]; split_ifs <;> omega
  | n + 2, k, hk => by
    rw [T, T_big (n + 1) (k - 2) (by push_cast at hk ⊢; omega), T_big (n + 1) (k - 1) (by push_cast at hk ⊢; omega), T_big (n + 1) k (by push_cast at hk ⊢; omega)]

lemma t_1_0 : T 1 0 = 1 := by decide
lemma t_1_1 : T 1 1 = 2 := by decide
lemma t_1_2 : T 1 2 = 1 := by decide
lemma t_2_0 : T 2 0 = 1 := by
  have h : T 2 0 = T 1 (0 - 2) + T 1 (0 - 1) + T 1 0 := rfl
  rw [h]; norm_num [T_neg 1 (-2) (by norm_num), T_neg 1 (-1) (by norm_num), t_1_0]
lemma t_2_1 : T 2 1 = 3 := by
  have h : T 2 1 = T 1 (1 - 2) + T 1 (1 - 1) + T 1 1 := rfl
  rw [h]; norm_num [T_neg 1 (-1) (by norm_num), t_1_0, t_1_1]
lemma t_2_2 : T 2 2 = 4 := by
  have h : T 2 2 = T 1 (2 - 2) + T 1 (2 - 1) + T 1 2 := rfl
  rw [h]; norm_num [t_1_0, t_1_1, t_1_2]
lemma t_2_3 : T 2 3 = 3 := by
  have h : T 2 3 = T 1 (3 - 2) + T 1 (3 - 1) + T 1 3 := rfl
  rw [h]; norm_num [t_1_1, t_1_2, T_big 1 3 (by norm_num)]
lemma t_2_4 : T 2 4 = 1 := by
  have h : T 2 4 = T 1 (4 - 2) + T 1 (4 - 1) + T 1 4 := rfl
  rw [h]; norm_num [t_1_2, T_big 1 3 (by norm_num), T_big 1 4 (by norm_num)]
lemma t_3_0 : T 3 0 = 1 := by
  have h : T 3 0 = T 2 (0 - 2) + T 2 (0 - 1) + T 2 0 := rfl
  rw [h]; norm_num [T_neg 2 (-2) (by norm_num), T_neg 2 (-1) (by norm_num), t_2_0]
lemma t_3_1 : T 3 1 = 4 := by
  have h : T 3 1 = T 2 (1 - 2) + T 2 (1 - 1) + T 2 1 := rfl
  rw [h]; norm_num [T_neg 2 (-1) (by norm_num), t_2_0, t_2_1]
lemma t_3_2 : T 3 2 = 8 := by
  have h : T 3 2 = T 2 (2 - 2) + T 2 (2 - 1) + T 2 2 := rfl
  rw [h]; norm_num [t_2_0, t_2_1, t_2_2]
lemma t_3_3 : T 3 3 = 10 := by
  have h : T 3 3 = T 2 (3 - 2) + T 2 (3 - 1) + T 2 3 := rfl
  rw [h]; norm_num [t_2_1, t_2_2, t_2_3]
lemma t_3_4 : T 3 4 = 8 := by
  have h : T 3 4 = T 2 (4 - 2) + T 2 (4 - 1) + T 2 4 := rfl
  rw [h]; norm_num [t_2_2, t_2_3, t_2_4]
lemma t_3_5 : T 3 5 = 4 := by
  have h : T 3 5 = T 2 (5 - 2) + T 2 (5 - 1) + T 2 5 := rfl
  rw [h]; norm_num [t_2_3, t_2_4, T_big 2 5 (by norm_num)]
lemma t_3_6 : T 3 6 = 1 := by
  have h : T 3 6 = T 2 (6 - 2) + T 2 (6 - 1) + T 2 6 := rfl
  rw [h]; norm_num [t_2_4, T_big 2 5 (by norm_num), T_big 2 6 (by norm_num)]
lemma t_4_0 : T 4 0 = 1 := by
  have h : T 4 0 = T 3 (0 - 2) + T 3 (0 - 1) + T 3 0 := rfl
  rw [h]; norm_num [T_neg 3 (-2) (by norm_num), T_neg 3 (-1) (by norm_num), t_3_0]
lemma t_4_1 : T 4 1 = 5 := by
  have h : T 4 1 = T 3 (1 - 2) + T 3 (1 - 1) + T 3 1 := rfl
  rw [h]; norm_num [T_neg 3 (-1) (by norm_num), t_3_0, t_3_1]
lemma t_4_2 : T 4 2 = 13 := by
  have h : T 4 2 = T 3 (2 - 2) + T 3 (2 - 1) + T 3 2 := rfl
  rw [h]; norm_num [t_3_0, t_3_1, t_3_2]
lemma t_4_3 : T 4 3 = 22 := by
  have h : T 4 3 = T 3 (3 - 2) + T 3 (3 - 1) + T 3 3 := rfl
  rw [h]; norm_num [t_3_1, t_3_2, t_3_3]
lemma t_4_4 : T 4 4 = 26 := by
  have h : T 4 4 = T 3 (4 - 2) + T 3 (4 - 1) + T 3 4 := rfl
  rw [h]; norm_num [t_3_2, t_3_3, t_3_4]
lemma t_4_5 : T 4 5 = 22 := by
  have h : T 4 5 = T 3 (5 - 2) + T 3 (5 - 1) + T 3 5 := rfl
  rw [h]; norm_num [t_3_3, t_3_4, t_3_5]
lemma t_4_6 : T 4 6 = 13 := by
  have h : T 4 6 = T 3 (6 - 2) + T 3 (6 - 1) + T 3 6 := rfl
  rw [h]; norm_num [t_3_4, t_3_5, t_3_6]
lemma t_4_7 : T 4 7 = 5 := by
  have h : T 4 7 = T 3 (7 - 2) + T 3 (7 - 1) + T 3 7 := rfl
  rw [h]; norm_num [t_3_5, t_3_6, T_big 3 7 (by norm_num)]
lemma t_4_8 : T 4 8 = 1 := by
  have h : T 4 8 = T 3 (8 - 2) + T 3 (8 - 1) + T 3 8 := rfl
  rw [h]; norm_num [t_3_6, T_big 3 7 (by norm_num), T_big 3 8 (by norm_num)]
lemma t_5_0 : T 5 0 = 1 := by
  have h : T 5 0 = T 4 (0 - 2) + T 4 (0 - 1) + T 4 0 := rfl
  rw [h]; norm_num [T_neg 4 (-2) (by norm_num), T_neg 4 (-1) (by norm_num), t_4_0]
lemma t_5_1 : T 5 1 = 6 := by
  have h : T 5 1 = T 4 (1 - 2) + T 4 (1 - 1) + T 4 1 := rfl
  rw [h]; norm_num [T_neg 4 (-1) (by norm_num), t_4_0, t_4_1]
lemma t_5_2 : T 5 2 = 19 := by
  have h : T 5 2 = T 4 (2 - 2) + T 4 (2 - 1) + T 4 2 := rfl
  rw [h]; norm_num [t_4_0, t_4_1, t_4_2]
lemma t_5_3 : T 5 3 = 40 := by
  have h : T 5 3 = T 4 (3 - 2) + T 4 (3 - 1) + T 4 3 := rfl
  rw [h]; norm_num [t_4_1, t_4_2, t_4_3]
lemma t_5_4 : T 5 4 = 61 := by
  have h : T 5 4 = T 4 (4 - 2) + T 4 (4 - 1) + T 4 4 := rfl
  rw [h]; norm_num [t_4_2, t_4_3, t_4_4]
lemma t_5_5 : T 5 5 = 70 := by
  have h : T 5 5 = T 4 (5 - 2) + T 4 (5 - 1) + T 4 5 := rfl
  rw [h]; norm_num [t_4_3, t_4_4, t_4_5]
lemma t_5_6 : T 5 6 = 61 := by
  have h : T 5 6 = T 4 (6 - 2) + T 4 (6 - 1) + T 4 6 := rfl
  rw [h]; norm_num [t_4_4, t_4_5, t_4_6]
lemma t_5_7 : T 5 7 = 40 := by
  have h : T 5 7 = T 4 (7 - 2) + T 4 (7 - 1) + T 4 7 := rfl
  rw [h]; norm_num [t_4_5, t_4_6, t_4_7]
lemma t_5_8 : T 5 8 = 19 := by
  have h : T 5 8 = T 4 (8 - 2) + T 4 (8 - 1) + T 4 8 := rfl
  rw [h]; norm_num [t_4_6, t_4_7, t_4_8]
lemma t_5_9 : T 5 9 = 6 := by
  have h : T 5 9 = T 4 (9 - 2) + T 4 (9 - 1) + T 4 9 := rfl
  rw [h]; norm_num [t_4_7, t_4_8, T_big 4 9 (by norm_num)]
lemma t_5_10 : T 5 10 = 1 := by
  have h : T 5 10 = T 4 (10 - 2) + T 4 (10 - 1) + T 4 10 := rfl
  rw [h]; norm_num [t_4_8, T_big 4 9 (by norm_num), T_big 4 10 (by norm_num)]
lemma t_6_1 : T 6 1 = 7 := by
  have h : T 6 1 = T 5 (1 - 2) + T 5 (1 - 1) + T 5 1 := rfl
  rw [h]; norm_num [T_neg 5 (-1) (by norm_num), t_5_0, t_5_1]
lemma t_6_2 : T 6 2 = 26 := by
  have h : T 6 2 = T 5 (2 - 2) + T 5 (2 - 1) + T 5 2 := rfl
  rw [h]; norm_num [t_5_0, t_5_1, t_5_2]
lemma t_6_3 : T 6 3 = 65 := by
  have h : T 6 3 = T 5 (3 - 2) + T 5 (3 - 1) + T 5 3 := rfl
  rw [h]; norm_num [t_5_1, t_5_2, t_5_3]
lemma t_6_4 : T 6 4 = 120 := by
  have h : T 6 4 = T 5 (4 - 2) + T 5 (4 - 1) + T 5 4 := rfl
  rw [h]; norm_num [t_5_2, t_5_3, t_5_4]
lemma t_6_5 : T 6 5 = 171 := by
  have h : T 6 5 = T 5 (5 - 2) + T 5 (5 - 1) + T 5 5 := rfl
  rw [h]; norm_num [t_5_3, t_5_4, t_5_5]
lemma t_6_6 : T 6 6 = 192 := by
  have h : T 6 6 = T 5 (6 - 2) + T 5 (6 - 1) + T 5 6 := rfl
  rw [h]; norm_num [t_5_4, t_5_5, t_5_6]
lemma t_6_7 : T 6 7 = 171 := by
  have h : T 6 7 = T 5 (7 - 2) + T 5 (7 - 1) + T 5 7 := rfl
  rw [h]; norm_num [t_5_5, t_5_6, t_5_7]
lemma t_6_8 : T 6 8 = 120 := by
  have h : T 6 8 = T 5 (8 - 2) + T 5 (8 - 1) + T 5 8 := rfl
  rw [h]; norm_num [t_5_6, t_5_7, t_5_8]
lemma t_6_9 : T 6 9 = 65 := by
  have h : T 6 9 = T 5 (9 - 2) + T 5 (9 - 1) + T 5 9 := rfl
  rw [h]; norm_num [t_5_7, t_5_8, t_5_9]
lemma t_6_10 : T 6 10 = 26 := by
  have h : T 6 10 = T 5 (10 - 2) + T 5 (10 - 1) + T 5 10 := rfl
  rw [h]; norm_num [t_5_8, t_5_9, t_5_10]
lemma t_6_11 : T 6 11 = 7 := by
  have h : T 6 11 = T 5 (11 - 2) + T 5 (11 - 1) + T 5 11 := rfl
  rw [h]; norm_num [t_5_9, t_5_10, T_big 5 11 (by norm_num)]
lemma t_7_3 : T 7 3 = 98 := by
  have h : T 7 3 = T 6 (3 - 2) + T 6 (3 - 1) + T 6 3 := rfl
  rw [h]; norm_num [t_6_1, t_6_2, t_6_3]
lemma t_7_4 : T 7 4 = 211 := by
  have h : T 7 4 = T 6 (4 - 2) + T 6 (4 - 1) + T 6 4 := rfl
  rw [h]; norm_num [t_6_2, t_6_3, t_6_4]
lemma t_7_5 : T 7 5 = 356 := by
  have h : T 7 5 = T 6 (5 - 2) + T 6 (5 - 1) + T 6 5 := rfl
  rw [h]; norm_num [t_6_3, t_6_4, t_6_5]
lemma t_7_6 : T 7 6 = 483 := by
  have h : T 7 6 = T 6 (6 - 2) + T 6 (6 - 1) + T 6 6 := rfl
  rw [h]; norm_num [t_6_4, t_6_5, t_6_6]
lemma t_7_7 : T 7 7 = 534 := by
  have h : T 7 7 = T 6 (7 - 2) + T 6 (7 - 1) + T 6 7 := rfl
  rw [h]; norm_num [t_6_5, t_6_6, t_6_7]
lemma t_7_8 : T 7 8 = 483 := by
  have h : T 7 8 = T 6 (8 - 2) + T 6 (8 - 1) + T 6 8 := rfl
  rw [h]; norm_num [t_6_6, t_6_7, t_6_8]
lemma t_7_9 : T 7 9 = 356 := by
  have h : T 7 9 = T 6 (9 - 2) + T 6 (9 - 1) + T 6 9 := rfl
  rw [h]; norm_num [t_6_7, t_6_8, t_6_9]
lemma t_7_10 : T 7 10 = 211 := by
  have h : T 7 10 = T 6 (10 - 2) + T 6 (10 - 1) + T 6 10 := rfl
  rw [h]; norm_num [t_6_8, t_6_9, t_6_10]
lemma t_7_11 : T 7 11 = 98 := by
  have h : T 7 11 = T 6 (11 - 2) + T 6 (11 - 1) + T 6 11 := rfl
  rw [h]; norm_num [t_6_9, t_6_10, t_6_11]
lemma t_8_5 : T 8 5 = 665 := by
  have h : T 8 5 = T 7 (5 - 2) + T 7 (5 - 1) + T 7 5 := rfl
  rw [h]; norm_num [t_7_3, t_7_4, t_7_5]
lemma t_8_6 : T 8 6 = 1050 := by
  have h : T 8 6 = T 7 (6 - 2) + T 7 (6 - 1) + T 7 6 := rfl
  rw [h]; norm_num [t_7_4, t_7_5, t_7_6]
lemma t_8_7 : T 8 7 = 1373 := by
  have h : T 8 7 = T 7 (7 - 2) + T 7 (7 - 1) + T 7 7 := rfl
  rw [h]; norm_num [t_7_5, t_7_6, t_7_7]
lemma t_8_8 : T 8 8 = 1500 := by
  have h : T 8 8 = T 7 (8 - 2) + T 7 (8 - 1) + T 7 8 := rfl
  rw [h]; norm_num [t_7_6, t_7_7, t_7_8]
lemma t_8_9 : T 8 9 = 1373 := by
  have h : T 8 9 = T 7 (9 - 2) + T 7 (9 - 1) + T 7 9 := rfl
  rw [h]; norm_num [t_7_7, t_7_8, t_7_9]
lemma t_8_10 : T 8 10 = 1050 := by
  have h : T 8 10 = T 7 (10 - 2) + T 7 (10 - 1) + T 7 10 := rfl
  rw [h]; norm_num [t_7_8, t_7_9, t_7_10]
lemma t_8_11 : T 8 11 = 665 := by
  have h : T 8 11 = T 7 (11 - 2) + T 7 (11 - 1) + T 7 11 := rfl
  rw [h]; norm_num [t_7_9, t_7_10, t_7_11]
lemma t_9_7 : T 9 7 = 3088 := by
  have h : T 9 7 = T 8 (7 - 2) + T 8 (7 - 1) + T 8 7 := rfl
  rw [h]; norm_num [t_8_5, t_8_6, t_8_7]
lemma t_9_8 : T 9 8 = 3923 := by
  have h : T 9 8 = T 8 (8 - 2) + T 8 (8 - 1) + T 8 8 := rfl
  rw [h]; norm_num [t_8_6, t_8_7, t_8_8]
lemma t_9_9 : T 9 9 = 4246 := by
  have h : T 9 9 = T 8 (9 - 2) + T 8 (9 - 1) + T 8 9 := rfl
  rw [h]; norm_num [t_8_7, t_8_8, t_8_9]
lemma t_9_10 : T 9 10 = 3923 := by
  have h : T 9 10 = T 8 (10 - 2) + T 8 (10 - 1) + T 8 10 := rfl
  rw [h]; norm_num [t_8_8, t_8_9, t_8_10]
lemma t_9_11 : T 9 11 = 3088 := by
  have h : T 9 11 = T 8 (11 - 2) + T 8 (11 - 1) + T 8 11 := rfl
  rw [h]; norm_num [t_8_9, t_8_10, t_8_11]
lemma t_10_9 : T 10 9 = 11257 := by
  have h : T 10 9 = T 9 (9 - 2) + T 9 (9 - 1) + T 9 9 := rfl
  rw [h]; norm_num [t_9_7, t_9_8, t_9_9]
lemma t_10_10 : T 10 10 = 12092 := by
  have h : T 10 10 = T 9 (10 - 2) + T 9 (10 - 1) + T 9 10 := rfl
  rw [h]; norm_num [t_9_8, t_9_9, t_9_10]
lemma t_10_11 : T 10 11 = 11257 := by
  have h : T 10 11 = T 9 (11 - 2) + T 9 (11 - 1) + T 9 11 := rfl
  rw [h]; norm_num [t_9_9, t_9_10, t_9_11]
lemma t_11_11 : T 11 11 = 34606 := by
  have h : T 11 11 = T 10 (11 - 2) + T 10 (11 - 1) + T 10 11 := rfl
  rw [h]; norm_num [t_10_9, t_10_10, t_10_11]

lemma a_12 : a 12 = 1161634 := by
  have h : a 12 = ∑ i : Fin 10, row 11 i := rfl
  rw [h, row_11]; decide
lemma a_11 : a 11 = 398746 := by
  have h : a 11 = ∑ i : Fin 10, row 10 i := rfl
  rw [h, row_10]; decide
lemma b_12 : a025565 12 = 34606 := by
  have h : a025565 12 = T 11 11 := rfl
  rw [h, t_11_11]
end A126364Aux

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a126364.main) := by
  intro h
  have h12 := h 12 (by norm_num)
  rw [A126364Aux.a_12, show 12 - 1 = 11 from rfl, A126364Aux.a_11, A126364Aux.b_12] at h12
  norm_num at h12
