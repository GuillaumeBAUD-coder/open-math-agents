import OMAStatements.S_oeis_a278772

/-!
Proof of Barker's conjectures for A278772 by a transfer count. N s m counts the continuations by m
rows of the scan from the state s (previous row, saturated row-mistake count, column comparison).
Every reachable state satisfies the linear recurrence of `N_rec`, checked by the kernel on tables of
N_0..N_K and propagated by induction through the one-row recursion of N. This gives Hardin's
empirical polynomial by strong induction, and the g.f. and recurrence follow from it.
-/

namespace OMA.S_oeis_a278772

open PowerSeries

/-- The continuations by m steps of the scan from a state. -/
def N (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) (m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 2 × Fin 2, if ok p0 p1 k e (List.ofFn y) = true then 1 else 0

theorem sum_cons (m : ℕ) (f : List (Fin 2 × Fin 2) → ℕ) :
    ∑ x : Fin (m + 1) → Fin 2 × Fin 2, f (List.ofFn x) =
      ∑ c : Fin 2 × Fin 2, ∑ y : Fin m → Fin 2 × Fin 2, f (c :: List.ofFn y) := by
  rw [← (Fin.consEquiv fun _ => Fin 2 × Fin 2).sum_comp]
  rw [Fintype.sum_prod_type (f := fun p : (Fin 2 × Fin 2) × (Fin m → Fin 2 × Fin 2) =>
    f (List.ofFn ((Fin.consEquiv fun _ => Fin 2 × Fin 2) p)))]
  simp [List.ofFn_succ]

theorem N_zero (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : N p0 p1 k e 0 = if ok p0 p1 k e [] = true then 1 else 0 := by
  simp [N]

/-- The condition on one step, without the rest of the scan. -/
def row (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) (c : Fin 2 × Fin 2) : Bool :=
  true

theorem N_succ (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) (m : ℕ) :
    N p0 p1 k e (m + 1) = ∑ c : Fin 2 × Fin 2,
      if row p0 p1 k e c = true then N c.1 c.2 (inc k (decide (code c < code (p0, p1)))) (cmp e c.1 c.2) m else 0 := by
  have h := sum_cons m (fun l => if ok p0 p1 k e l = true then 1 else 0)
  unfold N
  rw [h]
  apply Finset.sum_congr rfl
  intro c _
  have hr : row p0 p1 k e c = true := rfl
  rw [if_pos hr]
  apply Finset.sum_congr rfl
  intro y _
  rfl

/-- The index of a state in the tables. -/
def idx (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : ℕ := ((p0.val * 2 + p1.val) * 4 + k.val) * 3 + e.val

/-- The table of N_0. -/
def t0 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The table of N_1. -/
def t1 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : ℕ :=
  ([0, 0, 0, 1, 0, 4, 3, 4, 0, 0, 0, 0, 0, 0, 1, 2, 1, 3, 2, 3, 0, 0, 0, 0, 1, 0, 2, 1, 2, 2, 2, 2, 0, 0, 0, 0, 1, 0, 3, 2, 3, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The table of N_2. -/
def t2 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : ℕ :=
  ([2, 0, 6, 8, 6, 10, 6, 10, 0, 0, 0, 0, 3, 0, 10, 10, 10, 6, 3, 6, 0, 0, 0, 0, 5, 1, 12, 7, 12, 3, 3, 3, 0, 0, 0, 0, 7, 3, 12, 7, 12, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The table of N_3. -/
def t3 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : ℕ :=
  ([20, 4, 40, 33, 40, 20, 10, 20, 0, 0, 0, 0, 26, 10, 44, 31, 44, 10, 4, 10, 0, 0, 0, 0, 22, 20, 40, 25, 40, 4, 4, 4, 0, 0, 0, 0, 33, 31, 31, 16, 31, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The table of N_4. -/
def t4 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : ℕ :=
  ([117, 65, 155, 99, 155, 35, 15, 35, 0, 0, 0, 0, 130, 101, 135, 76, 135, 15, 5, 15, 0, 0, 0, 0, 96, 135, 101, 66, 101, 5, 5, 5, 0, 0, 0, 0, 116, 155, 65, 30, 65, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The table of N_5. -/
def t5 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : ℕ :=
  ([503, 456, 456, 245, 456, 56, 21, 56, 0, 0, 0, 0, 485, 546, 336, 161, 336, 21, 6, 21, 0, 0, 0, 0, 365, 580, 216, 146, 216, 6, 6, 6, 0, 0, 0, 0, 331, 546, 120, 50, 120, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The table of N_6. -/
def t6 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : ℕ :=
  ([1750, 2128, 1128, 532, 1128, 84, 28, 84, 0, 0, 0, 0, 1492, 2128, 728, 308, 728, 28, 7, 28, 0, 0, 0, 0, 1177, 1918, 413, 287, 413, 7, 7, 7, 0, 0, 0, 0, 813, 1554, 203, 77, 203, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The table of N_7. -/
def t7 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : ℕ :=
  ([5209, 7728, 2472, 1050, 2472, 120, 36, 120, 0, 0, 0, 0, 3991, 6728, 1428, 546, 1428, 36, 8, 36, 0, 0, 0, 0, 3291, 5328, 728, 518, 728, 8, 8, 8, 0, 0, 0, 0, 1786, 3823, 322, 112, 322, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The table of N_8. -/
def t8 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : ℕ :=
  ([13751, 23607, 4950, 1926, 4950, 165, 45, 165, 0, 0, 0, 0, 9592, 18351, 2598, 912, 2598, 45, 9, 45, 0, 0, 0, 0, 8200, 13051, 1206, 876, 1206, 9, 9, 9, 0, 0, 0, 0, 3600, 8451, 486, 156, 486, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The table of N_9. -/
def t9 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : ℕ :=
  ([33000, 63460, 9240, 3333, 9240, 220, 55, 220, 0, 0, 0, 0, 21175, 44803, 4455, 1452, 4455, 55, 10, 55, 0, 0, 0, 0, 18622, 29050, 1902, 1407, 1902, 10, 10, 10, 0, 0, 0, 0, 6777, 17205, 705, 210, 705, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The table of N_10. -/
def t10 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : ℕ :=
  ([73282, 154518, 16302, 5500, 16302, 286, 66, 286, 0, 0, 0, 0, 43615, 100298, 7282, 2222, 7282, 66, 11, 66, 0, 0, 0, 0, 39215, 59950, 2882, 2167, 2882, 11, 11, 11, 0, 0, 0, 0, 12067, 32802, 990, 275, 990, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The table of N_11. -/
def t11 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : ℕ :=
  ([152581, 347568, 27456, 8723, 27456, 364, 78, 364, 0, 0, 0, 0, 84799, 209352, 11440, 3289, 11440, 78, 12, 78, 0, 0, 0, 0, 77583, 116336, 4224, 3223, 4224, 12, 12, 12, 0, 0, 0, 0, 20515, 59268, 1353, 352, 1353, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The table of N_12. -/
def t12 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : ℕ :=
  ([300872, 732524, 44473, 13377, 44473, 455, 91, 455, 0, 0, 0, 0, 157014, 412412, 17381, 4732, 17381, 91, 13, 91, 0, 0, 0, 0, 145652, 214500, 6019, 4654, 6019, 13, 13, 13, 0, 0, 0, 0, 33540, 102388, 1807, 442, 1807, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The 37 states that the scan can reach after an admissible first step. -/
def reach (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : Bool :=
  ([true, false, false, true, true, true, true, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true] : List Bool).getD (idx p0 p1 k e) false

lemma reach_step : ∀ (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) (c : Fin 2 × Fin 2), reach p0 p1 k e = true →
    row p0 p1 k e c = true → reach c.1 c.2 (inc k (decide (code c < code (p0, p1)))) (cmp e c.1 c.2) = true := by
  decide +kernel

lemma N0 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : N p0 p1 k e 0 = t0 p0 p1 k e := by
  rw [N_zero]
  revert p0 p1 k e
  decide +kernel

lemma N1 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : N p0 p1 k e 1 = t1 p0 p1 k e := by
  rw [N_succ]
  simp only [N0]
  revert p0 p1 k e
  decide +kernel

lemma N2 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : N p0 p1 k e 2 = t2 p0 p1 k e := by
  rw [N_succ]
  simp only [N1]
  revert p0 p1 k e
  decide +kernel

lemma N3 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : N p0 p1 k e 3 = t3 p0 p1 k e := by
  rw [N_succ]
  simp only [N2]
  revert p0 p1 k e
  decide +kernel

lemma N4 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : N p0 p1 k e 4 = t4 p0 p1 k e := by
  rw [N_succ]
  simp only [N3]
  revert p0 p1 k e
  decide +kernel

lemma N5 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : N p0 p1 k e 5 = t5 p0 p1 k e := by
  rw [N_succ]
  simp only [N4]
  revert p0 p1 k e
  decide +kernel

lemma N6 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : N p0 p1 k e 6 = t6 p0 p1 k e := by
  rw [N_succ]
  simp only [N5]
  revert p0 p1 k e
  decide +kernel

lemma N7 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : N p0 p1 k e 7 = t7 p0 p1 k e := by
  rw [N_succ]
  simp only [N6]
  revert p0 p1 k e
  decide +kernel

lemma N8 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : N p0 p1 k e 8 = t8 p0 p1 k e := by
  rw [N_succ]
  simp only [N7]
  revert p0 p1 k e
  decide +kernel

lemma N9 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : N p0 p1 k e 9 = t9 p0 p1 k e := by
  rw [N_succ]
  simp only [N8]
  revert p0 p1 k e
  decide +kernel

lemma N10 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : N p0 p1 k e 10 = t10 p0 p1 k e := by
  rw [N_succ]
  simp only [N9]
  revert p0 p1 k e
  decide +kernel

lemma N11 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : N p0 p1 k e 11 = t11 p0 p1 k e := by
  rw [N_succ]
  simp only [N10]
  revert p0 p1 k e
  decide +kernel

lemma N12 (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3) : N p0 p1 k e 12 = t12 p0 p1 k e := by
  rw [N_succ]
  simp only [N11]
  revert p0 p1 k e
  decide +kernel

/-- The recurrence of the continuation counts, on every reachable state. -/
theorem N_rec (m : ℕ) : ∀ (p0 p1 : Fin 2) (k : Fin 4) (e : Fin 3), reach p0 p1 k e = true →
    (N p0 p1 k e (m + 11) : ℤ) = (11) * (N p0 p1 k e (m + 10) : ℤ) + (-55) * (N p0 p1 k e (m + 9) : ℤ) + (165) * (N p0 p1 k e (m + 8) : ℤ) + (-330) * (N p0 p1 k e (m + 7) : ℤ) + (462) * (N p0 p1 k e (m + 6) : ℤ) + (-462) * (N p0 p1 k e (m + 5) : ℤ) + (330) * (N p0 p1 k e (m + 4) : ℤ) + (-165) * (N p0 p1 k e (m + 3) : ℤ) + (55) * (N p0 p1 k e (m + 2) : ℤ) + (-11) * (N p0 p1 k e (m + 1) : ℤ) + (1) * (N p0 p1 k e (m) : ℤ) := by
  induction m with
  | zero =>
    intro p0 p1 k e hr
    simp only [Nat.zero_add]
    rw [N11, N10, N9, N8, N7, N6, N5, N4, N3, N2, N1, N0]
    revert p0 p1 k e
    decide +kernel
  | succ m ih =>
    intro p0 p1 k e hr
    rw [N_succ p0 p1 k e (m + 11), N_succ p0 p1 k e (m + 10), N_succ p0 p1 k e (m + 9), N_succ p0 p1 k e (m + 8), N_succ p0 p1 k e (m + 7), N_succ p0 p1 k e (m + 6), N_succ p0 p1 k e (m + 5), N_succ p0 p1 k e (m + 4), N_succ p0 p1 k e (m + 3), N_succ p0 p1 k e (m + 2), N_succ p0 p1 k e (m + 1), N_succ p0 p1 k e (m)]
    push_cast
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    split_ifs with hc
    · exact ih _ _ _ _ (reach_step p0 p1 k e c hr hc)
    · simp

/-- The first step, without the rest of the scan. -/
def first (c : Fin 2 × Fin 2) : Bool :=
  true

theorem a_succ (n : ℕ) : a (n + 1) = ∑ c : Fin 2 × Fin 2,
    if first c = true then N c.1 c.2 0 (cmp 0 c.1 c.2) n else 0 := by
  have h := sum_cons n (fun l => if valid l = true then 1 else 0)
  unfold a
  rw [Finset.card_filter, h]
  apply Finset.sum_congr rfl
  intro c _
  have hr : first c = true := rfl
  rw [if_pos hr]
  unfold N
  apply Finset.sum_congr rfl
  intro y _
  rfl

lemma reach_first : ∀ c : Fin 2 × Fin 2, first c = true → reach c.1 c.2 0 (cmp 0 c.1 c.2) = true := by
  decide +kernel

/-- The recurrence of a, for n >= 12. -/
theorem a_rec (m : ℕ) : (a (m + 12) : ℤ) = (11) * (a (m + 11) : ℤ) + (-55) * (a (m + 10) : ℤ) + (165) * (a (m + 9) : ℤ) + (-330) * (a (m + 8) : ℤ) + (462) * (a (m + 7) : ℤ) + (-462) * (a (m + 6) : ℤ) + (330) * (a (m + 5) : ℤ) + (-165) * (a (m + 4) : ℤ) + (55) * (a (m + 3) : ℤ) + (-11) * (a (m + 2) : ℤ) + (1) * (a (m + 1) : ℤ) := by
  rw [a_succ (m + 11), a_succ (m + 10), a_succ (m + 9), a_succ (m + 8), a_succ (m + 7), a_succ (m + 6), a_succ (m + 5), a_succ (m + 4), a_succ (m + 3), a_succ (m + 2), a_succ (m + 1), a_succ (m)]
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  split_ifs with hc
  · exact N_rec m _ _ _ _ (reach_first c hc)
  · simp

lemma values : a 1 = 0 ∧ a 2 = 2 ∧ a 3 = 20 ∧ a 4 = 117 ∧ a 5 = 503 ∧ a 6 = 1750 ∧ a 7 = 5209 ∧ a 8 = 13751 ∧ a 9 = 33000 ∧ a 10 = 73282 ∧ a 11 = 152581 ∧ a 12 = 300872 ∧ a 13 = 566293 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a_succ]
    simp only [N0]
    decide +kernel
  · rw [a_succ]
    simp only [N1]
    decide +kernel
  · rw [a_succ]
    simp only [N2]
    decide +kernel
  · rw [a_succ]
    simp only [N3]
    decide +kernel
  · rw [a_succ]
    simp only [N4]
    decide +kernel
  · rw [a_succ]
    simp only [N5]
    decide +kernel
  · rw [a_succ]
    simp only [N6]
    decide +kernel
  · rw [a_succ]
    simp only [N7]
    decide +kernel
  · rw [a_succ]
    simp only [N8]
    decide +kernel
  · rw [a_succ]
    simp only [N9]
    decide +kernel
  · rw [a_succ]
    simp only [N10]
    decide +kernel
  · rw [a_succ]
    simp only [N11]
    decide +kernel
  · rw [a_succ]
    simp only [N12]
    decide +kernel

/-- The closed form, for n >= 1. -/
theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (-11 / 168) * (n : ℚ) + (-2167 / 50400) * (n : ℚ) ^ 2 + (197 / 4032) * (n : ℚ) ^ 3 + (12329 / 362880) * (n : ℚ) ^ 4 + (167 / 11520) * (n : ℚ) ^ 5 + (1513 / 172800) * (n : ℚ) ^ 6 + (17 / 8064) * (n : ℚ) ^ 7 + (1 / 3780) * (n : ℚ) ^ 8 + (1 / 80640) * (n : ℚ) ^ 9 + (1 / 3628800) * (n : ℚ) ^ 10 := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13⟩ := values
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 12 with h4 | h4
    · interval_cases n
      · rw [v1]; norm_num
      · rw [v2]; norm_num
      · rw [v3]; norm_num
      · rw [v4]; norm_num
      · rw [v5]; norm_num
      · rw [v6]; norm_num
      · rw [v7]; norm_num
      · rw [v8]; norm_num
      · rw [v9]; norm_num
      · rw [v10]; norm_num
      · rw [v11]; norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
      have h := a_rec m
      have h' : (a (m + 12) : ℚ) = (11) * (a (m + 11) : ℚ) + (-55) * (a (m + 10) : ℚ) + (165) * (a (m + 9) : ℚ) + (-330) * (a (m + 8) : ℚ) + (462) * (a (m + 7) : ℚ) + (-462) * (a (m + 6) : ℚ) + (330) * (a (m + 5) : ℚ) + (-165) * (a (m + 4) : ℚ) + (55) * (a (m + 3) : ℚ) + (-11) * (a (m + 2) : ℚ) + (1) * (a (m + 1) : ℚ) := by
        exact_mod_cast h
      rw [h', ih (m + 11) (by omega) (by omega), ih (m + 10) (by omega) (by omega), ih (m + 9) (by omega) (by omega), ih (m + 8) (by omega) (by omega), ih (m + 7) (by omega) (by omega), ih (m + 6) (by omega) (by omega), ih (m + 5) (by omega) (by omega), ih (m + 4) (by omega) (by omega), ih (m + 3) (by omega) (by omega), ih (m + 2) (by omega) (by omega), ih (m + 1) (by omega) (by omega)]
      push_cast
      ring

/-- The recurrence of the g.f. denominator, from the closed form. -/
theorem den_rec (m : ℕ) : (1) * (a (m + 12) : ℚ) + (-11) * (a (m + 11) : ℚ) + (55) * (a (m + 10) : ℚ) + (-165) * (a (m + 9) : ℚ) + (330) * (a (m + 8) : ℚ) + (-462) * (a (m + 7) : ℚ) + (462) * (a (m + 6) : ℚ) + (-330) * (a (m + 5) : ℚ) + (165) * (a (m + 4) : ℚ) + (-55) * (a (m + 3) : ℚ) + (11) * (a (m + 2) : ℚ) + (-1) * (a (m + 1) : ℚ) = 0 := by
  rw [closed (m + 12) (by omega), closed (m + 11) (by omega), closed (m + 10) (by omega), closed (m + 9) (by omega), closed (m + 8) (by omega), closed (m + 7) (by omega), closed (m + 6) (by omega), closed (m + 5) (by omega), closed (m + 4) (by omega), closed (m + 3) (by omega), closed (m + 2) (by omega), closed (m + 1) (by omega)]
  push_cast
  ring

/-- The g.f., as A(x) * den = num in Q[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) * ((1 - X) ^ 11) =
    X ^ 2 * (2 - 2 * X + 7 * X ^ 2 - 14 * X ^ 3 + 12 * X ^ 4 - 5 * X ^ 5 + X ^ 6) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) with hA
  have e1 : A * ((1 - X) ^ 11) = C (1 : ℚ) * (A * X ^ 0) + C (-11 : ℚ) * (A * X ^ 1) + C (55 : ℚ) * (A * X ^ 2) + C (-165 : ℚ) * (A * X ^ 3) + C (330 : ℚ) * (A * X ^ 4) + C (-462 : ℚ) * (A * X ^ 5) + C (462 : ℚ) * (A * X ^ 6) + C (-330 : ℚ) * (A * X ^ 7) + C (165 : ℚ) * (A * X ^ 8) + C (-55 : ℚ) * (A * X ^ 9) + C (11 : ℚ) * (A * X ^ 10) + C (-1 : ℚ) * (A * X ^ 11) := by
    simp only [map_intCast, map_natCast, map_ofNat, map_neg, map_one, map_zero]; ring
  have e2 : (X ^ 2 * (2 - 2 * X + 7 * X ^ 2 - 14 * X ^ 3 + 12 * X ^ 4 - 5 * X ^ 5 + X ^ 6) : ℚ⟦X⟧) = X ^ 0 * C (0 : ℚ) + X ^ 1 * C (0 : ℚ) + X ^ 2 * C (2 : ℚ) + X ^ 3 * C (-2 : ℚ) + X ^ 4 * C (7 : ℚ) + X ^ 5 * C (-14 : ℚ) + X ^ 6 * C (12 : ℚ) + X ^ 7 * C (-5 : ℚ) + X ^ 8 * C (1 : ℚ) := by
    simp only [map_intCast, map_natCast, map_ofNat, map_neg, map_one, map_zero]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℚ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v := values
  rcases Nat.lt_or_ge n 12 with hn | hn
  · interval_cases n <;> simp_all <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
    have h := den_rec m
    simp only [show m + 12 - 0 = m + 12 by omega, show ¬ m + 12 = 0 by omega, show 0 ≤ m + 12 by omega, show m + 12 - 1 = m + 11 by omega, show ¬ m + 11 = 0 by omega, show 1 ≤ m + 12 by omega, show m + 12 - 2 = m + 10 by omega, show ¬ m + 10 = 0 by omega, show 2 ≤ m + 12 by omega, show m + 12 - 3 = m + 9 by omega, show ¬ m + 9 = 0 by omega, show 3 ≤ m + 12 by omega, show m + 12 - 4 = m + 8 by omega, show ¬ m + 8 = 0 by omega, show 4 ≤ m + 12 by omega, show m + 12 - 5 = m + 7 by omega, show ¬ m + 7 = 0 by omega, show 5 ≤ m + 12 by omega, show m + 12 - 6 = m + 6 by omega, show ¬ m + 6 = 0 by omega, show 6 ≤ m + 12 by omega, show m + 12 - 7 = m + 5 by omega, show ¬ m + 5 = 0 by omega, show 7 ≤ m + 12 by omega, show m + 12 - 8 = m + 4 by omega, show ¬ m + 4 = 0 by omega, show 8 ≤ m + 12 by omega, show m + 12 - 9 = m + 3 by omega, show ¬ m + 3 = 0 by omega, show 9 ≤ m + 12 by omega, show m + 12 - 10 = m + 2 by omega, show ¬ m + 2 = 0 by omega, show 10 ≤ m + 12 by omega, show m + 12 - 11 = m + 1 by omega, show ¬ m + 1 = 0 by omega, show 11 ≤ m + 12 by omega, show ¬ m + 12 = 0 by omega, show ¬ m + 12 = 1 by omega, show ¬ m + 12 = 2 by omega, show ¬ m + 12 = 3 by omega, show ¬ m + 12 = 4 by omega, show ¬ m + 12 = 5 by omega, show ¬ m + 12 = 6 by omega, show ¬ m + 12 = 7 by omega, show ¬ m + 12 = 8 by omega, if_true, if_false, Nat.sub_zero, ite_true, ite_false]
    linear_combination h

/-- Controls: the entry's data a(1..29). -/
theorem controls : a 1 = 0 ∧ a 2 = 2 ∧ a 3 = 20 ∧ a 4 = 117 ∧ a 5 = 503 ∧ a 6 = 1750 ∧ a 7 = 5209 ∧ a 8 = 13751 ∧ a 9 = 33000 ∧ a 10 = 73282 ∧ a 11 = 152581 ∧ a 12 = 300872 ∧ a 13 = 566293 ∧ a 14 = 1023724 ∧ a 15 = 1786462 ∧ a 16 = 3021818 ∧ a 17 = 4971616 ∧ a 18 = 7978746 ∧ a 19 = 12521114 ∧ a 20 = 19254543 ∧ a 21 = 29066411 ∧ a 22 = 43142066 ∧ a 23 = 63046335 ∧ a 24 = 90822745 ∧ a 25 = 129113400 ∧ a 26 = 181302810 ∧ a 27 = 251689347 ∧ a 28 = 345688410 ∧ a 29 = 470071817 := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13⟩ := values
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact v1
  · exact v2
  · exact v3
  · exact v4
  · exact v5
  · exact v6
  · exact v7
  · exact v8
  · exact v9
  · exact v10
  · exact v11
  · exact v12
  · exact v13
  · rw [← Nat.cast_inj (R := ℚ), closed _ (by norm_num)]; norm_num
  · rw [← Nat.cast_inj (R := ℚ), closed _ (by norm_num)]; norm_num
  · rw [← Nat.cast_inj (R := ℚ), closed _ (by norm_num)]; norm_num
  · rw [← Nat.cast_inj (R := ℚ), closed _ (by norm_num)]; norm_num
  · rw [← Nat.cast_inj (R := ℚ), closed _ (by norm_num)]; norm_num
  · rw [← Nat.cast_inj (R := ℚ), closed _ (by norm_num)]; norm_num
  · rw [← Nat.cast_inj (R := ℚ), closed _ (by norm_num)]; norm_num
  · rw [← Nat.cast_inj (R := ℚ), closed _ (by norm_num)]; norm_num
  · rw [← Nat.cast_inj (R := ℚ), closed _ (by norm_num)]; norm_num
  · rw [← Nat.cast_inj (R := ℚ), closed _ (by norm_num)]; norm_num
  · rw [← Nat.cast_inj (R := ℚ), closed _ (by norm_num)]; norm_num
  · rw [← Nat.cast_inj (R := ℚ), closed _ (by norm_num)]; norm_num
  · rw [← Nat.cast_inj (R := ℚ), closed _ (by norm_num)]; norm_num
  · rw [← Nat.cast_inj (R := ℚ), closed _ (by norm_num)]; norm_num
  · rw [← Nat.cast_inj (R := ℚ), closed _ (by norm_num)]; norm_num
  · rw [← Nat.cast_inj (R := ℚ), closed _ (by norm_num)]; norm_num

set_option maxHeartbeats 4000000 in
/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) * (1 - X) ^ 11 =
      X ^ 2 * (2 - 2 * X + 7 * X ^ 2 - 14 * X ^ 3 + 12 * X ^ 4 - 5 * X ^ 5 + X ^ 6) ∧
    ∀ n : ℕ, 11 < n → (a n : ℤ) = 11 * (a (n - 1) : ℤ) - 55 * (a (n - 2) : ℤ) + 165 * (a (n - 3) : ℤ) - 330 * (a (n - 4) : ℤ) + 462 * (a (n - 5) : ℤ) - 462 * (a (n - 6) : ℤ) + 330 * (a (n - 7) : ℤ) - 165 * (a (n - 8) : ℤ) + 55 * (a (n - 9) : ℤ) - 11 * (a (n - 10) : ℤ) + (a (n - 11) : ℤ) := by
  refine ⟨gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
  simp only [show m + 12 - 1 = m + 11 by omega, show m + 12 - 2 = m + 10 by omega, show m + 12 - 3 = m + 9 by omega, show m + 12 - 4 = m + 8 by omega, show m + 12 - 5 = m + 7 by omega, show m + 12 - 6 = m + 6 by omega, show m + 12 - 7 = m + 5 by omega, show m + 12 - 8 = m + 4 by omega, show m + 12 - 9 = m + 3 by omega, show m + 12 - 10 = m + 2 by omega, show m + 12 - 11 = m + 1 by omega]
  have key : ((a (m + 12) : ℤ) : ℚ) = ((11 * (a (m + 11) : ℤ) - 55 * (a (m + 10) : ℤ) + 165 * (a (m + 9) : ℤ) - 330 * (a (m + 8) : ℤ) + 462 * (a (m + 7) : ℤ) - 462 * (a (m + 6) : ℤ) + 330 * (a (m + 5) : ℤ) - 165 * (a (m + 4) : ℤ) + 55 * (a (m + 3) : ℤ) - 11 * (a (m + 2) : ℤ) + (a (m + 1) : ℤ) : ℤ) : ℚ) := by
    push_cast
    rw [closed (m + 12) (by omega), closed (m + 11) (by omega), closed (m + 10) (by omega), closed (m + 9) (by omega), closed (m + 8) (by omega), closed (m + 7) (by omega), closed (m + 6) (by omega), closed (m + 5) (by omega), closed (m + 4) (by omega), closed (m + 3) (by omega), closed (m + 2) (by omega), closed (m + 1) (by omega)]
    push_cast
    ring
  exact Int.cast_injective key

end OMA.S_oeis_a278772

theorem OMA.solution : type_of% @OMA.S_oeis_a278772.main :=
  OMA.S_oeis_a278772.conjecture
