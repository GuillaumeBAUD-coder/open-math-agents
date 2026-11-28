import OMAStatements.S_oeis_a278670

/-!
Proof of Barker's conjectures for A278670 by a transfer count. N s m counts the continuations by m
rows of the scan from the state s (previous row, saturated row-mistake count, column comparison).
Every reachable state satisfies the linear recurrence of `N_rec`, checked by the kernel on tables of
N_0..N_K and propagated by induction through the one-row recursion of N. This gives Hardin's
empirical polynomial by strong induction, and the g.f. and recurrence follow from it.
-/

namespace OMA.S_oeis_a278670

open PowerSeries

/-- The continuations by m steps of the scan from a state. -/
def N (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) (m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 2 × Fin 2, if ok p0 p1 k e (List.ofFn y) = true then 1 else 0

theorem sum_cons (m : ℕ) (f : List (Fin 2 × Fin 2) → ℕ) :
    ∑ x : Fin (m + 1) → Fin 2 × Fin 2, f (List.ofFn x) =
      ∑ c : Fin 2 × Fin 2, ∑ y : Fin m → Fin 2 × Fin 2, f (c :: List.ofFn y) := by
  rw [← (Fin.consEquiv fun _ => Fin 2 × Fin 2).sum_comp]
  rw [Fintype.sum_prod_type (f := fun p : (Fin 2 × Fin 2) × (Fin m → Fin 2 × Fin 2) =>
    f (List.ofFn ((Fin.consEquiv fun _ => Fin 2 × Fin 2) p)))]
  simp [List.ofFn_succ]

theorem N_zero (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) : N p0 p1 k e 0 = if ok p0 p1 k e [] = true then 1 else 0 := by
  simp [N]

/-- The condition on one step, without the rest of the scan. -/
def row (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) (c : Fin 2 × Fin 2) : Bool :=
  true

theorem N_succ (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) (m : ℕ) :
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
def idx (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) : ℕ := ((p0.val * 2 + p1.val) * 3 + k.val) * 3 + e.val

/-- The table of N_0. -/
def t0 (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) : ℕ :=
  ([0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The table of N_1. -/
def t1 (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) : ℕ :=
  ([1, 0, 4, 3, 4, 0, 0, 0, 0, 2, 1, 3, 2, 3, 0, 0, 0, 0, 1, 2, 2, 2, 2, 0, 0, 0, 0, 2, 3, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The table of N_2. -/
def t2 (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) : ℕ :=
  ([8, 6, 10, 6, 10, 0, 0, 0, 0, 10, 10, 6, 3, 6, 0, 0, 0, 0, 7, 12, 3, 3, 3, 0, 0, 0, 0, 7, 12, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The table of N_3. -/
def t3 (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) : ℕ :=
  ([33, 40, 20, 10, 20, 0, 0, 0, 0, 31, 44, 10, 4, 10, 0, 0, 0, 0, 25, 40, 4, 4, 4, 0, 0, 0, 0, 16, 31, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The table of N_4. -/
def t4 (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) : ℕ :=
  ([99, 155, 35, 15, 35, 0, 0, 0, 0, 76, 135, 15, 5, 15, 0, 0, 0, 0, 66, 101, 5, 5, 5, 0, 0, 0, 0, 30, 65, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The table of N_5. -/
def t5 (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) : ℕ :=
  ([245, 456, 56, 21, 56, 0, 0, 0, 0, 161, 336, 21, 6, 21, 0, 0, 0, 0, 146, 216, 6, 6, 6, 0, 0, 0, 0, 50, 120, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The table of N_6. -/
def t6 (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) : ℕ :=
  ([532, 1128, 84, 28, 84, 0, 0, 0, 0, 308, 728, 28, 7, 28, 0, 0, 0, 0, 287, 413, 7, 7, 7, 0, 0, 0, 0, 77, 203, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The table of N_7. -/
def t7 (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) : ℕ :=
  ([1050, 2472, 120, 36, 120, 0, 0, 0, 0, 546, 1428, 36, 8, 36, 0, 0, 0, 0, 518, 728, 8, 8, 8, 0, 0, 0, 0, 112, 322, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The table of N_8. -/
def t8 (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) : ℕ :=
  ([1926, 4950, 165, 45, 165, 0, 0, 0, 0, 912, 2598, 45, 9, 45, 0, 0, 0, 0, 876, 1206, 9, 9, 9, 0, 0, 0, 0, 156, 486, 1, 1, 1, 0, 0, 0, 0] : List ℕ).getD (idx p0 p1 k e) 0

/-- The 27 states that the scan can reach after an admissible first step. -/
def reach (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) : Bool :=
  ([true, false, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true] : List Bool).getD (idx p0 p1 k e) false

lemma reach_step : ∀ (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) (c : Fin 2 × Fin 2), reach p0 p1 k e = true →
    row p0 p1 k e c = true → reach c.1 c.2 (inc k (decide (code c < code (p0, p1)))) (cmp e c.1 c.2) = true := by
  decide +kernel

lemma N0 (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) : N p0 p1 k e 0 = t0 p0 p1 k e := by
  rw [N_zero]
  revert p0 p1 k e
  decide +kernel

lemma N1 (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) : N p0 p1 k e 1 = t1 p0 p1 k e := by
  rw [N_succ]
  simp only [N0]
  revert p0 p1 k e
  decide +kernel

lemma N2 (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) : N p0 p1 k e 2 = t2 p0 p1 k e := by
  rw [N_succ]
  simp only [N1]
  revert p0 p1 k e
  decide +kernel

lemma N3 (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) : N p0 p1 k e 3 = t3 p0 p1 k e := by
  rw [N_succ]
  simp only [N2]
  revert p0 p1 k e
  decide +kernel

lemma N4 (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) : N p0 p1 k e 4 = t4 p0 p1 k e := by
  rw [N_succ]
  simp only [N3]
  revert p0 p1 k e
  decide +kernel

lemma N5 (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) : N p0 p1 k e 5 = t5 p0 p1 k e := by
  rw [N_succ]
  simp only [N4]
  revert p0 p1 k e
  decide +kernel

lemma N6 (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) : N p0 p1 k e 6 = t6 p0 p1 k e := by
  rw [N_succ]
  simp only [N5]
  revert p0 p1 k e
  decide +kernel

lemma N7 (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) : N p0 p1 k e 7 = t7 p0 p1 k e := by
  rw [N_succ]
  simp only [N6]
  revert p0 p1 k e
  decide +kernel

lemma N8 (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3) : N p0 p1 k e 8 = t8 p0 p1 k e := by
  rw [N_succ]
  simp only [N7]
  revert p0 p1 k e
  decide +kernel

/-- The recurrence of the continuation counts, on every reachable state. -/
theorem N_rec (m : ℕ) : ∀ (p0 p1 : Fin 2) (k : Fin 3) (e : Fin 3), reach p0 p1 k e = true →
    (N p0 p1 k e (m + 7) : ℤ) = (7) * (N p0 p1 k e (m + 6) : ℤ) + (-21) * (N p0 p1 k e (m + 5) : ℤ) + (35) * (N p0 p1 k e (m + 4) : ℤ) + (-35) * (N p0 p1 k e (m + 3) : ℤ) + (21) * (N p0 p1 k e (m + 2) : ℤ) + (-7) * (N p0 p1 k e (m + 1) : ℤ) + (1) * (N p0 p1 k e (m) : ℤ) := by
  induction m with
  | zero =>
    intro p0 p1 k e hr
    simp only [Nat.zero_add]
    rw [N7, N6, N5, N4, N3, N2, N1, N0]
    revert p0 p1 k e
    decide +kernel
  | succ m ih =>
    intro p0 p1 k e hr
    rw [N_succ p0 p1 k e (m + 7), N_succ p0 p1 k e (m + 6), N_succ p0 p1 k e (m + 5), N_succ p0 p1 k e (m + 4), N_succ p0 p1 k e (m + 3), N_succ p0 p1 k e (m + 2), N_succ p0 p1 k e (m + 1), N_succ p0 p1 k e (m)]
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

/-- The recurrence of a, for n >= 8. -/
theorem a_rec (m : ℕ) : (a (m + 8) : ℤ) = (7) * (a (m + 7) : ℤ) + (-21) * (a (m + 6) : ℤ) + (35) * (a (m + 5) : ℤ) + (-35) * (a (m + 4) : ℤ) + (21) * (a (m + 3) : ℤ) + (-7) * (a (m + 2) : ℤ) + (1) * (a (m + 1) : ℤ) := by
  rw [a_succ (m + 7), a_succ (m + 6), a_succ (m + 5), a_succ (m + 4), a_succ (m + 3), a_succ (m + 2), a_succ (m + 1), a_succ (m)]
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  split_ifs with hc
  · exact N_rec m _ _ _ _ (reach_first c hc)
  · simp

lemma values : a 1 = 1 ∧ a 2 = 8 ∧ a 3 = 33 ∧ a 4 = 99 ∧ a 5 = 245 ∧ a 6 = 532 ∧ a 7 = 1050 ∧ a 8 = 1926 ∧ a 9 = 3333 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

/-- The closed form, for n >= 1. -/
theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (1 / 12) * (n : ℚ) + (61 / 180) * (n : ℚ) ^ 2 + (19 / 48) * (n : ℚ) ^ 3 + (23 / 144) * (n : ℚ) ^ 4 + (1 / 48) * (n : ℚ) ^ 5 + (1 / 720) * (n : ℚ) ^ 6 := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := values
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 8 with h4 | h4
    · interval_cases n
      · rw [v1]; norm_num
      · rw [v2]; norm_num
      · rw [v3]; norm_num
      · rw [v4]; norm_num
      · rw [v5]; norm_num
      · rw [v6]; norm_num
      · rw [v7]; norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
      have h := a_rec m
      have h' : (a (m + 8) : ℚ) = (7) * (a (m + 7) : ℚ) + (-21) * (a (m + 6) : ℚ) + (35) * (a (m + 5) : ℚ) + (-35) * (a (m + 4) : ℚ) + (21) * (a (m + 3) : ℚ) + (-7) * (a (m + 2) : ℚ) + (1) * (a (m + 1) : ℚ) := by
        exact_mod_cast h
      rw [h', ih (m + 7) (by omega) (by omega), ih (m + 6) (by omega) (by omega), ih (m + 5) (by omega) (by omega), ih (m + 4) (by omega) (by omega), ih (m + 3) (by omega) (by omega), ih (m + 2) (by omega) (by omega), ih (m + 1) (by omega) (by omega)]
      push_cast
      ring

/-- The recurrence of the g.f. denominator, from the closed form. -/
theorem den_rec (m : ℕ) : (1) * (a (m + 8) : ℚ) + (-7) * (a (m + 7) : ℚ) + (21) * (a (m + 6) : ℚ) + (-35) * (a (m + 5) : ℚ) + (35) * (a (m + 4) : ℚ) + (-21) * (a (m + 3) : ℚ) + (7) * (a (m + 2) : ℚ) + (-1) * (a (m + 1) : ℚ) = 0 := by
  rw [closed (m + 8) (by omega), closed (m + 7) (by omega), closed (m + 6) (by omega), closed (m + 5) (by omega), closed (m + 4) (by omega), closed (m + 3) (by omega), closed (m + 2) (by omega), closed (m + 1) (by omega)]
  push_cast
  ring

/-- The g.f., as A(x) * den = num in Q[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) * ((1 - X) ^ 7) =
    X * (1 + X - 2 * X ^ 2 + X ^ 3) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) with hA
  have e1 : A * ((1 - X) ^ 7) = C (1 : ℚ) * (A * X ^ 0) + C (-7 : ℚ) * (A * X ^ 1) + C (21 : ℚ) * (A * X ^ 2) + C (-35 : ℚ) * (A * X ^ 3) + C (35 : ℚ) * (A * X ^ 4) + C (-21 : ℚ) * (A * X ^ 5) + C (7 : ℚ) * (A * X ^ 6) + C (-1 : ℚ) * (A * X ^ 7) := by
    simp only [map_intCast, map_natCast, map_ofNat, map_neg, map_one, map_zero]; ring
  have e2 : (X * (1 + X - 2 * X ^ 2 + X ^ 3) : ℚ⟦X⟧) = X ^ 0 * C (0 : ℚ) + X ^ 1 * C (1 : ℚ) + X ^ 2 * C (1 : ℚ) + X ^ 3 * C (-2 : ℚ) + X ^ 4 * C (1 : ℚ) := by
    simp only [map_intCast, map_natCast, map_ofNat, map_neg, map_one, map_zero]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℚ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v := values
  rcases Nat.lt_or_ge n 8 with hn | hn
  · interval_cases n <;> simp_all <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    have h := den_rec m
    simp only [show m + 8 - 0 = m + 8 by omega, show ¬ m + 8 = 0 by omega, show 0 ≤ m + 8 by omega, show m + 8 - 1 = m + 7 by omega, show ¬ m + 7 = 0 by omega, show 1 ≤ m + 8 by omega, show m + 8 - 2 = m + 6 by omega, show ¬ m + 6 = 0 by omega, show 2 ≤ m + 8 by omega, show m + 8 - 3 = m + 5 by omega, show ¬ m + 5 = 0 by omega, show 3 ≤ m + 8 by omega, show m + 8 - 4 = m + 4 by omega, show ¬ m + 4 = 0 by omega, show 4 ≤ m + 8 by omega, show m + 8 - 5 = m + 3 by omega, show ¬ m + 3 = 0 by omega, show 5 ≤ m + 8 by omega, show m + 8 - 6 = m + 2 by omega, show ¬ m + 2 = 0 by omega, show 6 ≤ m + 8 by omega, show m + 8 - 7 = m + 1 by omega, show ¬ m + 1 = 0 by omega, show 7 ≤ m + 8 by omega, show ¬ m + 8 = 0 by omega, show ¬ m + 8 = 1 by omega, show ¬ m + 8 = 2 by omega, show ¬ m + 8 = 3 by omega, show ¬ m + 8 = 4 by omega, if_true, if_false, Nat.sub_zero, ite_true, ite_false]
    linear_combination h

/-- Controls: the entry's data a(1..34). -/
theorem controls : a 1 = 1 ∧ a 2 = 8 ∧ a 3 = 33 ∧ a 4 = 99 ∧ a 5 = 245 ∧ a 6 = 532 ∧ a 7 = 1050 ∧ a 8 = 1926 ∧ a 9 = 3333 ∧ a 10 = 5500 ∧ a 11 = 8723 ∧ a 12 = 13377 ∧ a 13 = 19929 ∧ a 14 = 28952 ∧ a 15 = 41140 ∧ a 16 = 57324 ∧ a 17 = 78489 ∧ a 18 = 105792 ∧ a 19 = 140581 ∧ a 20 = 184415 ∧ a 21 = 239085 ∧ a 22 = 306636 ∧ a 23 = 389390 ∧ a 24 = 489970 ∧ a 25 = 611325 ∧ a 26 = 756756 ∧ a 27 = 929943 ∧ a 28 = 1134973 ∧ a 29 = 1376369 ∧ a 30 = 1659120 ∧ a 31 = 1988712 ∧ a 32 = 2371160 ∧ a 33 = 2813041 ∧ a 34 = 3321528 := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := values
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact v1
  · exact v2
  · exact v3
  · exact v4
  · exact v5
  · exact v6
  · exact v7
  · exact v8
  · exact v9
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
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) * (1 - X) ^ 7 =
      X * (1 + X - 2 * X ^ 2 + X ^ 3) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * (a (n - 1) : ℤ) - 21 * (a (n - 2) : ℤ) + 35 * (a (n - 3) : ℤ) - 35 * (a (n - 4) : ℤ) + 21 * (a (n - 5) : ℤ) - 7 * (a (n - 6) : ℤ) + (a (n - 7) : ℤ) := by
  refine ⟨gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  simp only [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega, show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega, show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega, show m + 8 - 7 = m + 1 by omega]
  have key : ((a (m + 8) : ℤ) : ℚ) = ((7 * (a (m + 7) : ℤ) - 21 * (a (m + 6) : ℤ) + 35 * (a (m + 5) : ℤ) - 35 * (a (m + 4) : ℤ) + 21 * (a (m + 3) : ℤ) - 7 * (a (m + 2) : ℤ) + (a (m + 1) : ℤ) : ℤ) : ℚ) := by
    push_cast
    rw [closed (m + 8) (by omega), closed (m + 7) (by omega), closed (m + 6) (by omega), closed (m + 5) (by omega), closed (m + 4) (by omega), closed (m + 3) (by omega), closed (m + 2) (by omega), closed (m + 1) (by omega)]
    push_cast
    ring
  exact Int.cast_injective key

end OMA.S_oeis_a278670

theorem OMA.solution : type_of% @OMA.S_oeis_a278670.main :=
  OMA.S_oeis_a278670.conjecture
