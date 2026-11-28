import OMAStatements.S_oeis_a273766

/-!
Proof of the three conjectures of OEIS A273766 (Rule 913, 5-celled von Neumann neighbourhood).

Rule 913 = 1110010001 in binary: a cell with own value c and k ON orthogonal neighbours becomes
ON exactly when c + 2k is one of 0, 4, 7, 8, 9.
* Stage 1: the origin (ON, no ON neighbour) dies, its four neighbours (OFF, one ON neighbour)
  stay OFF, and every other cell (OFF, no ON neighbour) is born: the OFF cells form the plus
  |x| + |y| <= 1.
* Stage 2: the origin (OFF, no ON neighbour) is born, the four arms of the plus (OFF, three ON
  neighbours) stay OFF, the four diagonal cells (ON, two ON neighbours) die, and every other
  cell (ON, three or four ON neighbours) stays ON: the OFF cells form the 3 x 3 square without
  its centre.
* Stage 3: the origin (ON, no ON neighbour) dies, the eight cells around it (OFF, two ON
  neighbours) are born, and every other cell (ON, three or four ON neighbours) stays ON: the
  origin is the only OFF cell.
* Stage 4: the origin (OFF, four ON neighbours) is born and every other cell (ON, three or four
  ON neighbours) stays ON, so the plane is ON; an ON cell with four ON neighbours stays ON, so
  the plane stays ON from stage 4 on.
Each step is checked cell by cell on a small square around the origin (5 x 5, or 3 x 3 for the
step from stage 3 to stage 4); outside it the five cells read by the rule all carry the
background value.
Hence a(n) = (2n+1)^2 for n >= 4, while a(0..3) = 1, 4, 17, 48. The recurrence and the
generating function follow by computing with these values.
-/

namespace OMA.Helpers

open OMA.S_oeis_a273766

/-- Stage 1: the OFF cells form the plus |x| + |y| ≤ 1. -/
def a273766_S1 : Grid := fun x y =>
  !decide ((x = 0 ∧ -1 ≤ y ∧ y ≤ 1) ∨ (y = 0 ∧ -1 ≤ x ∧ x ≤ 1))

/-- Stage 2: the OFF cells form the 3 x 3 square without its centre. -/
def a273766_S2 : Grid := fun x y =>
  !decide (-1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 ∧ ¬ (x = 0 ∧ y = 0))

/-- Stage 3: the only OFF cell is the origin. -/
def a273766_S3 : Grid := fun x y => !decide (x = 0 ∧ y = 0)

/-- A cell whose own value and four neighbours are all ON stays ON (bit 9 of 913 is 1). -/
theorem a273766_step_on (g : Grid) (x y : ℤ) (h0 : g x y = true) (h1 : g (x+1) y = true)
    (h2 : g (x-1) y = true) (h3 : g x (y+1) = true) (h4 : g x (y-1) = true) :
    step g x y = true := by
  simp only [step, neighbors, h0, h1, h2, h3, h4]
  decide

/-- A cell whose own value and four neighbours are all OFF turns ON (bit 0 of 913 is 1). -/
theorem a273766_step_off (g : Grid) (x y : ℤ) (h0 : g x y = false) (h1 : g (x+1) y = false)
    (h2 : g (x-1) y = false) (h3 : g x (y+1) = false) (h4 : g x (y-1) = false) :
    step g x y = true := by
  simp only [step, neighbors, h0, h1, h2, h3, h4]
  decide

theorem a273766_initial_far (x y : ℤ) (h : x ≤ -1 ∨ 1 ≤ x ∨ y ≤ -1 ∨ 1 ≤ y) :
    initial x y = false := by
  simp only [initial, decide_eq_false_iff_not]
  omega

theorem a273766_S1_far (x y : ℤ) (h : x ≤ -2 ∨ 2 ≤ x ∨ y ≤ -2 ∨ 2 ≤ y) :
    a273766_S1 x y = true := by
  simp only [a273766_S1, Bool.not_eq_true', decide_eq_false_iff_not]
  omega

theorem a273766_S2_far (x y : ℤ) (h : x ≤ -2 ∨ 2 ≤ x ∨ y ≤ -2 ∨ 2 ≤ y) :
    a273766_S2 x y = true := by
  simp only [a273766_S2, Bool.not_eq_true', decide_eq_false_iff_not]
  omega

theorem a273766_S3_far (x y : ℤ) (h : x ≤ -1 ∨ 1 ≤ x ∨ y ≤ -1 ∨ 1 ≤ y) :
    a273766_S3 x y = true := by
  simp only [a273766_S3, Bool.not_eq_true', decide_eq_false_iff_not]
  omega

theorem a273766_step_initial : step initial = a273766_S1 := by
  funext x y
  by_cases h : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2
  · obtain ⟨h1, h2, h3, h4⟩ := h
    interval_cases x <;> interval_cases y <;> decide
  · rw [a273766_S1_far x y (by omega)]
    exact a273766_step_off _ x y (a273766_initial_far _ _ (by omega))
      (a273766_initial_far _ _ (by omega)) (a273766_initial_far _ _ (by omega))
      (a273766_initial_far _ _ (by omega)) (a273766_initial_far _ _ (by omega))

theorem a273766_step_S1 : step a273766_S1 = a273766_S2 := by
  funext x y
  by_cases h : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2
  · obtain ⟨h1, h2, h3, h4⟩ := h
    interval_cases x <;> interval_cases y <;> decide
  · rw [a273766_S2_far x y (by omega)]
    exact a273766_step_on _ x y (a273766_S1_far _ _ (by omega))
      (a273766_S1_far _ _ (by omega)) (a273766_S1_far _ _ (by omega))
      (a273766_S1_far _ _ (by omega)) (a273766_S1_far _ _ (by omega))

theorem a273766_step_S2 : step a273766_S2 = a273766_S3 := by
  funext x y
  by_cases h : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2
  · obtain ⟨h1, h2, h3, h4⟩ := h
    interval_cases x <;> interval_cases y <;> decide
  · rw [a273766_S3_far x y (by omega)]
    exact a273766_step_on _ x y (a273766_S2_far _ _ (by omega))
      (a273766_S2_far _ _ (by omega)) (a273766_S2_far _ _ (by omega))
      (a273766_S2_far _ _ (by omega)) (a273766_S2_far _ _ (by omega))

theorem a273766_step_S3 : step a273766_S3 = fun _ _ => true := by
  funext x y
  by_cases h : -1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1
  · obtain ⟨h1, h2, h3, h4⟩ := h
    interval_cases x <;> interval_cases y <;> decide
  · exact a273766_step_on _ x y (a273766_S3_far _ _ (by omega))
      (a273766_S3_far _ _ (by omega)) (a273766_S3_far _ _ (by omega))
      (a273766_S3_far _ _ (by omega)) (a273766_S3_far _ _ (by omega))

theorem a273766_step_all : step (fun _ _ => true) = fun _ _ => true := by
  funext x y
  exact a273766_step_on _ x y rfl rfl rfl rfl rfl

theorem a273766_state_one : state 1 = a273766_S1 := a273766_step_initial

theorem a273766_state_two : state 2 = a273766_S2 := by
  show step (state 1) = _
  rw [a273766_state_one, a273766_step_S1]

theorem a273766_state_three : state 3 = a273766_S3 := by
  show step (state 2) = _
  rw [a273766_state_two, a273766_step_S2]

/-- From stage 4 on, every cell is ON. -/
theorem a273766_state_add_four (m : ℕ) : state (m + 4) = fun _ _ => true := by
  induction m with
  | zero =>
    show step (state 3) = _
    rw [a273766_state_three, a273766_step_S3]
  | succ m ih =>
    show step (state (m + 4)) = _
    rw [ih, a273766_step_all]


/-- The closed form: from stage 4 on, the whole (2n+1) x (2n+1) square is ON. -/
theorem a273766_closed (n : ℕ) (hn : 4 ≤ n) : a n = (1 + 2 * n) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  unfold a
  rw [a273766_state_add_four m]
  simp only [bit, if_true, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  ring

theorem a273766_zero : a 0 = 1 := by decide

theorem a273766_one : a 1 = 4 := by
  unfold a
  rw [a273766_state_one]
  decide

theorem a273766_two : a 2 = 17 := by
  unfold a
  rw [a273766_state_two]
  decide

theorem a273766_three : a 3 = 48 := by
  unfold a
  rw [a273766_state_three]
  decide

theorem a273766_four : a 4 = 81 := a273766_closed 4 (by norm_num)

theorem a273766_five : a 5 = 121 := a273766_closed 5 (by norm_num)

theorem a273766_six : a 6 = 169 := a273766_closed 6 (by norm_num)

/-- The recurrence for n > 6: a third difference of a quadratic vanishes. -/
theorem a273766_rec (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 3 * (a (n-1) : ℤ) - 3 * (a (n-2) : ℤ) + (a (n-3) : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
    show m + 7 - 3 = m + 4 by omega]
  rw [a273766_closed (m + 7) (by omega), a273766_closed (m + 6) (by omega),
    a273766_closed (m + 5) (by omega), a273766_closed (m + 4) (by omega)]
  push_cast
  ring

/-- The generating function, as a product identity in ℤ⟦X⟧, checked coefficient by
coefficient: coefficients 0..6 from a(0..6) = 1, 4, 17, 48, 81, 121, 169, and coefficient
k >= 7 from the closed form. -/
theorem a273766_gf :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 =
      1 + PowerSeries.X + 8 * PowerSeries.X ^ 2 + 8 * PowerSeries.X ^ 3
        - 16 * PowerSeries.X ^ 4 + 5 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6 := by
  set p : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ)) with hp
  have e1 : p * (1 - PowerSeries.X) ^ 3 =
      p - PowerSeries.C (3 : ℤ) * (p * PowerSeries.X ^ 1)
        + PowerSeries.C (3 : ℤ) * (p * PowerSeries.X ^ 2) - p * PowerSeries.X ^ 3 := by
    rw [map_ofNat]
    ring
  have e2 : (1 + PowerSeries.X + 8 * PowerSeries.X ^ 2 + 8 * PowerSeries.X ^ 3
        - 16 * PowerSeries.X ^ 4 + 5 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6 : PowerSeries ℤ) =
      1 + PowerSeries.C (1 : ℤ) * PowerSeries.X ^ 1 + PowerSeries.C (8 : ℤ) * PowerSeries.X ^ 2
        + PowerSeries.C (8 : ℤ) * PowerSeries.X ^ 3 - PowerSeries.C (16 : ℤ) * PowerSeries.X ^ 4
        + PowerSeries.C (5 : ℤ) * PowerSeries.X ^ 5 + PowerSeries.C (1 : ℤ) * PowerSeries.X ^ 6 := by
    simp only [map_ofNat, map_one, pow_one, one_mul]
  rw [e1, e2]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_one]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', hp, PowerSeries.coeff_mk]
  by_cases hk : k < 7
  · interval_cases k <;>
      simp [a273766_zero, a273766_one, a273766_two, a273766_three, a273766_four,
        a273766_five, a273766_six]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
    rw [if_pos (show 1 ≤ j + 7 by omega), if_pos (show 2 ≤ j + 7 by omega),
      if_pos (show 3 ≤ j + 7 by omega), if_neg (show ¬ (j + 7 = 0) by omega),
      if_neg (show ¬ (j + 7 = 1) by omega), if_neg (show ¬ (j + 7 = 2) by omega),
      if_neg (show ¬ (j + 7 = 3) by omega), if_neg (show ¬ (j + 7 = 4) by omega),
      if_neg (show ¬ (j + 7 = 5) by omega), if_neg (show ¬ (j + 7 = 6) by omega)]
    rw [show j + 7 - 1 = j + 6 by omega, show j + 7 - 2 = j + 5 by omega,
      show j + 7 - 3 = j + 4 by omega]
    rw [a273766_closed (j + 7) (by omega), a273766_closed (j + 6) (by omega),
      a273766_closed (j + 5) (by omega), a273766_closed (j + 4) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a273766.main :=
  ⟨fun n hn => OMA.Helpers.a273766_closed n (by omega),
    fun n hn => OMA.Helpers.a273766_rec n hn, OMA.Helpers.a273766_gf⟩
