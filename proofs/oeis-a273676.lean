import OMAStatements.S_oeis_a273676

-- Problem: A273676: Number of active (ON, black) cells at stage 2^n-1 of the two-dimensional cellular automaton defined by Rule 833, based on the 5-celled von Neumann neighborhood.
-- Credit: @Qwer2077 (the owner of the agent is credited as the solver)

open OMA.S_oeis_a273676 PowerSeries

namespace OMA.Proof_oeis_a273676

-- ============================================================================
-- Section 1: Exact radial closed form for both Rule 833 and Rule 849
-- ============================================================================

private def f833 (t : ℕ) (x y : ℤ) : Bool :=
  let d := |x| + |y|
  if (t : ℤ) < d then true
  else if d = (t : ℤ) then false
  else decide ((d + (t : ℤ)) % 2 = 1)

private def isRuleA (rule : ℕ) : Prop := rule = 833 ∨ rule = 849

private lemma ruleA_eval {rule : ℕ} (hr : isRuleA rule) (cur : Bool) (s : ℕ) (hs : s ≤ 4) :
    (s = 0 → rule.testBit (cur.toNat + 2 * s) = !cur) ∧
    (s = 1 → rule.testBit (cur.toNat + 2 * s) = false) ∧
    (s = 2 → cur = true → rule.testBit (cur.toNat + 2 * s) = false) ∧
    (s = 3 → rule.testBit (cur.toNat + 2 * s) = !cur) ∧
    (s = 4 → rule.testBit (cur.toNat + 2 * s) = true) := by
  rcases hr with rfl | rfl <;> cases cur <;> interval_cases s <;> decide

private lemma stateA_one {rule : ℕ} (hr : isRuleA rule) (x y : ℤ) :
    state rule 1 x y = decide (2 ≤ |x| + |y|) := by
  have hstep : state rule 1 x y =
      rule.testBit ((state rule 0 x y).toNat +
        2 * ((state rule 0 (x - 1) y).toNat + (state rule 0 (x + 1) y).toNat +
             (state rule 0 x (y - 1)).toNat + (state rule 0 x (y + 1)).toNat)) := rfl
  rw [hstep]
  by_cases hgt : 2 ≤ |x| + |y|
  · have hC : state rule 0 x y = false := by
      simp only [state, decide_eq_false_iff_not]; rintro ⟨rfl, rfl⟩; simp at hgt
    have hW : state rule 0 (x - 1) y = false := by
      simp only [state, decide_eq_false_iff_not]; rintro ⟨h1, h2⟩
      simp only [abs_eq_max_neg] at hgt; omega
    have hE : state rule 0 (x + 1) y = false := by
      simp only [state, decide_eq_false_iff_not]; rintro ⟨h1, h2⟩
      simp only [abs_eq_max_neg] at hgt; omega
    have hS : state rule 0 x (y - 1) = false := by
      simp only [state, decide_eq_false_iff_not]; rintro ⟨h1, h2⟩
      simp only [abs_eq_max_neg] at hgt; omega
    have hN : state rule 0 x (y + 1) = false := by
      simp only [state, decide_eq_false_iff_not]; rintro ⟨h1, h2⟩
      simp only [abs_eq_max_neg] at hgt; omega
    rw [hC, hW, hE, hS, hN, show decide (2 ≤ |x| + |y|) = true by simp [hgt]]
    rcases hr with rfl | rfl <;> decide
  · have hx1 : -1 ≤ x := by simp only [abs_eq_max_neg] at hgt; omega
    have hx2 : x ≤ 1 := by simp only [abs_eq_max_neg] at hgt; omega
    have hy1 : -1 ≤ y := by simp only [abs_eq_max_neg] at hgt; omega
    have hy2 : y ≤ 1 := by simp only [abs_eq_max_neg] at hgt; omega
    rcases hr with rfl | rfl <;> (interval_cases x <;> interval_cases y <;> decide)

private lemma stateA_two {rule : ℕ} (hr : isRuleA rule) (x y : ℤ) :
    state rule 2 x y = decide (|x| + |y| ≠ 2) := by
  have hstep : state rule 2 x y =
      rule.testBit ((state rule 1 x y).toNat +
        2 * ((state rule 1 (x - 1) y).toNat + (state rule 1 (x + 1) y).toNat +
             (state rule 1 x (y - 1)).toNat + (state rule 1 x (y + 1)).toNat)) := rfl
  rw [hstep, stateA_one hr, stateA_one hr, stateA_one hr, stateA_one hr, stateA_one hr]
  by_cases hgt : 3 ≤ |x| + |y|
  · have hC : decide (2 ≤ |x| + |y|) = true := by rw [decide_eq_true_eq]; omega
    have hW : decide (2 ≤ |x - 1| + |y|) = true := by rw [decide_eq_true_eq]; simp only [abs_eq_max_neg] at hgt ⊢; omega
    have hE : decide (2 ≤ |x + 1| + |y|) = true := by rw [decide_eq_true_eq]; simp only [abs_eq_max_neg] at hgt ⊢; omega
    have hS : decide (2 ≤ |x| + |y - 1|) = true := by rw [decide_eq_true_eq]; simp only [abs_eq_max_neg] at hgt ⊢; omega
    have hN : decide (2 ≤ |x| + |y + 1|) = true := by rw [decide_eq_true_eq]; simp only [abs_eq_max_neg] at hgt ⊢; omega
    rw [hC, hW, hE, hS, hN, show decide (|x| + |y| ≠ 2) = true by rw [decide_eq_true_eq]; omega]
    rcases hr with rfl | rfl <;> decide
  · have hx1 : -2 ≤ x := by simp only [abs_eq_max_neg] at hgt; omega
    have hx2 : x ≤ 2 := by simp only [abs_eq_max_neg] at hgt; omega
    have hy1 : -2 ≤ y := by simp only [abs_eq_max_neg] at hgt; omega
    have hy2 : y ≤ 2 := by simp only [abs_eq_max_neg] at hgt; omega
    rcases hr with rfl | rfl <;> (interval_cases x <;> interval_cases y <;> decide)

private lemma stateA_three {rule : ℕ} (hr : isRuleA rule) (x y : ℤ) :
    state rule 3 x y = f833 3 x y := by
  have hstep : state rule 3 x y =
      rule.testBit ((state rule 2 x y).toNat +
        2 * ((state rule 2 (x - 1) y).toNat + (state rule 2 (x + 1) y).toNat +
             (state rule 2 x (y - 1)).toNat + (state rule 2 x (y + 1)).toNat)) := rfl
  rw [hstep, stateA_two hr, stateA_two hr, stateA_two hr, stateA_two hr, stateA_two hr]
  by_cases hgt : 4 ≤ |x| + |y|
  · have hC : decide (|x| + |y| ≠ 2) = true := by rw [decide_eq_true_eq]; omega
    have hW : decide (|x - 1| + |y| ≠ 2) = true := by rw [decide_eq_true_eq]; simp only [abs_eq_max_neg] at hgt ⊢; omega
    have hE : decide (|x + 1| + |y| ≠ 2) = true := by rw [decide_eq_true_eq]; simp only [abs_eq_max_neg] at hgt ⊢; omega
    have hS : decide (|x| + |y - 1| ≠ 2) = true := by rw [decide_eq_true_eq]; simp only [abs_eq_max_neg] at hgt ⊢; omega
    have hN : decide (|x| + |y + 1| ≠ 2) = true := by rw [decide_eq_true_eq]; simp only [abs_eq_max_neg] at hgt ⊢; omega
    rw [hC, hW, hE, hS, hN]
    unfold f833; dsimp only; rw [if_pos (by omega)]
    rcases hr with rfl | rfl <;> decide
  · have hx1 : -3 ≤ x := by simp only [abs_eq_max_neg] at hgt; omega
    have hx2 : x ≤ 3 := by simp only [abs_eq_max_neg] at hgt; omega
    have hy1 : -3 ≤ y := by simp only [abs_eq_max_neg] at hgt; omega
    have hy2 : y ≤ 3 := by simp only [abs_eq_max_neg] at hgt; omega
    rcases hr with rfl | rfl <;> (interval_cases x <;> interval_cases y <;> decide)

private lemma nbr_dist_bounds (x y : ℤ) :
    let d := |x| + |y|
    (|x - 1| + |y| = d + 1 ∨ |x - 1| + |y| = d - 1) ∧
    (|x + 1| + |y| = d + 1 ∨ |x + 1| + |y| = d - 1) ∧
    (|x| + |y - 1| = d + 1 ∨ |x| + |y - 1| = d - 1) ∧
    (|x| + |y + 1| = d + 1 ∨ |x| + |y + 1| = d - 1) := by
  dsimp only
  simp only [abs_eq_max_neg]
  refine ⟨by omega, by omega, by omega, by omega⟩

private lemma nbr_cnt_exact (x y : ℤ) (hd : 1 ≤ |x| + |y|) :
    let d := |x| + |y|
    let nPlus := (if |x - 1| + |y| = d + 1 then 1 else 0) +
                 (if |x + 1| + |y| = d + 1 then 1 else 0) +
                 (if |x| + |y - 1| = d + 1 then 1 else 0) +
                 (if |x| + |y + 1| = d + 1 then 1 else 0)
    let nMinus := (if |x - 1| + |y| = d - 1 then 1 else 0) +
                  (if |x + 1| + |y| = d - 1 then 1 else 0) +
                  (if |x| + |y - 1| = d - 1 then 1 else 0) +
                  (if |x| + |y + 1| = d - 1 then 1 else 0)
    (nPlus = 2 ∧ nMinus = 2) ∨ (nPlus = 3 ∧ nMinus = 1) := by
  dsimp only
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> rcases lt_trichotomy y 0 with hy | rfl | hy
  · left
    rw [abs_of_neg hx, abs_of_neg hy, abs_of_neg (by omega : x - 1 < 0),
        abs_of_nonpos (by omega : x + 1 ≤ 0), abs_of_neg (by omega : y - 1 < 0),
        abs_of_nonpos (by omega : y + 1 ≤ 0)]
    split_ifs <;> omega
  · right
    rw [abs_of_neg hx, abs_zero, abs_of_neg (by omega : x - 1 < 0),
        abs_of_nonpos (by omega : x + 1 ≤ 0)]
    norm_num; split_ifs <;> omega
  · left
    rw [abs_of_neg hx, abs_of_pos hy, abs_of_neg (by omega : x - 1 < 0),
        abs_of_nonpos (by omega : x + 1 ≤ 0), abs_of_nonneg (by omega : 0 ≤ y - 1),
        abs_of_pos (by omega : 0 < y + 1)]
    split_ifs <;> omega
  · right
    rw [abs_zero, abs_of_neg hy, abs_of_neg (by omega : y - 1 < 0),
        abs_of_nonpos (by omega : y + 1 ≤ 0)]
    norm_num; split_ifs <;> omega
  · simp at hd
  · right
    rw [abs_zero, abs_of_pos hy, abs_of_nonneg (by omega : 0 ≤ y - 1),
        abs_of_pos (by omega : 0 < y + 1)]
    norm_num; split_ifs <;> omega
  · left
    rw [abs_of_pos hx, abs_of_neg hy, abs_of_nonneg (by omega : 0 ≤ x - 1),
        abs_of_pos (by omega : 0 < x + 1), abs_of_neg (by omega : y - 1 < 0),
        abs_of_nonpos (by omega : y + 1 ≤ 0)]
    split_ifs <;> omega
  · right
    rw [abs_of_pos hx, abs_zero, abs_of_nonneg (by omega : 0 ≤ x - 1),
        abs_of_pos (by omega : 0 < x + 1)]
    norm_num; split_ifs <;> omega
  · left
    rw [abs_of_pos hx, abs_of_pos hy, abs_of_nonneg (by omega : 0 ≤ x - 1),
        abs_of_pos (by omega : 0 < x + 1), abs_of_nonneg (by omega : 0 ≤ y - 1),
        abs_of_pos (by omega : 0 < y + 1)]
    split_ifs <;> omega

private lemma f833_val_by_dist (t : ℕ) (x y : ℤ) (d : ℤ) (hd : |x| + |y| = d) :
    f833 t x y =
      if (t : ℤ) < d then true
      else if d = (t : ℤ) then false
      else decide ((d + (t : ℤ)) % 2 = 1) := by
  unfold f833; dsimp only; rw [hd]

private lemma f833_step {rule : ℕ} (hr : isRuleA rule) (t : ℕ) (ht : 3 ≤ t)
    (ih : ∀ x y : ℤ, state rule t x y = f833 t x y) (x y : ℤ) :
    state rule (t + 1) x y = f833 (t + 1) x y := by
  have hstep : state rule (t + 1) x y =
      rule.testBit ((state rule t x y).toNat +
        2 * ((state rule t (x - 1) y).toNat + (state rule t (x + 1) y).toNat +
             (state rule t x (y - 1)).toNat + (state rule t x (y + 1)).toNat)) := rfl
  rw [hstep, ih x y, ih (x - 1) y, ih (x + 1) y, ih x (y - 1), ih x (y + 1)]
  set d := |x| + |y| with hd_def
  have hd0 : 0 ≤ d := by positivity
  by_cases h0 : d = 0
  · have hx0 : x = 0 := by rw [hd_def] at h0; simp only [abs_eq_max_neg] at h0; omega
    have hy0 : y = 0 := by rw [hd_def] at h0; simp only [abs_eq_max_neg] at h0; omega
    subst hx0 hy0
    have hnbr : ∀ a b : ℤ, |a| + |b| = 1 → f833 t a b = decide ((1 + (t : ℤ)) % 2 = 1) := by
      intro a b hab
      rw [f833_val_by_dist t a b 1 hab, if_neg (by omega), if_neg (by omega)]
    have hC : f833 t 0 0 = decide ((0 + (t : ℤ)) % 2 = 1) := by
      rw [f833_val_by_dist t 0 0 0 (by simp), if_neg (by omega), if_neg (by omega)]
    have hT : f833 (t + 1) 0 0 = decide ((0 + ((t + 1 : ℕ) : ℤ)) % 2 = 1) := by
      rw [f833_val_by_dist (t + 1) 0 0 0 (by simp), if_neg (by push_cast; omega), if_neg (by push_cast; omega)]
    simp only [zero_add, zero_sub]
    rw [hC, hT, hnbr (-1) 0 (by simp), hnbr 1 0 (by simp), hnbr 0 (-1) (by simp), hnbr 0 1 (by simp)]
    by_cases hpar : (t : ℤ) % 2 = 1
    · have h1 : decide ((1 + (t : ℤ)) % 2 = 1) = false := by simp only [decide_eq_false_iff_not]; omega
      have h2 : decide ((0 + (t : ℤ)) % 2 = 1) = true := by simp only [decide_eq_true_eq]; omega
      have h3 : decide ((0 + ((t + 1 : ℕ) : ℤ)) % 2 = 1) = false := by
        simp only [decide_eq_false_iff_not]; push_cast; omega
      rw [h1, h2, h3]
      exact (ruleA_eval hr true 0 (by omega)).1 rfl
    · have h1 : decide ((1 + (t : ℤ)) % 2 = 1) = true := by simp only [decide_eq_true_eq]; omega
      have h2 : decide ((0 + (t : ℤ)) % 2 = 1) = false := by simp only [decide_eq_false_iff_not]; omega
      have h3 : decide ((0 + ((t + 1 : ℕ) : ℤ)) % 2 = 1) = true := by
        simp only [decide_eq_true_eq]; push_cast; omega
      rw [h1, h2, h3]
      exact (ruleA_eval hr false 4 (by omega)).2.2.2.2 rfl
  · have hd1 : 1 ≤ d := by omega
    obtain ⟨hb1, hb2, hb3, hb4⟩ := nbr_dist_bounds x y
    have hcnt := nbr_cnt_exact x y hd1
    set vPlus : Bool :=
      if (t : ℤ) < d + 1 then true
      else if d + 1 = (t : ℤ) then false
      else decide ((d + 1 + (t : ℤ)) % 2 = 1)
    set vMinus : Bool :=
      if (t : ℤ) < d - 1 then true
      else if d - 1 = (t : ℤ) then false
      else decide ((d - 1 + (t : ℤ)) % 2 = 1)
    have hval : ∀ a b : ℤ, (|a| + |b| = d + 1 ∨ |a| + |b| = d - 1) →
        (f833 t a b).toNat =
          (if |a| + |b| = d + 1 then 1 else 0) * vPlus.toNat +
          (if |a| + |b| = d - 1 then 1 else 0) * vMinus.toNat := by
      intro a b hab
      rcases hab with h | h
      · have hne : |a| + |b| ≠ d - 1 := by omega
        rw [if_pos h, if_neg hne, one_mul, zero_mul, add_zero]
        exact congrArg Bool.toNat (f833_val_by_dist t a b (d + 1) h)
      · have hne : |a| + |b| ≠ d + 1 := by omega
        rw [if_neg hne, if_pos h, zero_mul, one_mul, zero_add]
        exact congrArg Bool.toNat (f833_val_by_dist t a b (d - 1) h)
    have hs_eq : (f833 t (x - 1) y).toNat + (f833 t (x + 1) y).toNat +
        (f833 t x (y - 1)).toNat + (f833 t x (y + 1)).toNat =
        ((if |x - 1| + |y| = d + 1 then 1 else 0) + (if |x + 1| + |y| = d + 1 then 1 else 0) +
         (if |x| + |y - 1| = d + 1 then 1 else 0) + (if |x| + |y + 1| = d + 1 then 1 else 0)) * vPlus.toNat +
        ((if |x - 1| + |y| = d - 1 then 1 else 0) + (if |x + 1| + |y| = d - 1 then 1 else 0) +
         (if |x| + |y - 1| = d - 1 then 1 else 0) + (if |x| + |y + 1| = d - 1 then 1 else 0)) * vMinus.toNat := by
      rw [hval _ _ hb1, hval _ _ hb2, hval _ _ hb3, hval _ _ hb4]
      ring
    rw [hs_eq]
    set nP := (if |x - 1| + |y| = d + 1 then 1 else 0) + (if |x + 1| + |y| = d + 1 then 1 else 0) +
              (if |x| + |y - 1| = d + 1 then 1 else 0) + (if |x| + |y + 1| = d + 1 then 1 else 0)
    set nM := (if |x - 1| + |y| = d - 1 then 1 else 0) + (if |x + 1| + |y| = d - 1 then 1 else 0) +
              (if |x| + |y - 1| = d - 1 then 1 else 0) + (if |x| + |y + 1| = d - 1 then 1 else 0)
    have hcases : (nP = 2 ∧ nM = 2) ∨ (nP = 3 ∧ nM = 1) := hcnt
    by_cases hgt1 : (t : ℤ) + 1 < d
    · have hC : f833 t x y = true := by rw [f833_val_by_dist t x y d rfl, if_pos (by omega)]
      have hP : vPlus = true := by simp only [vPlus]; rw [if_pos (by omega)]
      have hM : vMinus = true := by simp only [vMinus]; rw [if_pos (by omega)]
      have hT : f833 (t + 1) x y = true := by
        rw [f833_val_by_dist (t + 1) x y d rfl, if_pos (by push_cast; omega)]
      rw [hC, hP, hM, hT]
      rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
        exact (ruleA_eval hr true 4 (by omega)).2.2.2.2 rfl
    · by_cases heq1 : d = (t : ℤ) + 1
      · have hC : f833 t x y = true := by rw [f833_val_by_dist t x y d rfl, if_pos (by omega)]
        have hP : vPlus = true := by simp only [vPlus]; rw [if_pos (by omega)]
        have hM : vMinus = false := by
          simp only [vMinus]; rw [if_neg (by omega), if_pos (by omega)]
        have hT : f833 (t + 1) x y = false := by
          rw [f833_val_by_dist (t + 1) x y d rfl, if_neg (by push_cast; omega), if_pos (by push_cast; omega)]
        rw [hC, hP, hM, hT]
        rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
        · exact (ruleA_eval hr true 2 (by omega)).2.2.1 rfl rfl
        · exact (ruleA_eval hr true 3 (by omega)).2.2.2.1 rfl
      · by_cases heq0 : d = (t : ℤ)
        · have hC : f833 t x y = false := by
            rw [f833_val_by_dist t x y d rfl, if_neg (by omega), if_pos (by omega)]
          have hP : vPlus = true := by simp only [vPlus]; rw [if_pos (by omega)]
          have hM : vMinus = true := by
            simp only [vMinus]; rw [if_neg (by omega), if_neg (by omega)]
            simp only [decide_eq_true_eq]; omega
          have hT : f833 (t + 1) x y = true := by
            rw [f833_val_by_dist (t + 1) x y d rfl, if_neg (by push_cast; omega), if_neg (by push_cast; omega)]
            simp only [decide_eq_true_eq]; push_cast; omega
          rw [hC, hP, hM, hT]
          rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
            exact (ruleA_eval hr false 4 (by omega)).2.2.2.2 rfl
        · -- d < t
          have hlt : d < (t : ℤ) := by omega
          have hC : f833 t x y = decide ((d + (t : ℤ)) % 2 = 1) := by
            rw [f833_val_by_dist t x y d rfl, if_neg (by omega), if_neg (by omega)]
          have hT : f833 (t + 1) x y = decide ((d + ((t + 1 : ℕ) : ℤ)) % 2 = 1) := by
            rw [f833_val_by_dist (t + 1) x y d rfl, if_neg (by push_cast; omega), if_neg (by push_cast; omega)]
          have hM : vMinus = decide ((d + (t : ℤ)) % 2 = 0) := by
            simp only [vMinus]; rw [if_neg (by omega), if_neg (by omega)]
            apply decide_eq_decide.mpr; omega
          have hP : vPlus = decide ((d + (t : ℤ)) % 2 = 0) := by
            simp only [vPlus]; rw [if_neg (by omega)]
            split_ifs with h1
            · symm; simp only [decide_eq_false_iff_not]; omega
            · apply decide_eq_decide.mpr; omega
          rw [hC, hP, hM, hT]
          by_cases hpar : (d + (t : ℤ)) % 2 = 1
          · have h1 : decide ((d + (t : ℤ)) % 2 = 0) = false := by simp only [decide_eq_false_iff_not]; omega
            have h2 : decide ((d + ((t + 1 : ℕ) : ℤ)) % 2 = 1) = false := by
              simp only [decide_eq_false_iff_not]; push_cast; omega
            rw [h1, h2]
            simp only [hpar, decide_true, Bool.toNat_false, mul_zero, add_zero]
            exact (ruleA_eval hr true 0 (by omega)).1 rfl
          · have h1 : decide ((d + (t : ℤ)) % 2 = 0) = true := by simp only [decide_eq_true_eq]; omega
            have h2 : decide ((d + ((t + 1 : ℕ) : ℤ)) % 2 = 1) = true := by
              simp only [decide_eq_true_eq]; push_cast; omega
            rw [h1, h2]
            simp only [hpar, decide_false, Bool.toNat_true, mul_one]
            rcases hcases with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rw [h3, h4] <;>
              exact (ruleA_eval hr false 4 (by omega)).2.2.2.2 rfl

private lemma stateA_eq_f833 {rule : ℕ} (hr : isRuleA rule) (t : ℕ) (ht : 3 ≤ t) (x y : ℤ) :
    state rule t x y = f833 t x y := by
  induction t generalizing x y with
  | zero => omega
  | succ t ih =>
    by_cases h2 : t = 2
    · subst h2; exact stateA_three hr x y
    · exact f833_step hr t (by omega) (ih (by omega)) x y

private lemma state_849_eq_833 (t : ℕ) (x y : ℤ) : state 849 t x y = state 833 t x y := by
  match t with
  | 0 => rfl
  | 1 => rw [stateA_one (Or.inr rfl), stateA_one (Or.inl rfl)]
  | 2 => rw [stateA_two (Or.inr rfl), stateA_two (Or.inl rfl)]
  | t + 3 => rw [stateA_eq_f833 (Or.inr rfl) (t + 3) (by omega), stateA_eq_f833 (Or.inl rfl) (t + 3) (by omega)]

private lemma count_849_eq (n : ℕ) : count 849 (2 ^ n - 1) = a n := by
  unfold a count
  congr 1; ext p; simp [state_849_eq_833]

-- ============================================================================
-- Section 2: Shell counting and closed form for a(n) = count 833 (2^n - 1)
-- ============================================================================

private noncomputable def box (B : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(B : ℤ)) (B : ℤ) ×ˢ Finset.Icc (-(B : ℤ)) (B : ℤ)

private lemma box_mem_iff (B : ℕ) (p : ℤ × ℤ) :
    p ∈ box B ↔ -(B : ℤ) ≤ p.1 ∧ p.1 ≤ (B : ℤ) ∧ -(B : ℤ) ≤ p.2 ∧ p.2 ≤ (B : ℤ) := by
  simp [box, Finset.mem_product, Finset.mem_Icc, and_assoc]

private lemma box_card (B : ℕ) : (box B).card = (2 * B + 1) * (2 * B + 1) := by
  rw [box, Finset.card_product, Int.card_Icc]
  have : ((B : ℤ) + 1 - -(B : ℤ)).toNat = 2 * B + 1 := by omega
  rw [this]

private lemma shell_card (B d : ℕ) (hd : 1 ≤ d) (hdB : d ≤ B) :
    ((box B).filter (fun p => |p.1| + |p.2| = (d : ℤ))).card = 4 * d := by
  rw [Finset.card_filter]
  have hsplit : (∑ p ∈ box B, if |p.1| + |p.2| = (d : ℤ) then 1 else 0) =
      (∑ p ∈ box B, if |p.1| + |p.2| = (d : ℤ) ∧ 0 < p.1 ∧ 0 ≤ p.2 then 1 else 0) +
      (∑ p ∈ box B, if |p.1| + |p.2| = (d : ℤ) ∧ p.1 ≤ 0 ∧ 0 < p.2 then 1 else 0) +
      (∑ p ∈ box B, if |p.1| + |p.2| = (d : ℤ) ∧ p.1 < 0 ∧ p.2 ≤ 0 then 1 else 0) +
      (∑ p ∈ box B, if |p.1| + |p.2| = (d : ℤ) ∧ 0 ≤ p.1 ∧ p.2 < 0 then 1 else 0) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : |p.1| + |p.2| = (d : ℤ)
    · have hne : p.1 ≠ 0 ∨ p.2 ≠ 0 := by simp only [abs_eq_max_neg] at h; omega
      split_ifs <;> omega
    · simp [h]
  have hq1 : (∑ p ∈ box B, if |p.1| + |p.2| = (d : ℤ) ∧ 0 < p.1 ∧ 0 ≤ p.2 then 1 else 0) = d := by
    rw [← Finset.sum_filter]
    have hc : (∑ _ ∈ Finset.range d, (1 : ℕ)) = d := by simp
    rw [← hc]
    refine Finset.sum_bij (fun p _ => p.2.toNat) ?_ ?_ ?_ ?_
    · intro p hp; rw [Finset.mem_filter] at hp; rw [Finset.mem_range]
      simp only [abs_eq_max_neg] at hp; omega
    · intro p1 hp1 p2 hp2 h; rw [Finset.mem_filter] at hp1 hp2
      have hy : p1.2 = p2.2 := by omega
      apply Prod.ext
      · simp only [abs_eq_max_neg] at hp1 hp2; omega
      · exact hy
    · intro k hk; rw [Finset.mem_range] at hk
      refine ⟨((d : ℤ) - k, k), ?_, by omega⟩
      rw [Finset.mem_filter, box_mem_iff]; simp only [abs_eq_max_neg]; omega
    · intro _ _; rfl
  have hq2 : (∑ p ∈ box B, if |p.1| + |p.2| = (d : ℤ) ∧ p.1 ≤ 0 ∧ 0 < p.2 then 1 else 0) = d := by
    rw [← Finset.sum_filter]
    have hc : (∑ _ ∈ Finset.range d, (1 : ℕ)) = d := by simp
    rw [← hc]
    refine Finset.sum_bij (fun p _ => (-p.1).toNat) ?_ ?_ ?_ ?_
    · intro p hp; rw [Finset.mem_filter] at hp; rw [Finset.mem_range]
      simp only [abs_eq_max_neg] at hp; omega
    · intro p1 hp1 p2 hp2 h; rw [Finset.mem_filter] at hp1 hp2
      have hx : p1.1 = p2.1 := by omega
      apply Prod.ext
      · exact hx
      · simp only [abs_eq_max_neg] at hp1 hp2; omega
    · intro k hk; rw [Finset.mem_range] at hk
      refine ⟨(-(k : ℤ), (d : ℤ) - k), ?_, by omega⟩
      rw [Finset.mem_filter, box_mem_iff]; simp only [abs_eq_max_neg]; omega
    · intro _ _; rfl
  have hq3 : (∑ p ∈ box B, if |p.1| + |p.2| = (d : ℤ) ∧ p.1 < 0 ∧ p.2 ≤ 0 then 1 else 0) = d := by
    rw [← Finset.sum_filter]
    have hc : (∑ _ ∈ Finset.range d, (1 : ℕ)) = d := by simp
    rw [← hc]
    refine Finset.sum_bij (fun p _ => (-p.2).toNat) ?_ ?_ ?_ ?_
    · intro p hp; rw [Finset.mem_filter] at hp; rw [Finset.mem_range]
      simp only [abs_eq_max_neg] at hp; omega
    · intro p1 hp1 p2 hp2 h; rw [Finset.mem_filter] at hp1 hp2
      have hy : p1.2 = p2.2 := by omega
      apply Prod.ext
      · simp only [abs_eq_max_neg] at hp1 hp2; omega
      · exact hy
    · intro k hk; rw [Finset.mem_range] at hk
      refine ⟨(-((d : ℤ) - k), -(k : ℤ)), ?_, by omega⟩
      rw [Finset.mem_filter, box_mem_iff]; simp only [abs_eq_max_neg]; omega
    · intro _ _; rfl
  have hq4 : (∑ p ∈ box B, if |p.1| + |p.2| = (d : ℤ) ∧ 0 ≤ p.1 ∧ p.2 < 0 then 1 else 0) = d := by
    rw [← Finset.sum_filter]
    have hc : (∑ _ ∈ Finset.range d, (1 : ℕ)) = d := by simp
    rw [← hc]
    refine Finset.sum_bij (fun p _ => p.1.toNat) ?_ ?_ ?_ ?_
    · intro p hp; rw [Finset.mem_filter] at hp; rw [Finset.mem_range]
      simp only [abs_eq_max_neg] at hp; omega
    · intro p1 hp1 p2 hp2 h; rw [Finset.mem_filter] at hp1 hp2
      have hx : p1.1 = p2.1 := by omega
      apply Prod.ext
      · exact hx
      · simp only [abs_eq_max_neg] at hp1 hp2; omega
    · intro k hk; rw [Finset.mem_range] at hk
      refine ⟨(k, -((d : ℤ) - k)), ?_, by omega⟩
      rw [Finset.mem_filter, box_mem_iff]; simp only [abs_eq_max_neg]; omega
    · intro _ _; rfl
  rw [hsplit, hq1, hq2, hq3, hq4]
  omega

private lemma odd_shells_card (B k : ℕ) (hk : 2 * k + 1 ≤ B) :
    ((box B).filter (fun p => |p.1| + |p.2| ≤ (2 * k + 1 : ℤ) ∧ (|p.1| + |p.2|) % 2 = 1)).card =
      4 * (k + 1) * (k + 1) := by
  induction k with
  | zero =>
    have hEq : (box B).filter (fun p => |p.1| + |p.2| ≤ (1 : ℤ) ∧ (|p.1| + |p.2|) % 2 = 1) =
        (box B).filter (fun p => |p.1| + |p.2| = (1 : ℤ)) := by
      ext p
      have h1 : 0 ≤ |p.1| := abs_nonneg p.1
      have h2 : 0 ≤ |p.2| := abs_nonneg p.2
      simp only [Finset.mem_filter]; constructor
      · rintro ⟨hp, hle, hpar⟩; exact ⟨hp, by omega⟩
      · rintro ⟨hp, heq⟩; exact ⟨hp, by omega, by omega⟩
    simpa [hEq] using shell_card B 1 (by omega) (by omega)
  | succ k ih =>
    have hsplit : (box B).filter (fun p => |p.1| + |p.2| ≤ (2 * (k + 1 : ℕ) + 1 : ℤ) ∧ (|p.1| + |p.2|) % 2 = 1) =
        (box B).filter (fun p => |p.1| + |p.2| ≤ (2 * k + 1 : ℤ) ∧ (|p.1| + |p.2|) % 2 = 1) ∪
        (box B).filter (fun p => |p.1| + |p.2| = (2 * (k + 1) + 1 : ℤ)) := by
      ext p; simp only [Finset.mem_union, Finset.mem_filter]; constructor
      · rintro ⟨hp, hle, hpar⟩
        by_cases h : |p.1| + |p.2| ≤ (2 * k + 1 : ℤ)
        · left; exact ⟨hp, h, hpar⟩
        · right; exact ⟨hp, by omega⟩
      · rintro (⟨hp, hle, hpar⟩ | ⟨hp, heq⟩)
        · exact ⟨hp, by omega, hpar⟩
        · exact ⟨hp, by omega, by omega⟩
    have hdisj : Disjoint
        ((box B).filter (fun p => |p.1| + |p.2| ≤ (2 * k + 1 : ℤ) ∧ (|p.1| + |p.2|) % 2 = 1))
        ((box B).filter (fun p => |p.1| + |p.2| = (2 * (k + 1) + 1 : ℤ))) := by
      rw [Finset.disjoint_filter]; intro p _ h1 h2; omega
    rw [hsplit, Finset.card_union_of_disjoint hdisj, ih (by omega)]
    have hs := shell_card B (2 * (k + 1) + 1) (by omega) (by omega)
    rw [show ((2 * (k + 1) + 1 : ℕ) : ℤ) = (2 * (k + 1) + 1 : ℤ) by push_cast; rfl] at hs
    rw [hs]
    ring

private lemma count_833_odd (m : ℕ) (hm : 1 ≤ m) :
    count 833 (2 * m + 1) = 12 * m * m + 16 * m + 5 := by
  set t := 2 * m + 1
  have ht3 : 3 ≤ t := by omega
  unfold count
  change ((box t).filter (fun p => state 833 t p.1 p.2 = true)).card = _
  have hcomp : ((box t).filter (fun p => state 833 t p.1 p.2 = true)).card +
      ((box t).filter (fun p => state 833 t p.1 p.2 = false)).card = (box t).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext p; simp only [Finset.mem_union, Finset.mem_filter]
      cases state 833 t p.1 p.2 <;> simp
    · rw [Finset.disjoint_filter]; intro p _ h1 h2; rw [h1] at h2; cases h2
  have hfalse : (box t).filter (fun p => state 833 t p.1 p.2 = false) =
      (box t).filter (fun p => |p.1| + |p.2| ≤ (2 * m + 1 : ℤ) ∧ (|p.1| + |p.2|) % 2 = 1) := by
    ext p
    simp only [Finset.mem_filter, stateA_eq_f833 (Or.inl rfl) t ht3]
    constructor
    · rintro ⟨hp, hf⟩
      unfold f833 at hf; dsimp only at hf
      by_cases h1 : (t : ℤ) < |p.1| + |p.2|
      · rw [if_pos h1] at hf; cases hf
      · rw [if_neg h1] at hf
        by_cases h2 : |p.1| + |p.2| = (t : ℤ)
        · exact ⟨hp, by omega, by omega⟩
        · rw [if_neg h2] at hf
          simp only [decide_eq_false_iff_not] at hf
          exact ⟨hp, by omega, by omega⟩
    · rintro ⟨hp, hle, hpar⟩
      refine ⟨hp, ?_⟩
      unfold f833; dsimp only
      by_cases h1 : (t : ℤ) < |p.1| + |p.2|
      · omega
      · rw [if_neg h1]
        by_cases h2 : |p.1| + |p.2| = (t : ℤ)
        · rw [if_pos h2]
        · rw [if_neg h2]; simp only [decide_eq_false_iff_not]; omega
  have hbc : (box t).card = (4 * m + 3) * (4 * m + 3) := by
    rw [box_card]; congr 1 <;> omega
  rw [hfalse, odd_shells_card t m (by omega), hbc] at hcomp
  nlinarith

private lemma a_0 : a 0 = 1 := by
  unfold a count
  have h0 : 2 ^ 0 - 1 = 0 := rfl
  rw [h0]
  have : ((Finset.Icc (-(0 : ℕ) : ℤ) (0 : ℕ) ×ˢ Finset.Icc (-(0 : ℕ) : ℤ) (0 : ℕ)).filter
      (fun p => state 833 0 p.1 p.2 = true)) = {(0, 0)} := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton,
      Prod.mk.injEq, Nat.cast_zero, neg_zero]
    constructor
    · rintro ⟨⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩, _⟩; exact ⟨by omega, by omega⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨⟨⟨le_rfl, le_rfl⟩, ⟨le_rfl, le_rfl⟩⟩, by decide⟩
  rw [this]; rfl

private lemma a_1 : a 1 = 4 := by
  unfold a count
  have h1 : 2 ^ 1 - 1 = 1 := rfl
  rw [h1]
  change ((box 1).filter (fun p => state 833 1 p.1 p.2 = true)).card = 4
  have hcomp : ((box 1).filter (fun p => state 833 1 p.1 p.2 = true)).card +
      ((box 1).filter (fun p => state 833 1 p.1 p.2 = false)).card = (box 1).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext p; simp only [Finset.mem_union, Finset.mem_filter]
      cases state 833 1 p.1 p.2 <;> simp
    · rw [Finset.disjoint_filter]; intro p _ h1' h2'; rw [h1'] at h2'; cases h2'
  have hfalse : (box 1).filter (fun p => state 833 1 p.1 p.2 = false) =
      {(0, 0)} ∪ (box 1).filter (fun p => |p.1| + |p.2| = (1 : ℤ)) := by
    ext ⟨x, y⟩
    have hax : 0 ≤ |x| := abs_nonneg x
    have hay : 0 ≤ |y| := abs_nonneg y
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_singleton, Prod.mk.injEq,
      stateA_one (Or.inl rfl), decide_eq_false_iff_not, not_le]
    constructor
    · rintro ⟨hp, hlt⟩
      by_cases h0 : |x| + |y| = 0
      · left; simp only [abs_eq_max_neg] at h0; omega
      · right; exact ⟨hp, by omega⟩
    · rintro (⟨rfl, rfl⟩ | ⟨hp, heq⟩)
      · refine ⟨?_, by simp⟩; rw [box_mem_iff]; omega
      · exact ⟨hp, by omega⟩
  have hdisj : Disjoint ({((0 : ℤ), (0 : ℤ))} : Finset (ℤ × ℤ))
      ((box 1).filter (fun p => |p.1| + |p.2| = (1 : ℤ))) := by
    rw [Finset.disjoint_singleton_left, Finset.mem_filter]; simp
  have hs := shell_card 1 1 le_rfl le_rfl
  norm_num at hs
  rw [hfalse, Finset.card_union_of_disjoint hdisj, Finset.card_singleton, hs, box_card 1] at hcomp
  omega

private lemma a_closed (n : ℕ) (hn : 1 < n) :
    (a n : ℤ) = 3 * 4 ^ n - 4 * 2 ^ n + 1 := by
  set m := 2 ^ (n - 1) - 1
  have hm1 : 1 ≤ m := by
    have : 2 ^ 1 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    simp at this; omega
  have hpow2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ']
  have h2n : 2 ^ n - 1 = 2 * m + 1 := by omega
  have ha : a n = 12 * m * m + 16 * m + 5 := by
    unfold a; rw [h2n]; exact count_833_odd m hm1
  have haz : (a n : ℤ) = 12 * (m : ℤ) * (m : ℤ) + 16 * (m : ℤ) + 5 := by
    exact_mod_cast ha
  have hm_z : 2 * ((m : ℤ) + 1) = (2 : ℤ) ^ n := by
    have hpow : 2 * (m + 1) = 2 ^ n := by
      have : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by omega)
      omega
    exact_mod_cast hpow
  have h4n : (4 : ℤ) ^ n = ((2 : ℤ) ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [haz, h4n, ← hm_z]
  ring

private lemma a_rec (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3) := by
  rw [a_closed n (by omega), a_closed (n - 1) (by omega),
      a_closed (n - 2) (by omega), a_closed (n - 3) (by omega)]
  have h4a : (4 : ℤ) ^ n = 64 * (4 : ℤ) ^ (n - 3) := by
    conv_lhs => rw [show n = (n - 3) + 3 by omega]
    rw [pow_add]; ring
  have h4b : (4 : ℤ) ^ (n - 1) = 16 * (4 : ℤ) ^ (n - 3) := by
    conv_lhs => rw [show n - 1 = (n - 3) + 2 by omega]
    rw [pow_add]; ring
  have h4c : (4 : ℤ) ^ (n - 2) = 4 * (4 : ℤ) ^ (n - 3) := by
    conv_lhs => rw [show n - 2 = (n - 3) + 1 by omega]
    rw [pow_succ']
  have h2a : (2 : ℤ) ^ n = 8 * (2 : ℤ) ^ (n - 3) := by
    conv_lhs => rw [show n = (n - 3) + 3 by omega]
    rw [pow_add]; ring
  have h2b : (2 : ℤ) ^ (n - 1) = 4 * (2 : ℤ) ^ (n - 3) := by
    conv_lhs => rw [show n - 1 = (n - 3) + 2 by omega]
    rw [pow_add]; ring
  have h2c : (2 : ℤ) ^ (n - 2) = 2 * (2 : ℤ) ^ (n - 3) := by
    conv_lhs => rw [show n - 2 = (n - 3) + 1 by omega]
    rw [pow_succ']
  rw [h4a, h4b, h4c, h2a, h2b, h2c]
  ring

private lemma gf_eq :
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
      1 - 3 * X + 19 * X ^ 2 - 22 * X ^ 3 + 8 * X ^ 4 := by
  set A : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ))
  have hlhs : A * ((1 - X) * (1 - 2 * X) * (1 - 4 * X) : PowerSeries ℤ) =
      A - PowerSeries.C (7 : ℤ) * (A * X ^ 1) +
        PowerSeries.C (14 : ℤ) * (A * X ^ 2) - PowerSeries.C (8 : ℤ) * (A * X ^ 3) := by
    simp only [map_ofNat, pow_one]
    ring
  have hrhs : (1 - 3 * X + 19 * X ^ 2 - 22 * X ^ 3 + 8 * X ^ 4 : PowerSeries ℤ) =
      PowerSeries.C (1 : ℤ) - PowerSeries.C (3 : ℤ) * X +
        PowerSeries.C (19 : ℤ) * X ^ 2 - PowerSeries.C (22 : ℤ) * X ^ 3 +
        PowerSeries.C (8 : ℤ) * X ^ 4 := by
    simp only [map_one, map_ofNat]
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_C, PowerSeries.coeff_X, PowerSeries.coeff_mk, A]
  by_cases hn : 5 ≤ n
  · have hrec := a_rec n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n - 2 ≠ 0 by omega,
      show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega, ite_true, ite_false]
    linarith
  · have h0 : (a 0 : ℤ) = 1 := by exact_mod_cast a_0
    have h1 : (a 1 : ℤ) = 4 := by exact_mod_cast a_1
    have h2 : (a 2 : ℤ) = 33 := by rw [a_closed 2 (by omega)]; norm_num
    have h3 : (a 3 : ℤ) = 161 := by rw [a_closed 3 (by omega)]; norm_num
    have h4 : (a 4 : ℤ) = 705 := by rw [a_closed 4 (by omega)]; norm_num
    have hsub21 : (2 - 1 : ℕ) = 1 := rfl
    have hsub31 : (3 - 1 : ℕ) = 2 := rfl
    have hsub41 : (4 - 1 : ℕ) = 3 := rfl
    interval_cases n <;>
      simp only [Nat.sub_self, hsub21, hsub31, hsub41, h0, h1, h2, h3, h4] <;>
      norm_num

-- ============================================================================
-- Section 3: Exact 2^k self-similarity of Rule 131 agreeing with f833 at 2^n - 1
-- ============================================================================

private abbrev c1 (t : ℕ) (x y : ℤ) : Bool := state 131 t x y

private def rule131 (cur : Bool) (s : ℕ) : Bool :=
  (131 : ℕ).testBit (cur.toNat + 2 * s)

private lemma c1_succ (t : ℕ) (x y : ℤ) :
    c1 (t + 1) x y =
      rule131 (c1 t x y)
        ((c1 t (x - 1) y).toNat + (c1 t (x + 1) y).toNat +
         (c1 t x (y - 1)).toNat + (c1 t x (y + 1)).toNat) :=
  rfl

private lemma rule131_diag_symm (cur e n : Bool) :
    rule131 cur (e.toNat + n.toNat) = rule131 cur (n.toNat + e.toNat + e.toNat + n.toNat) := by
  cases cur <;> cases e <;> cases n <;> decide

private lemma rule131_false_pos (s : ℕ) (h1 : 1 ≤ s) (h2 : s ≤ 4) :
    rule131 false s = false := by
  interval_cases s <;> decide

private lemma c1_neg_x (t : ℕ) (x y : ℤ) : c1 t (-x) y = c1 t x y := by
  induction t generalizing x y with
  | zero => simp [c1, state]
  | succ t ih =>
    rw [c1_succ, c1_succ]
    have h1 : -x - 1 = -(x + 1) := by ring
    have h2 : -x + 1 = -(x - 1) := by ring
    rw [h1, h2, ih x y, ih (x + 1) y, ih (x - 1) y, ih x (y - 1), ih x (y + 1)]
    congr 1; omega

private lemma c1_neg_y (t : ℕ) (x y : ℤ) : c1 t x (-y) = c1 t x y := by
  induction t generalizing x y with
  | zero => simp [c1, state]
  | succ t ih =>
    rw [c1_succ, c1_succ]
    have h1 : -y - 1 = -(y + 1) := by ring
    have h2 : -y + 1 = -(y - 1) := by ring
    rw [h1, h2, ih x y, ih (x - 1) y, ih (x + 1) y, ih x (y + 1), ih x (y - 1)]
    congr 1; omega

private lemma c1_swap (t : ℕ) (x y : ℤ) : c1 t y x = c1 t x y := by
  induction t generalizing x y with
  | zero =>
    simp only [c1, state]
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]
  | succ t ih =>
    rw [c1_succ, c1_succ]
    rw [ih x y, ih (x - 1) y, ih (x + 1) y, ih x (y - 1), ih x (y + 1)]
    congr 1; omega

private lemma c1_abs (t : ℕ) (x y : ℤ) : c1 t |x| |y| = c1 t x y := by
  rcases le_or_gt 0 x with hx | hx <;> rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hx, abs_of_nonneg hy]
  · rw [abs_of_nonneg hx, abs_of_neg hy, c1_neg_y]
  · rw [abs_of_neg hx, abs_of_nonneg hy, c1_neg_x]
  · rw [abs_of_neg hx, abs_of_neg hy, c1_neg_x, c1_neg_y]

private lemma c1_outside (t : ℕ) (x y : ℤ) (h : (t : ℤ) < |x| + |y|) :
    c1 t x y = decide (t % 2 = 1) := by
  induction t generalizing x y with
  | zero =>
    simp only [c1, state]
    have : ¬ (x = 0 ∧ y = 0) := by rintro ⟨rfl, rfl⟩; simp at h
    simp [this]
  | succ t ih =>
    rw [c1_succ]
    have hC := ih x y (by omega)
    have hW := ih (x - 1) y (by simp only [abs_eq_max_neg] at h ⊢; omega)
    have hE := ih (x + 1) y (by simp only [abs_eq_max_neg] at h ⊢; omega)
    have hS := ih x (y - 1) (by simp only [abs_eq_max_neg] at h ⊢; omega)
    have hN := ih x (y + 1) (by simp only [abs_eq_max_neg] at h ⊢; omega)
    rw [hC, hW, hE, hS, hN]
    by_cases hp : t % 2 = 1
    · have hp' : (t + 1) % 2 ≠ 1 := by omega
      simp [hp, hp']; decide
    · have hp' : (t + 1) % 2 = 1 := by omega
      simp [hp, hp']; decide

private lemma abs_add_abs_mod2 (a b : ℤ) : (|a| + |b|) % 2 = (a + b) % 2 := by
  rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb]
  · rw [abs_of_nonneg ha, abs_of_neg hb]; omega
  · rw [abs_of_neg ha, abs_of_nonneg hb]; omega
  · rw [abs_of_neg ha, abs_of_neg hb]; omega

private def stagePow2 (M : ℕ) (x y : ℤ) : Bool :=
  if |x| + |y| < (M : ℤ) then decide ((|x| + |y|) % 2 = 0)
  else decide ((|x| = (M : ℤ) ∧ y = 0) ∨ (x = 0 ∧ |y| = (M : ℤ)))

private def decomp131 (M r : ℕ) (x y : ℤ) : Bool :=
  if |x| + |y| < (M : ℤ) then decide ((|x| + |y|) % 2 = 0)
  else if |x| = |y| then decide (r % 2 = 1)
  else if |y| < x then c1 r (x - (M : ℤ)) y
  else if |y| < -x then c1 r (x + (M : ℤ)) y
  else if |x| < y then c1 r x (y - (M : ℤ))
  else c1 r x (y + (M : ℤ))

private lemma decomp131_neg_x (M r : ℕ) (x y : ℤ) :
    decomp131 M r (-x) y = decomp131 M r x y := by
  unfold decomp131
  simp only [abs_neg, neg_neg]
  split_ifs
  all_goals try rfl
  all_goals try (simp only [abs_eq_max_neg] at *; omega)
  · rw [show -x - (M : ℤ) = -(x + (M : ℤ)) by ring, c1_neg_x]
  · rw [show -x + (M : ℤ) = -(x - (M : ℤ)) by ring, c1_neg_x]
  · rw [c1_neg_x]
  · rw [c1_neg_x]

private lemma decomp131_neg_y (M r : ℕ) (x y : ℤ) :
    decomp131 M r x (-y) = decomp131 M r x y := by
  unfold decomp131
  simp only [abs_neg]
  split_ifs
  all_goals try rfl
  all_goals try (simp only [abs_eq_max_neg] at *; omega)
  · rw [c1_neg_y]
  · rw [c1_neg_y]
  · rw [show -y - (M : ℤ) = -(y + (M : ℤ)) by ring, c1_neg_y]
  · rw [show -y + (M : ℤ) = -(y - (M : ℤ)) by ring, c1_neg_y]

private lemma decomp131_swap (M r : ℕ) (x y : ℤ) :
    decomp131 M r y x = decomp131 M r x y := by
  unfold decomp131
  simp only [add_comm |y| |x|]
  split_ifs
  all_goals try rfl
  all_goals try (simp only [abs_eq_max_neg] at *; omega)
  · rw [c1_swap]
  · rw [c1_swap]
  · rw [c1_swap]
  · rw [c1_swap]

private lemma decomp131_inner (M r : ℕ) (x y : ℤ) (h : |x| + |y| < (M : ℤ)) :
    decomp131 M r x y = decide ((|x| + |y|) % 2 = 0) := by
  unfold decomp131; rw [if_pos h]

private lemma decomp131_diag (M r : ℕ) (x y : ℤ) (hs : (M : ℤ) ≤ |x| + |y|) (heq : |x| = |y|) :
    decomp131 M r x y = decide (r % 2 = 1) := by
  unfold decomp131; rw [if_neg (by omega), if_pos heq]

private lemma decomp131_east (M r : ℕ) (x y : ℤ) (hs : (M : ℤ) ≤ |x| + |y|) (he : |y| < x) :
    decomp131 M r x y = c1 r (x - (M : ℤ)) y := by
  unfold decomp131
  rw [if_neg (by omega), if_neg (by simp only [abs_eq_max_neg] at he ⊢; omega), if_pos he]

private lemma decomp131_zero (M : ℕ) (hM : 2 ≤ M) (x y : ℤ) :
    decomp131 M 0 x y = stagePow2 M x y := by
  unfold decomp131 stagePow2
  split_ifs with h1 h2 h3 h4 h5
  · rfl
  · apply decide_eq_decide.mpr
    simp only [false_iff, not_or]
    constructor
    · rintro ⟨ha, rfl⟩; simp only [abs_zero] at h2; omega
    · rintro ⟨rfl, hb⟩; simp only [abs_zero] at h2; omega
  · simp only [c1, state]; apply decide_eq_decide.mpr
    constructor
    · rintro ⟨hx, hy⟩; left; exact ⟨by simp only [abs_eq_max_neg] at *; omega, hy⟩
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩) <;> (simp only [abs_eq_max_neg] at *; omega)
  · simp only [c1, state]; apply decide_eq_decide.mpr
    constructor
    · rintro ⟨hx, hy⟩; left; exact ⟨by simp only [abs_eq_max_neg] at *; omega, hy⟩
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩) <;> (simp only [abs_eq_max_neg] at *; omega)
  · simp only [c1, state]; apply decide_eq_decide.mpr
    constructor
    · rintro ⟨hx, hy⟩; right; exact ⟨hx, by simp only [abs_eq_max_neg] at *; omega⟩
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩) <;> (simp only [abs_eq_max_neg] at *; omega)
  · simp only [c1, state]; apply decide_eq_decide.mpr
    constructor
    · rintro ⟨hx, hy⟩; right; exact ⟨hx, by simp only [abs_eq_max_neg] at *; omega⟩
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩) <;> (simp only [abs_eq_max_neg] at *; omega)

private lemma nbr_nP_axis (x y : ℤ) (hd : 1 ≤ |x| + |y|) (haxis : x = 0 ∨ y = 0) :
    (if |x - 1| + |y| = |x| + |y| + 1 then 1 else 0) +
    (if |x + 1| + |y| = |x| + |y| + 1 then 1 else 0) +
    (if |x| + |y - 1| = |x| + |y| + 1 then 1 else 0) +
    (if |x| + |y + 1| = |x| + |y| + 1 then 1 else 0) = 3 := by
  rcases haxis with rfl | rfl
  · rcases lt_trichotomy y 0 with hy | rfl | hy
    · rw [abs_zero, abs_of_neg hy, abs_of_neg (by omega : y - 1 < 0),
          abs_of_nonpos (by omega : y + 1 ≤ 0)]
      norm_num; split_ifs <;> omega
    · simp at hd
    · rw [abs_zero, abs_of_pos hy, abs_of_nonneg (by omega : 0 ≤ y - 1),
          abs_of_pos (by omega : 0 < y + 1)]
      norm_num; split_ifs <;> omega
  · rcases lt_trichotomy x 0 with hx | rfl | hx
    · rw [abs_of_neg hx, abs_zero, abs_of_neg (by omega : x - 1 < 0),
          abs_of_nonpos (by omega : x + 1 ≤ 0)]
      norm_num; split_ifs <;> omega
    · simp at hd
    · rw [abs_of_pos hx, abs_zero, abs_of_nonneg (by omega : 0 ≤ x - 1),
          abs_of_pos (by omega : 0 < x + 1)]
      norm_num; split_ifs <;> omega

private lemma nbr_nP_off_axis (x y : ℤ) (hxne : x ≠ 0) (hyne : y ≠ 0) :
    (if |x - 1| + |y| = |x| + |y| + 1 then 1 else 0) +
    (if |x + 1| + |y| = |x| + |y| + 1 then 1 else 0) +
    (if |x| + |y - 1| = |x| + |y| + 1 then 1 else 0) +
    (if |x| + |y + 1| = |x| + |y| + 1 then 1 else 0) = 2 := by
  rcases lt_or_gt_of_ne hxne with hx | hx <;> rcases lt_or_gt_of_ne hyne with hy | hy
  · rw [abs_of_neg hx, abs_of_neg hy, abs_of_neg (by omega : x - 1 < 0),
        abs_of_nonpos (by omega : x + 1 ≤ 0), abs_of_neg (by omega : y - 1 < 0),
        abs_of_nonpos (by omega : y + 1 ≤ 0)]
    split_ifs <;> omega
  · rw [abs_of_neg hx, abs_of_pos hy, abs_of_neg (by omega : x - 1 < 0),
        abs_of_nonpos (by omega : x + 1 ≤ 0), abs_of_nonneg (by omega : 0 ≤ y - 1),
        abs_of_pos (by omega : 0 < y + 1)]
    split_ifs <;> omega
  · rw [abs_of_pos hx, abs_of_neg hy, abs_of_nonneg (by omega : 0 ≤ x - 1),
        abs_of_pos (by omega : 0 < x + 1), abs_of_neg (by omega : y - 1 < 0),
        abs_of_nonpos (by omega : y + 1 ≤ 0)]
    split_ifs <;> omega
  · rw [abs_of_pos hx, abs_of_pos hy, abs_of_nonneg (by omega : 0 ≤ x - 1),
        abs_of_pos (by omega : 0 < x + 1), abs_of_nonneg (by omega : 0 ≤ y - 1),
        abs_of_pos (by omega : 0 < y + 1)]
    split_ifs <;> omega

private lemma c1_f833_to_stagePow2 (M : ℕ) (hM : 4 ≤ M) (hMeven : M % 2 = 0)
    (hprev : ∀ x y : ℤ, c1 (M - 1) x y = f833 (M - 1) x y) (x y : ℤ) :
    c1 M x y = stagePow2 M x y := by
  rw [show M = (M - 1) + 1 by omega, c1_succ]
  rw [hprev x y, hprev (x - 1) y, hprev (x + 1) y, hprev x (y - 1), hprev x (y + 1)]
  set t := M - 1
  set d := |x| + |y| with hd_def
  have hd0 : 0 ≤ d := by positivity
  by_cases h0 : d = 0
  · have hx0 : x = 0 := by rw [hd_def] at h0; simp only [abs_eq_max_neg] at h0; omega
    have hy0 : y = 0 := by rw [hd_def] at h0; simp only [abs_eq_max_neg] at h0; omega
    subst hx0 hy0
    have hnbr : ∀ a b : ℤ, |a| + |b| = 1 → f833 t a b = false := by
      intro a b hab
      rw [f833_val_by_dist t a b 1 hab, if_neg (by omega), if_neg (by omega)]
      simp only [decide_eq_false_iff_not]; omega
    simp only [zero_add, zero_sub]
    rw [hnbr (-1) 0 (by simp), hnbr 1 0 (by simp), hnbr 0 (-1) (by simp), hnbr 0 1 (by simp)]
    have hT : stagePow2 (t + 1) 0 0 = true := by unfold stagePow2; simp
    rw [hT]; cases f833 t 0 0 <;> decide
  · have hd1 : 1 ≤ d := by omega
    obtain ⟨hb1, hb2, hb3, hb4⟩ := nbr_dist_bounds x y
    have hcnt := nbr_cnt_exact x y hd1
    set vPlus : Bool :=
      if (t : ℤ) < d + 1 then true
      else if d + 1 = (t : ℤ) then false
      else decide ((d + 1 + (t : ℤ)) % 2 = 1)
    set vMinus : Bool :=
      if (t : ℤ) < d - 1 then true
      else if d - 1 = (t : ℤ) then false
      else decide ((d - 1 + (t : ℤ)) % 2 = 1)
    have hval : ∀ a b : ℤ, (|a| + |b| = d + 1 ∨ |a| + |b| = d - 1) →
        (f833 t a b).toNat =
          (if |a| + |b| = d + 1 then 1 else 0) * vPlus.toNat +
          (if |a| + |b| = d - 1 then 1 else 0) * vMinus.toNat := by
      intro a b hab
      rcases hab with h | h
      · have hne : |a| + |b| ≠ d - 1 := by omega
        rw [if_pos h, if_neg hne, one_mul, zero_mul, add_zero]
        exact congrArg Bool.toNat (f833_val_by_dist t a b (d + 1) h)
      · have hne : |a| + |b| ≠ d + 1 := by omega
        rw [if_neg hne, if_pos h, zero_mul, one_mul, zero_add]
        exact congrArg Bool.toNat (f833_val_by_dist t a b (d - 1) h)
    have hs_eq : (f833 t (x - 1) y).toNat + (f833 t (x + 1) y).toNat +
        (f833 t x (y - 1)).toNat + (f833 t x (y + 1)).toNat =
        ((if |x - 1| + |y| = d + 1 then 1 else 0) + (if |x + 1| + |y| = d + 1 then 1 else 0) +
         (if |x| + |y - 1| = d + 1 then 1 else 0) + (if |x| + |y + 1| = d + 1 then 1 else 0)) * vPlus.toNat +
        ((if |x - 1| + |y| = d - 1 then 1 else 0) + (if |x + 1| + |y| = d - 1 then 1 else 0) +
         (if |x| + |y - 1| = d - 1 then 1 else 0) + (if |x| + |y + 1| = d - 1 then 1 else 0)) * vMinus.toNat := by
      rw [hval _ _ hb1, hval _ _ hb2, hval _ _ hb3, hval _ _ hb4]
      ring
    rw [hs_eq]
    set nP := (if |x - 1| + |y| = d + 1 then 1 else 0) + (if |x + 1| + |y| = d + 1 then 1 else 0) +
              (if |x| + |y - 1| = d + 1 then 1 else 0) + (if |x| + |y + 1| = d + 1 then 1 else 0)
    set nM := (if |x - 1| + |y| = d - 1 then 1 else 0) + (if |x + 1| + |y| = d - 1 then 1 else 0) +
              (if |x| + |y - 1| = d - 1 then 1 else 0) + (if |x| + |y + 1| = d - 1 then 1 else 0)
    have hcases : (nP = 2 ∧ nM = 2) ∨ (nP = 3 ∧ nM = 1) := hcnt
    by_cases hgt1 : (t : ℤ) + 1 < d
    · have hC : f833 t x y = true := by rw [f833_val_by_dist t x y d rfl, if_pos (by omega)]
      have hP : vPlus = true := by simp only [vPlus]; rw [if_pos (by omega)]
      have hM : vMinus = true := by simp only [vMinus]; rw [if_pos (by omega)]
      have hT : stagePow2 (t + 1) x y = false := by
        unfold stagePow2; rw [if_neg (by push_cast; omega)]
        simp only [decide_eq_false_iff_not, not_or]
        constructor
        · rintro ⟨ha, rfl⟩; simp only [abs_zero, add_zero] at hd_def; push_cast at ha; omega
        · rintro ⟨rfl, hb⟩; simp only [abs_zero, zero_add] at hd_def; push_cast at hb; omega
      rw [hC, hP, hM, hT]
      rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide
    · by_cases heq1 : d = (t : ℤ) + 1
      · have hC : f833 t x y = true := by rw [f833_val_by_dist t x y d rfl, if_pos (by omega)]
        have hP : vPlus = true := by simp only [vPlus]; rw [if_pos (by omega)]
        have hM : vMinus = false := by
          simp only [vMinus]; rw [if_neg (by omega), if_pos (by omega)]
        rw [hC, hP, hM]
        unfold stagePow2; rw [if_neg (by push_cast; omega)]
        by_cases haxis : x = 0 ∨ y = 0
        · have htip : (|x| = ((t + 1 : ℕ) : ℤ) ∧ y = 0) ∨ (x = 0 ∧ |y| = ((t + 1 : ℕ) : ℤ)) := by
            rcases haxis with rfl | rfl
            · right; exact ⟨rfl, by simp only [abs_zero, zero_add] at hd_def; push_cast; omega⟩
            · left; exact ⟨by simp only [abs_zero, add_zero] at hd_def; push_cast; omega, rfl⟩
          have hnP3 : nP = 3 := nbr_nP_axis x y hd1 haxis
          rw [hnP3, decide_eq_true htip]
          simp only [Bool.toNat_true, Bool.toNat_false, mul_one, mul_zero, add_zero]
          decide
        · have hnot : ¬ ((|x| = ((t + 1 : ℕ) : ℤ) ∧ y = 0) ∨ (x = 0 ∧ |y| = ((t + 1 : ℕ) : ℤ))) := by
            rintro (⟨_, hy⟩ | ⟨hx, _⟩) <;> exact haxis (by tauto)
          have hnP2 : nP = 2 :=
            nbr_nP_off_axis x y (fun h => haxis (Or.inl h)) (fun h => haxis (Or.inr h))
          rw [hnP2, decide_eq_false hnot]
          simp only [Bool.toNat_true, Bool.toNat_false, mul_one, mul_zero, add_zero]
          decide
      · by_cases heq0 : d = (t : ℤ)
        · have hC : f833 t x y = false := by
            rw [f833_val_by_dist t x y d rfl, if_neg (by omega), if_pos (by omega)]
          have hP : vPlus = true := by simp only [vPlus]; rw [if_pos (by omega)]
          have hM : vMinus = true := by
            simp only [vMinus]; rw [if_neg (by omega), if_neg (by omega)]
            simp only [decide_eq_true_eq]; omega
          have hT : stagePow2 (t + 1) x y = false := by
            unfold stagePow2; rw [if_pos (by push_cast; omega)]
            simp only [decide_eq_false_iff_not]; omega
          rw [hC, hP, hM, hT]
          rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide
        · -- d < t
          have hlt : d < (t : ℤ) := by omega
          have hC : f833 t x y = decide (d % 2 = 0) := by
            rw [f833_val_by_dist t x y d rfl, if_neg (by omega), if_neg (by omega)]
            apply decide_eq_decide.mpr; omega
          have hP : vPlus = decide (d % 2 = 1) := by
            simp only [vPlus]; rw [if_neg (by omega)]
            split_ifs with h1
            · symm; simp only [decide_eq_false_iff_not]; omega
            · apply decide_eq_decide.mpr; omega
          have hM : vMinus = decide (d % 2 = 1) := by
            simp only [vMinus]; rw [if_neg (by omega), if_neg (by omega)]
            apply decide_eq_decide.mpr; omega
          have hT : stagePow2 (t + 1) x y = decide (d % 2 = 0) := by
            unfold stagePow2; rw [if_pos (by push_cast; omega), ← hd_def]
          rw [hC, hP, hM, hT]
          by_cases hp : d % 2 = 0
          · have h1 : decide (d % 2 = 1) = false := by simp only [decide_eq_false_iff_not]; omega
            rw [h1]; simp only [hp, decide_true, Bool.toNat_false, mul_zero, add_zero]; decide
          · have h1 : decide (d % 2 = 1) = true := by simp only [decide_eq_true_eq]; omega
            rw [h1]; simp only [hp, decide_false, Bool.toNat_true, mul_one]
            rcases hcases with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rw [h3, h4] <;> decide

private lemma decomp131_step_octant (M r : ℕ) (hM4 : 4 ≤ M) (hMeven : M % 2 = 0)
    (hr : r + 1 < M)
    (h10 : ∀ r', r' < M → c1 r' 1 0 = false)
    (hcur : ∀ x y : ℤ, c1 (M + r) x y = decomp131 M r x y)
    (x y : ℤ) (hy0 : 0 ≤ y) (hyx : y ≤ x) :
    c1 (M + (r + 1)) x y = decomp131 M (r + 1) x y := by
  have hx0 : 0 ≤ x := by omega
  have hax : |x| = x := abs_of_nonneg hx0
  have hay : |y| = y := abs_of_nonneg hy0
  by_cases h_in : x + y < (M : ℤ)
  · -- Case 1: Inner diamond |x| + |y| < M
    rw [decomp131_inner M (r + 1) x y (by rw [hax, hay]; exact h_in)]
    rw [show M + (r + 1) = (M + r) + 1 by omega, c1_succ]
    rw [hcur x y, hcur (x - 1) y, hcur (x + 1) y, hcur x (y - 1), hcur x (y + 1)]
    by_cases hpar : (x + y) % 2 = 0
    · -- Even sum => x + y <= M - 2, all 4 neighbors are inside and odd (false)
      have hW : decomp131 M r (x - 1) y = false := by
        rw [decomp131_inner M r (x - 1) y (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
        simp only [decide_eq_false_iff_not]; omega
      have hE : decomp131 M r (x + 1) y = false := by
        rw [decomp131_inner M r (x + 1) y (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
        simp only [decide_eq_false_iff_not]; omega
      have hS : decomp131 M r x (y - 1) = false := by
        rw [decomp131_inner M r x (y - 1) (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
        simp only [decide_eq_false_iff_not]; omega
      have hN : decomp131 M r x (y + 1) = false := by
        rw [decomp131_inner M r x (y + 1) (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
        simp only [decide_eq_false_iff_not]; omega
      rw [hW, hE, hS, hN, hax, hay, show decide ((x + y) % 2 = 0) = true by simp [hpar]]
      cases decomp131 M r x y <;> decide
    · -- Odd sum => cur = false; W (x - 1, y) is inside & even (true) => s >= 1 => false
      have hc : decomp131 M r x y = false := by
        rw [decomp131_inner M r x y (by rw [hax, hay]; exact h_in), hax, hay]
        simp only [decide_eq_false_iff_not]; omega
      have hW : decomp131 M r (x - 1) y = true := by
        rw [decomp131_inner M r (x - 1) y (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
        simp only [decide_eq_true_eq]; omega
      rw [hc, hW, hax, hay, show decide ((x + y) % 2 = 0) = false by simp only [decide_eq_false_iff_not]; omega]
      have h1 : 1 ≤ (true).toNat + (decomp131 M r (x + 1) y).toNat +
          (decomp131 M r x (y - 1)).toNat + (decomp131 M r x (y + 1)).toNat := by simp; omega
      have h2 : (true).toNat + (decomp131 M r (x + 1) y).toNat +
          (decomp131 M r x (y - 1)).toNat + (decomp131 M r x (y + 1)).toNat ≤ 4 := by
        have a1 := Bool.toNat_le (decomp131 M r (x + 1) y)
        have a2 := Bool.toNat_le (decomp131 M r x (y - 1))
        have a3 := Bool.toNat_le (decomp131 M r x (y + 1))
        simp; omega
      exact rule131_false_pos _ h1 h2
  · -- Outer region: x + y >= M
    by_cases hdiag : x = y
    · -- Case 2: Diagonal x = y, x + y >= M => 2*x >= M
      subst hdiag
      rw [decomp131_diag M (r + 1) x x (by rw [hax]; omega) rfl]
      rw [show M + (r + 1) = (M + r) + 1 by omega, c1_succ]
      rw [hcur x x, hcur (x - 1) x, hcur (x + 1) x, hcur x (x - 1), hcur x (x + 1)]
      have hE : decomp131 M r (x + 1) x = decide (r % 2 = 1) := by
        rw [decomp131_east M r (x + 1) x (by simp only [abs_eq_max_neg]; omega)
          (by simp only [abs_eq_max_neg]; omega)]
        exact c1_outside r (x + 1 - M) x (by simp only [abs_eq_max_neg]; omega)
      have hN : decomp131 M r x (x + 1) = decide (r % 2 = 1) := by
        rw [decomp131_swap]; exact hE
      by_cases hhalf : x + x = (M : ℤ)
      · have hW : decomp131 M r (x - 1) x = false := by
          rw [decomp131_inner M r (x - 1) x (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
          simp only [decide_eq_false_iff_not]; omega
        have hS : decomp131 M r x (x - 1) = false := by rw [decomp131_swap]; exact hW
        rw [hW, hS, hE, hN]
        by_cases hp : r % 2 = 1
        · have hp' : (r + 1) % 2 ≠ 1 := by omega
          simp [hp, hp']; cases decomp131 M r x x <;> decide
        · have hp' : (r + 1) % 2 = 1 := by omega
          simp [hp, hp']; cases decomp131 M r x x <;> decide
      · have hW : decomp131 M r (x - 1) x = decide (r % 2 = 1) := by
          rw [decomp131_swap, decomp131_east M r x (x - 1) (by simp only [abs_eq_max_neg]; omega)
            (by simp only [abs_eq_max_neg]; omega)]
          exact c1_outside r (x - M) (x - 1) (by simp only [abs_eq_max_neg]; omega)
        have hS : decomp131 M r x (x - 1) = decide (r % 2 = 1) := by rw [decomp131_swap]; exact hW
        rw [hW, hS, hE, hN]
        by_cases hp : r % 2 = 1
        · have hp' : (r + 1) % 2 ≠ 1 := by omega
          simp [hp, hp']; cases decomp131 M r x x <;> decide
        · have hp' : (r + 1) % 2 = 1 := by omega
          simp [hp, hp']; cases decomp131 M r x x <;> decide
    · -- East sector: 0 <= y < x and x + y >= M
      rw [decomp131_east M (r + 1) x y (by rw [hax, hay]; omega) (by rw [hay]; omega)]
      by_cases hbd : x + y = (M : ℤ)
      · by_cases hypos : 0 < y
        · -- Case 3: x + y = M, 0 < y < x => W, S are false; use rule131_diag_symm!
          rw [show M + (r + 1) = (M + r) + 1 by omega, c1_succ]
          rw [hcur x y, hcur (x - 1) y, hcur (x + 1) y, hcur x (y - 1), hcur x (y + 1)]
          have hC : decomp131 M r x y = c1 r (x - M) y :=
            decomp131_east M r x y (by rw [hax, hay]; omega) (by rw [hay]; omega)
          have hW : decomp131 M r (x - 1) y = false := by
            rw [decomp131_inner M r (x - 1) y (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
            simp only [decide_eq_false_iff_not]; omega
          have hS : decomp131 M r x (y - 1) = false := by
            rw [decomp131_inner M r x (y - 1) (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
            simp only [decide_eq_false_iff_not]; omega
          have hE : decomp131 M r (x + 1) y = c1 r ((x - M) + 1) y := by
            rw [decomp131_east M r (x + 1) y (by simp only [abs_eq_max_neg]; omega)
              (by simp only [abs_eq_max_neg]; omega)]
            congr 1; ring
          have hN : decomp131 M r x (y + 1) = c1 r (x - M) (y + 1) := by
            by_cases hxy1 : x = y + 1
            · rw [decomp131_diag M r x (y + 1) (by simp only [abs_eq_max_neg]; omega)
                (by simp only [abs_eq_max_neg]; omega)]
              symm
              exact c1_outside r (x - M) (y + 1) (by simp only [abs_eq_max_neg]; omega)
            · exact decomp131_east M r x (y + 1) (by simp only [abs_eq_max_neg]; omega)
                (by simp only [abs_eq_max_neg]; omega)
          rw [hC, hW, hS, hE, hN]
          conv_rhs => rw [c1_succ]
          have hsymW : c1 r ((x - M) - 1) y = c1 r (x - M) (y + 1) := by
            rw [show (x - (M : ℤ)) - 1 = -(y + 1) by omega, c1_neg_x, c1_swap,
                show x - (M : ℤ) = -y by omega, c1_neg_x]
          have hsymS : c1 r (x - M) (y - 1) = c1 r ((x - M) + 1) y := by
            rw [show x - (M : ℤ) = -y by omega, c1_neg_x, c1_swap,
                show -y + 1 = -(y - 1) by ring, c1_neg_x]
          rw [hsymW, hsymS]
          simp only [Bool.toNat_false, zero_add, add_zero]
          have hcom : (c1 r (x - M + 1) y).toNat + (c1 r (x - M) (y + 1)).toNat =
              (c1 r (x - M + 1) y).toNat + (c1 r (x - M) (y + 1)).toNat := rfl
          have hsym_eq := rule131_diag_symm (c1 r (x - M) y) (c1 r (x - M + 1) y) (c1 r (x - M) (y + 1))
          have hsum2 : (c1 r (x - M) (y + 1)).toNat + (c1 r (x - M + 1) y).toNat +
              (c1 r (x - M + 1) y).toNat + (c1 r (x - M) (y + 1)).toNat =
              (c1 r (x - M) (y + 1)).toNat + (c1 r (x - M + 1) y).toNat +
              (c1 r (x - M + 1) y).toNat + (c1 r (x - M) (y + 1)).toNat := rfl
          exact hsym_eq
        · -- Case 4: Tip (M, 0)
          have hyz : y = 0 := by omega
          subst hyz
          have hxm : x = (M : ℤ) := by omega
          subst hxm
          rw [show (M : ℤ) - (M : ℤ) = 0 by ring]
          rw [show M + (r + 1) = (M + r) + 1 by omega, c1_succ]
          simp only [zero_add, zero_sub]
          rw [hcur M 0, hcur (M - 1) 0, hcur (M + 1) 0, hcur M (-1), hcur M 1]
          have hC : decomp131 M r M 0 = c1 r 0 0 := by
            rw [decomp131_east M r M 0 (by simp only [abs_eq_max_neg]; omega)
              (by simp only [abs_eq_max_neg]; omega), sub_self]
          have hE : decomp131 M r (M + 1) 0 = c1 r 1 0 := by
            rw [decomp131_east M r (M + 1) 0 (by simp only [abs_eq_max_neg]; omega)
              (by simp only [abs_eq_max_neg]; omega)]
            congr 1; ring
          have hS : decomp131 M r M (-1) = c1 r 0 (-1) := by
            rw [decomp131_east M r M (-1) (by simp only [abs_eq_max_neg]; omega)
              (by simp only [abs_eq_max_neg]; omega), sub_self]
          have hN : decomp131 M r M 1 = c1 r 0 1 := by
            rw [decomp131_east M r M 1 (by simp only [abs_eq_max_neg]; omega)
              (by simp only [abs_eq_max_neg]; omega), sub_self]
          have hW : decomp131 M r (M - 1) 0 = false := by
            rw [decomp131_inner M r (M - 1) 0 (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
            simp only [decide_eq_false_iff_not]; omega
          rw [hC, hE, hS, hN, hW]
          conv_rhs => rw [c1_succ]
          simp only [zero_add, zero_sub]
          have hw' : c1 r (-1) 0 = false := by
            rw [show (-1 : ℤ) = -(1 : ℤ) by ring, c1_neg_x]
            exact h10 r (by omega)
          rw [hw']
      · -- Case 5: Strictly outside inner diamond: x + y > M and 0 <= y < x
        rw [show M + (r + 1) = (M + r) + 1 by omega, c1_succ, c1_succ]
        rw [hcur x y, hcur (x - 1) y, hcur (x + 1) y, hcur x (y - 1), hcur x (y + 1)]
        have match_pt : ∀ a b : ℤ, (M : ℤ) ≤ |a| + |b| → |b| ≤ a →
            decomp131 M r a b = c1 r (a - M) b := by
          intro a b hs hba
          by_cases hlt : |b| < a
          · exact decomp131_east M r a b hs hlt
          · have heq : |a| = |b| := by simp only [abs_eq_max_neg] at *; omega
            rw [decomp131_diag M r a b hs heq]
            symm
            exact c1_outside r (a - M) b (by simp only [abs_eq_max_neg] at *; omega)
        have hC := match_pt x y (by simp only [abs_eq_max_neg]; omega) (by simp only [abs_eq_max_neg]; omega)
        have hW := match_pt (x - 1) y (by simp only [abs_eq_max_neg]; omega) (by simp only [abs_eq_max_neg]; omega)
        have hE := match_pt (x + 1) y (by simp only [abs_eq_max_neg]; omega) (by simp only [abs_eq_max_neg]; omega)
        have hS := match_pt x (y - 1) (by simp only [abs_eq_max_neg]; omega) (by simp only [abs_eq_max_neg]; omega)
        have hN := match_pt x (y + 1) (by simp only [abs_eq_max_neg]; omega) (by simp only [abs_eq_max_neg]; omega)
        rw [hC, hW, hE, hS, hN]
        rw [show x - 1 - (M : ℤ) = (x - (M : ℤ)) - 1 by ring,
            show x + 1 - (M : ℤ) = (x - (M : ℤ)) + 1 by ring]

private lemma decomp131_step (M r : ℕ) (hM4 : 4 ≤ M) (hMeven : M % 2 = 0)
    (hr : r + 1 < M)
    (h10 : ∀ r', r' < M → c1 r' 1 0 = false)
    (hcur : ∀ x y : ℤ, c1 (M + r) x y = decomp131 M r x y) :
    ∀ x y : ℤ, c1 (M + (r + 1)) x y = decomp131 M (r + 1) x y := by
  intro x y
  have hs : ∀ u v : ℤ, 0 ≤ u → 0 ≤ v → c1 (M + (r + 1)) u v = decomp131 M (r + 1) u v := by
    intro u v hu hv
    rcases le_or_gt v u with hvu | huv
    · exact decomp131_step_octant M r hM4 hMeven hr h10 hcur u v hv hvu
    · rw [← c1_swap, ← decomp131_swap]
      exact decomp131_step_octant M r hM4 hMeven hr h10 hcur v u hu (by omega)
  rw [← c1_abs]
  have hd : decomp131 M (r + 1) |x| |y| = decomp131 M (r + 1) x y := by
    rcases le_or_gt 0 x with hx | hx <;> rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hx, abs_of_nonneg hy]
    · rw [abs_of_nonneg hx, abs_of_neg hy, decomp131_neg_y]
    · rw [abs_of_neg hx, abs_of_nonneg hy, decomp131_neg_x]
    · rw [abs_of_neg hx, abs_of_neg hy, decomp131_neg_x, decomp131_neg_y]
  rw [← hd]
  exact hs |x| |y| (abs_nonneg x) (abs_nonneg y)

private lemma decomp131_to_f833 (M : ℕ) (hM4 : 4 ≤ M) (hMeven : M % 2 = 0)
    (hprev : ∀ x y : ℤ, c1 (M - 1) x y = f833 (M - 1) x y) (x y : ℤ) :
    decomp131 M (M - 1) x y = f833 (2 * M - 1) x y := by
  have hs : ∀ u v : ℤ, 0 ≤ v → v ≤ u → decomp131 M (M - 1) u v = f833 (2 * M - 1) u v := by
    intro u v hv hvu
    have hu : 0 ≤ u := by omega
    by_cases hin : u + v < (M : ℤ)
    · rw [decomp131_inner M (M - 1) u v (by rw [abs_of_nonneg hu, abs_of_nonneg hv]; exact hin)]
      unfold f833; dsimp only
      rw [abs_of_nonneg hu, abs_of_nonneg hv, if_neg (by omega), if_neg (by omega)]
      apply decide_eq_decide.mpr; omega
    · by_cases heq : u = v
      · rw [decomp131_diag M (M - 1) u v (by rw [abs_of_nonneg hu, abs_of_nonneg hv]; omega)
          (by rw [abs_of_nonneg hu, abs_of_nonneg hv]; exact heq)]
        unfold f833; dsimp only
        rw [abs_of_nonneg hu, abs_of_nonneg hv, show decide ((M - 1) % 2 = 1) = true by
          simp only [decide_eq_true_eq]; omega]
        split_ifs with h1 h2
        · rfl
        · omega
        · symm; simp only [decide_eq_true_eq]; omega
      · rw [decomp131_east M (M - 1) u v (by rw [abs_of_nonneg hu, abs_of_nonneg hv]; omega)
          (by rw [abs_of_nonneg hv]; omega), hprev]
        unfold f833; dsimp only
        rw [abs_of_nonneg hu, abs_of_nonneg hv]
        by_cases hge : (M : ℤ) ≤ u
        · rw [abs_of_nonneg (by omega : 0 ≤ u - (M : ℤ))]
          split_ifs <;> first | rfl | omega | (apply decide_eq_decide.mpr; omega)
        · rw [abs_of_neg (by omega : u - (M : ℤ) < 0)]
          have hl1 : ¬ (((M - 1 : ℕ) : ℤ) < -(u - (M : ℤ)) + v) := by omega
          have hr1 : ¬ (((2 * M - 1 : ℕ) : ℤ) < u + v) := by omega
          have hr2 : ¬ (u + v = ((2 * M - 1 : ℕ) : ℤ)) := by omega
          rw [if_neg hl1, if_neg hr1, if_neg hr2]
          split_ifs with h1
          · symm; simp only [decide_eq_false_iff_not]; omega
          · apply decide_eq_decide.mpr; omega
  have hsym : ∀ u v : ℤ, 0 ≤ u → 0 ≤ v → decomp131 M (M - 1) u v = f833 (2 * M - 1) u v := by
    intro u v hu hv
    rcases le_or_gt v u with hvu | huv
    · exact hs u v hv hvu
    · rw [← decomp131_swap]
      have hf : f833 (2 * M - 1) v u = f833 (2 * M - 1) u v := by
        unfold f833; dsimp only; rw [add_comm |v| |u|]
      rw [← hf]
      exact hs v u hu (by omega)
  have hd1 : decomp131 M (M - 1) |x| |y| = decomp131 M (M - 1) x y := by
    rcases le_or_gt 0 x with hx | hx <;> rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hx, abs_of_nonneg hy]
    · rw [abs_of_nonneg hx, abs_of_neg hy, decomp131_neg_y]
    · rw [abs_of_neg hx, abs_of_nonneg hy, decomp131_neg_x]
    · rw [abs_of_neg hx, abs_of_neg hy, decomp131_neg_x, decomp131_neg_y]
  have hd2 : f833 (2 * M - 1) |x| |y| = f833 (2 * M - 1) x y := by
    unfold f833; simp
  rw [← hd1, ← hd2]
  exact hsym |x| |y| (abs_nonneg x) (abs_nonneg y)

private lemma c1_base_3 (x y : ℤ) : c1 3 x y = f833 3 x y := by
  by_cases hgt : 3 < |x| + |y|
  · rw [c1_outside 3 x y hgt]
    unfold f833; dsimp only; rw [if_pos (by exact_mod_cast hgt)]; decide
  · have hx1 : -3 ≤ x := by simp only [abs_eq_max_neg] at hgt; omega
    have hx2 : x ≤ 3 := by simp only [abs_eq_max_neg] at hgt; omega
    have hy1 : -3 ≤ y := by simp only [abs_eq_max_neg] at hgt; omega
    have hy2 : y ≤ 3 := by simp only [abs_eq_max_neg] at hgt; omega
    interval_cases x <;> interval_cases y <;> decide

private lemma c1_pow2_eq_f833 (n : ℕ) (hn : 2 ≤ n) :
    (∀ x y : ℤ, c1 (2 ^ n - 1) x y = f833 (2 ^ n - 1) x y) ∧
    (∀ r : ℕ, r < 2 ^ n → c1 r 1 0 = false) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h1 : n = 1
    · subst h1
      refine ⟨c1_base_3, ?_⟩
      intro r hr
      have : r < 4 := by simpa using hr
      interval_cases r <;> decide
    · obtain ⟨hprev, h10⟩ := ih (by omega)
      set M := 2 ^ n
      have hM4 : 4 ≤ M := by
        have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
        simpa using this
      have hMeven : M % 2 = 0 := by
        have hpow : M = 2 * 2 ^ (n - 1) := by
          show 2 ^ n = 2 * 2 ^ (n - 1)
          conv_lhs => rw [show n = (n - 1) + 1 by omega]
          rw [pow_succ']
        omega
      have hM : ∀ x y : ℤ, c1 M x y = stagePow2 M x y :=
        c1_f833_to_stagePow2 M hM4 hMeven hprev
      have hdec : ∀ r : ℕ, r < M → ∀ x y : ℤ, c1 (M + r) x y = decomp131 M r x y := by
        intro r
        induction r with
        | zero =>
          intro _ x y
          rw [Nat.add_zero, hM x y, decomp131_zero M (by omega) x y]
        | succ r ihr =>
          intro hr x y
          exact decomp131_step M r hM4 hMeven hr h10 (ihr (by omega)) x y
      have h2M : 2 ^ (n + 1) = 2 * M := by rw [pow_succ']
      refine ⟨?_, ?_⟩
      · intro x y
        rw [h2M]
        conv_lhs => rw [show 2 * M - 1 = M + (M - 1) by omega]
        rw [hdec (M - 1) (by omega) x y, decomp131_to_f833 M hM4 hMeven hprev x y]
      · intro r hr
        rw [h2M] at hr
        by_cases hlt : r < M
        · exact h10 r hlt
        · rw [show r = M + (r - M) by omega, hdec (r - M) (by omega) 1 0,
              decomp131_inner M (r - M) 1 0 (by simp; omega)]
          decide

private lemma count_131_eq (n : ℕ) (hn : 1 < n) : a n = count 131 (2 ^ n - 1) := by
  have h2n : 3 ≤ 2 ^ n - 1 := by
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
    simp at this; omega
  have h1 := (c1_pow2_eq_f833 n (by omega)).1
  unfold a count
  congr 1; ext p
  simp only [Finset.mem_filter]
  have heq : state 833 (2 ^ n - 1) p.1 p.2 = state 131 (2 ^ n - 1) p.1 p.2 := by
    rw [stateA_eq_f833 (Or.inl rfl) (2 ^ n - 1) h2n, ← h1 p.1 p.2]
  rw [heq]

end OMA.Proof_oeis_a273676

theorem OMA.solution : type_of% @OMA.S_oeis_a273676.main :=
  ⟨OMA.Proof_oeis_a273676.count_849_eq, OMA.Proof_oeis_a273676.count_131_eq,
   OMA.Proof_oeis_a273676.a_closed, OMA.Proof_oeis_a273676.a_rec, OMA.Proof_oeis_a273676.gf_eq⟩
