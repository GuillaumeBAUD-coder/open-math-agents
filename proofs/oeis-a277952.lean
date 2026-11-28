import OMAStatements.S_oeis_a277952

-- Problem: A277952: Binary representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 14, based on the 5-celled von Neumann neighborhood.
-- Credit: @Qwer2077 (the owner of the agent is credited as the solver)

namespace OMA.Proof_oeis_a277952

open OMA.S_oeis_a277952
open PowerSeries

private def rule14 (c : Bool) (s : ℕ) : Bool :=
  Nat.testBit 14 (c.toNat + 2 * s)

private lemma cell_step (t : ℕ) (x y : ℤ) :
    cell 14 (t + 1) x y =
      rule14 (cell 14 t x y)
        ((cell 14 t (x + 1) y).toNat + (cell 14 t (x - 1) y).toNat +
         (cell 14 t x (y + 1)).toNat + (cell 14 t x (y - 1)).toNat) := rfl

private lemma cell_outside : ∀ (t : ℕ) (x y : ℤ), (t : ℤ) < |x| + |y| → cell 14 t x y = false
  | 0, x, y, h => by
    have hxy : ¬(x = 0 ∧ y = 0) := by
      rintro ⟨rfl, rfl⟩; simp at h
    simp [cell, hxy]
  | t + 1, x, y, h => by
    rw [cell_step]
    have hc : cell 14 t x y = false := cell_outside t x y (by omega)
    have h1 : cell 14 t (x + 1) y = false := cell_outside t (x + 1) y (by simp only [abs_eq_max_neg] at h ⊢; omega)
    have h2 : cell 14 t (x - 1) y = false := cell_outside t (x - 1) y (by simp only [abs_eq_max_neg] at h ⊢; omega)
    have h3 : cell 14 t x (y + 1) = false := cell_outside t x (y + 1) (by simp only [abs_eq_max_neg] at h ⊢; omega)
    have h4 : cell 14 t x (y - 1) = false := cell_outside t x (y - 1) (by simp only [abs_eq_max_neg] at h ⊢; omega)
    rw [hc, h1, h2, h3, h4]
    decide

private lemma cell_neg_y : ∀ (t : ℕ) (x y : ℤ), cell 14 t x (-y) = cell 14 t x y
  | 0, x, y => by simp [cell]
  | t + 1, x, y => by
    rw [cell_step, cell_step, cell_neg_y t x y, cell_neg_y t (x + 1) y, cell_neg_y t (x - 1) y]
    have ha : cell 14 t x (-y + 1) = cell 14 t x (y - 1) := by
      have : -y + 1 = -(y - 1) := by ring
      rw [this, cell_neg_y]
    have hb : cell 14 t x (-y - 1) = cell 14 t x (y + 1) := by
      have : -y - 1 = -(y + 1) := by ring
      rw [this, cell_neg_y]
    rw [ha, hb]
    congr 1
    omega

private lemma cell_neg_x : ∀ (t : ℕ) (x y : ℤ), cell 14 t (-x) y = cell 14 t x y
  | 0, x, y => by simp [cell]
  | t + 1, x, y => by
    rw [cell_step, cell_step, cell_neg_x t x y, cell_neg_x t x (y + 1), cell_neg_x t x (y - 1)]
    have ha : cell 14 t (-x + 1) y = cell 14 t (x - 1) y := by
      have : -x + 1 = -(x - 1) := by ring
      rw [this, cell_neg_x]
    have hb : cell 14 t (-x - 1) y = cell 14 t (x + 1) y := by
      have : -x - 1 = -(x + 1) := by ring
      rw [this, cell_neg_x]
    rw [ha, hb]
    congr 1
    omega

private def f0 (t : ℕ) (x : ℤ) : Bool :=
  decide (|x| = (t : ℤ) ∨ |x| = (t : ℤ) - 1 ∨ (|x| < (t : ℤ) - 1 ∧ |x| % 2 = 1))

private def f1 (t : ℕ) (x : ℤ) : Bool :=
  decide (|x| < (t : ℤ) ∧ |x| % 2 = 0)

private lemma f0_neg (t : ℕ) (x : ℤ) : f0 t (-x) = f0 t x := by
  simp [f0, abs_neg]

private lemma f1_neg (t : ℕ) (x : ℤ) : f1 t (-x) = f1 t x := by
  simp [f1, abs_neg]

private lemma step_y0_nonneg (t : ℕ) (x : ℤ) (hx : 0 ≤ x) :
    rule14 (f0 t x) ((f0 t (x + 1)).toNat + (f0 t (x - 1)).toNat + (f1 t x).toNat + (f1 t x).toNat) =
      f0 (t + 1) x := by
  have habx : |x| = x := abs_of_nonneg hx
  have habp : |x + 1| = x + 1 := abs_of_nonneg (by omega)
  by_cases hgt : (t : ℤ) + 1 < x
  · have h1 : f0 t x = false := by simp only [f0, habx, decide_eq_false_iff_not]; omega
    have h2 : f0 t (x + 1) = false := by simp only [f0, habp, decide_eq_false_iff_not]; omega
    have h3 : f0 t (x - 1) = false := by
      simp only [f0, abs_of_nonneg (show 0 ≤ x - 1 by omega), decide_eq_false_iff_not]; omega
    have h4 : f1 t x = false := by simp only [f1, habx, decide_eq_false_iff_not]; omega
    have h5 : f0 (t + 1) x = false := by simp only [f0, habx, decide_eq_false_iff_not]; omega
    rw [h1, h2, h3, h4, h5]; decide
  · by_cases heq1 : x = (t : ℤ) + 1
    · subst heq1
      have h1 : f0 t ((t : ℤ) + 1) = false := by simp only [f0, habx, decide_eq_false_iff_not]; omega
      have h2 : f0 t ((t : ℤ) + 1 + 1) = false := by simp only [f0, habp, decide_eq_false_iff_not]; omega
      have h3 : f0 t ((t : ℤ) + 1 - 1) = true := by
        simp only [f0, show |(t : ℤ) + 1 - 1| = (t : ℤ) by rw [show (t : ℤ) + 1 - 1 = (t : ℤ) by omega]; exact abs_of_nonneg (by omega),
          decide_eq_true_eq]
        left; trivial
      have h4 : f1 t ((t : ℤ) + 1) = false := by simp only [f1, habx, decide_eq_false_iff_not]; omega
      have h5 : f0 (t + 1) ((t : ℤ) + 1) = true := by
        simp only [f0, habx, decide_eq_true_eq]; left; omega
      rw [h1, h2, h3, h4, h5]; decide
    · by_cases heq0 : x = (t : ℤ)
      · subst heq0
        have h1 : f0 t (t : ℤ) = true := by simp only [f0, habx, decide_eq_true_eq]; left; trivial
        have h2 : f0 t ((t : ℤ) + 1) = false := by simp only [f0, habp, decide_eq_false_iff_not]; omega
        have h4 : f1 t (t : ℤ) = false := by simp only [f1, habx, decide_eq_false_iff_not]; omega
        have h5 : f0 (t + 1) (t : ℤ) = true := by
          simp only [f0, habx, decide_eq_true_eq]; right; left; omega
        rcases t with _ | t'
        · have h3 : f0 0 (((0 : ℕ) : ℤ) - 1) = false := by decide
          rw [h1, h2, h3, h4, h5]; decide
        · have h3 : f0 (t' + 1) (((t' + 1 : ℕ) : ℤ) - 1) = true := by
            have habm : |((t' + 1 : ℕ) : ℤ) - 1| = ((t' + 1 : ℕ) : ℤ) - 1 := abs_of_nonneg (by omega)
            simp only [f0, habm, decide_eq_true_eq]; right; left; trivial
          rw [h1, h2, h3, h4, h5]; decide
      · by_cases heqm1 : x = (t : ℤ) - 1
        · have h1 : f0 t x = true := by simp only [f0, habx, decide_eq_true_eq]; right; left; exact heqm1
          have h2 : f0 t (x + 1) = true := by simp only [f0, habp, decide_eq_true_eq]; left; omega
          rcases eq_or_lt_of_le hx with rfl | hpos
          · have ht_eq : t = 1 := by omega
            subst ht_eq
            decide
          · have habm : |x - 1| = x - 1 := abs_of_nonneg (by omega)
            by_cases hpar : x % 2 = 0
            · have h3 : f0 t (x - 1) = true := by
                simp only [f0, habm, decide_eq_true_eq]; right; right; omega
              have h4 : f1 t x = true := by simp only [f1, habx, decide_eq_true_eq]; omega
              have h5 : f0 (t + 1) x = false := by simp only [f0, habx, decide_eq_false_iff_not]; omega
              rw [h1, h2, h3, h4, h5]; decide
            · have h3 : f0 t (x - 1) = false := by simp only [f0, habm, decide_eq_false_iff_not]; omega
              have h4 : f1 t x = false := by simp only [f1, habx, decide_eq_false_iff_not]; omega
              have h5 : f0 (t + 1) x = true := by
                simp only [f0, habx, decide_eq_true_eq]; right; right; omega
              rw [h1, h2, h3, h4, h5]; decide
        · have hxle : x ≤ (t : ℤ) - 2 := by omega
          by_cases hpar : x % 2 = 0
          · have h1 : f0 t x = false := by simp only [f0, habx, decide_eq_false_iff_not]; omega
            have h2 : f0 t (x + 1) = true := by
              simp only [f0, habp, decide_eq_true_eq]
              by_cases hxt : x + 1 = (t : ℤ) - 1
              · right; left; exact hxt
              · right; right; omega
            have h3 : f0 t (x - 1) = true := by
              rcases eq_or_lt_of_le hx with rfl | hpos
              · simp only [f0, show |(0 : ℤ) - 1| = 1 by decide, decide_eq_true_eq]
                by_cases ht2 : t = 2
                · right; left; omega
                · right; right; omega
              · have habm : |x - 1| = x - 1 := abs_of_nonneg (by omega)
                simp only [f0, habm, decide_eq_true_eq]
                right; right; omega
            have h4 : f1 t x = true := by simp only [f1, habx, decide_eq_true_eq]; omega
            have h5 : f0 (t + 1) x = false := by simp only [f0, habx, decide_eq_false_iff_not]; omega
            rw [h1, h2, h3, h4, h5]; decide
          · have habm : |x - 1| = x - 1 := abs_of_nonneg (by omega)
            have h1 : f0 t x = true := by
              simp only [f0, habx, decide_eq_true_eq]; right; right; omega
            have h2 : f0 t (x + 1) = if x = (t : ℤ) - 2 then true else false := by
              by_cases hxt : x = (t : ℤ) - 2
              · rw [if_pos hxt]; simp only [f0, habp, decide_eq_true_eq]; right; left; omega
              · rw [if_neg hxt]; simp only [f0, habp, decide_eq_false_iff_not]; omega
            have h3 : f0 t (x - 1) = false := by simp only [f0, habm, decide_eq_false_iff_not]; omega
            have h4 : f1 t x = false := by simp only [f1, habx, decide_eq_false_iff_not]; omega
            have h5 : f0 (t + 1) x = true := by
              simp only [f0, habx, decide_eq_true_eq]; right; right; omega
            rw [h1, h2, h3, h4, h5]
            split_ifs <;> decide

private lemma step_y1_nonneg (t : ℕ) (x : ℤ) (hx : 0 ≤ x) (u : Bool)
    (hu : (t : ℤ) < x + 2 → u = false) :
    rule14 (f1 t x) ((f1 t (x + 1)).toNat + (f1 t (x - 1)).toNat + u.toNat + (f0 t x).toNat) =
      f1 (t + 1) x := by
  have habx : |x| = x := abs_of_nonneg hx
  have habp : |x + 1| = x + 1 := abs_of_nonneg (by omega)
  by_cases hgt : (t : ℤ) + 1 ≤ x
  · have hu0 : u = false := hu (by omega)
    have h1 : f1 t x = false := by simp only [f1, habx, decide_eq_false_iff_not]; omega
    have h2 : f1 t (x + 1) = false := by simp only [f1, habp, decide_eq_false_iff_not]; omega
    have h3 : f1 t (x - 1) = false := by
      simp only [f1, abs_of_nonneg (show 0 ≤ x - 1 by omega), decide_eq_false_iff_not]; omega
    have h4 : f0 t x = false := by simp only [f0, habx, decide_eq_false_iff_not]; omega
    have h5 : f1 (t + 1) x = false := by simp only [f1, habx, decide_eq_false_iff_not]; omega
    rw [hu0, h1, h2, h3, h4, h5]; decide
  · by_cases heq0 : x = (t : ℤ)
    · subst heq0
      have hu0 : u = false := hu (by omega)
      have h1 : f1 t (t : ℤ) = false := by simp only [f1, habx, decide_eq_false_iff_not]; omega
      have h2 : f1 t ((t : ℤ) + 1) = false := by simp only [f1, habp, decide_eq_false_iff_not]; omega
      have h4 : f0 t (t : ℤ) = true := by simp only [f0, habx, decide_eq_true_eq]; left; trivial
      rcases t with _ | t'
      · have h3 : f1 0 (((0 : ℕ) : ℤ) - 1) = false := by decide
        have h5 : f1 (0 + 1) ((0 : ℕ) : ℤ) = true := by decide
        rw [hu0, h1, h2, h3, h4, h5]; decide
      · have habm : |((t' + 1 : ℕ) : ℤ) - 1| = (t' : ℤ) := by
          rw [show ((t' + 1 : ℕ) : ℤ) - 1 = (t' : ℤ) by omega, abs_of_nonneg (by omega)]
        by_cases hpar : ((t' + 1 : ℕ) : ℤ) % 2 = 0
        · have h3 : f1 (t' + 1) (((t' + 1 : ℕ) : ℤ) - 1) = false := by
            simp only [f1, habm, decide_eq_false_iff_not]; omega
          have h5 : f1 (t' + 1 + 1) ((t' + 1 : ℕ) : ℤ) = true := by
            simp only [f1, habx, decide_eq_true_eq]; omega
          rw [hu0, h1, h2, h3, h4, h5]; decide
        · have h3 : f1 (t' + 1) (((t' + 1 : ℕ) : ℤ) - 1) = true := by
            simp only [f1, habm, decide_eq_true_eq]; omega
          have h5 : f1 (t' + 1 + 1) ((t' + 1 : ℕ) : ℤ) = false := by
            simp only [f1, habx, decide_eq_false_iff_not]; omega
          rw [hu0, h1, h2, h3, h4, h5]; decide
    · by_cases heqm1 : x = (t : ℤ) - 1
      · have hu0 : u = false := hu (by omega)
        have h2 : f1 t (x + 1) = false := by simp only [f1, habp, decide_eq_false_iff_not]; omega
        have h4 : f0 t x = true := by simp only [f0, habx, decide_eq_true_eq]; right; left; exact heqm1
        rcases eq_or_lt_of_le hx with rfl | hpos
        · have ht1 : t = 1 := by omega
          subst ht1
          have h1 : f1 1 0 = true := by decide
          have h3 : f1 1 ((0 : ℤ) - 1) = false := by decide
          have h5 : f1 2 0 = true := by decide
          rw [hu0, h1, h2, h3, h4, h5]; decide
        · have habm : |x - 1| = x - 1 := abs_of_nonneg (by omega)
          by_cases hpar : x % 2 = 0
          · have h1 : f1 t x = true := by simp only [f1, habx, decide_eq_true_eq]; omega
            have h3 : f1 t (x - 1) = false := by simp only [f1, habm, decide_eq_false_iff_not]; omega
            have h5 : f1 (t + 1) x = true := by simp only [f1, habx, decide_eq_true_eq]; omega
            rw [hu0, h1, h2, h3, h4, h5]; decide
          · have h1 : f1 t x = false := by simp only [f1, habx, decide_eq_false_iff_not]; omega
            have h3 : f1 t (x - 1) = true := by simp only [f1, habm, decide_eq_true_eq]; omega
            have h5 : f1 (t + 1) x = false := by simp only [f1, habx, decide_eq_false_iff_not]; omega
            rw [hu0, h1, h2, h3, h4, h5]; decide
      · have hxle : x ≤ (t : ℤ) - 2 := by omega
        by_cases hpar : x % 2 = 0
        · have h1 : f1 t x = true := by simp only [f1, habx, decide_eq_true_eq]; omega
          have h2 : f1 t (x + 1) = false := by simp only [f1, habp, decide_eq_false_iff_not]; omega
          have h3 : f1 t (x - 1) = false := by
            rcases eq_or_lt_of_le hx with rfl | hpos
            · simp [f1]
            · simp only [f1, abs_of_nonneg (show 0 ≤ x - 1 by omega), decide_eq_false_iff_not]; omega
          have h4 : f0 t x = false := by simp only [f0, habx, decide_eq_false_iff_not]; omega
          have h5 : f1 (t + 1) x = true := by simp only [f1, habx, decide_eq_true_eq]; omega
          rw [h1, h2, h3, h4, h5]
          cases u <;> decide
        · have habm : |x - 1| = x - 1 := abs_of_nonneg (by omega)
          have h1 : f1 t x = false := by simp only [f1, habx, decide_eq_false_iff_not]; omega
          have h2 : f1 t (x + 1) = true := by simp only [f1, habp, decide_eq_true_eq]; omega
          have h3 : f1 t (x - 1) = true := by simp only [f1, habm, decide_eq_true_eq]; omega
          have h4 : f0 t x = true := by
            simp only [f0, habx, decide_eq_true_eq]; right; right; omega
          have h5 : f1 (t + 1) x = false := by simp only [f1, habx, decide_eq_false_iff_not]; omega
          rw [h1, h2, h3, h4, h5]
          cases u <;> decide

private lemma cell_strip : ∀ t : ℕ, (∀ x : ℤ, cell 14 t x 0 = f0 t x) ∧ (∀ x : ℤ, cell 14 t x 1 = f1 t x)
  | 0 => ⟨fun x => by
            by_cases hx : x = 0
            · subst hx; decide
            · have hne : |x| ≠ 0 := by simp [hx]
              have hnn : 0 ≤ |x| := abs_nonneg x
              simp only [cell, f0, hx, false_and, decide_false, Nat.cast_zero, zero_sub]
              symm
              rw [decide_eq_false_iff_not]
              omega,
          fun x => by simp [cell, f1]⟩
  | t + 1 => by
    obtain ⟨ih0, ih1⟩ := cell_strip t
    refine ⟨fun x => ?_, fun x => ?_⟩
    · by_cases hx : 0 ≤ x
      · rw [cell_step]
        have hm1 : cell 14 t x (-1) = cell 14 t x 1 := cell_neg_y t x 1
        rw [show (0 : ℤ) + 1 = 1 by norm_num, show (0 : ℤ) - 1 = -1 by norm_num, hm1]
        rw [ih0, ih0, ih0, ih1]
        exact step_y0_nonneg t x hx
      · have hnx : 0 ≤ -x := by omega
        rw [← cell_neg_x (t + 1) x 0, ← f0_neg (t + 1) x]
        rw [cell_step]
        have hm1 : cell 14 t (-x) (-1) = cell 14 t (-x) 1 := cell_neg_y t (-x) 1
        rw [show (0 : ℤ) + 1 = 1 by norm_num, show (0 : ℤ) - 1 = -1 by norm_num, hm1]
        rw [ih0, ih0, ih0, ih1]
        exact step_y0_nonneg t (-x) hnx
    · by_cases hx : 0 ≤ x
      · rw [cell_step]
        rw [show (1 : ℤ) + 1 = 2 by norm_num, show (1 : ℤ) - 1 = 0 by norm_num]
        rw [ih1, ih1, ih1, ih0]
        exact step_y1_nonneg t x hx (cell 14 t x 2) (fun hlt =>
          cell_outside t x 2 (by rw [abs_of_nonneg hx, show |(2 : ℤ)| = 2 by decide]; omega))
      · have hnx : 0 ≤ -x := by omega
        rw [← cell_neg_x (t + 1) x 1, ← f1_neg (t + 1) x]
        rw [cell_step]
        rw [show (1 : ℤ) + 1 = 2 by norm_num, show (1 : ℤ) - 1 = 0 by norm_num]
        rw [ih1, ih1, ih1, ih0]
        exact step_y1_nonneg t (-x) hnx (cell 14 t (-x) 2) (fun hlt =>
          cell_outside t (-x) 2 (by rw [abs_of_nonneg hnx, show |(2 : ℤ)| = 2 by decide]; omega))

private lemma a_eq_sum_f0 (n : ℕ) :
    a n = ∑ j ∈ Finset.range (n + 1), if f0 n (j : ℤ) then (10 : ℤ) ^ j else 0 := by
  unfold a
  rw [← Finset.sum_range_reflect (fun k => if cell 14 n ((k : ℤ) - n) 0 then (10 : ℤ) ^ (n - k) else 0) (n + 1)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjle : j ≤ n := by simp [Finset.mem_range] at hj; omega
  have h1 : n + 1 - 1 - j = n - j := by omega
  have h2 : n - (n - j) = j := by omega
  have h3 : (((n - j : ℕ) : ℤ) - (n : ℤ)) = -(j : ℤ) := by omega
  rw [h1, h2, h3, (cell_strip n).1, f0_neg]

private lemma odd_pow_sum (m : ℕ) :
    (99 : ℤ) * (∑ r ∈ Finset.range m, (10 : ℤ) ^ (2 * r + 1)) = 10 * (10 : ℤ) ^ (2 * m) - 10 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

private lemma f0_even_eval (m j : ℕ) (hj : j ≤ 2 * m) :
    f0 (2 * m) (j : ℤ) = decide (j = 2 * m ∨ j % 2 = 1) := by
  simp only [f0, Nat.abs_cast, decide_eq_decide]
  omega

private lemma a_even (m : ℕ) :
    (99 : ℤ) * a (2 * m) = if m = 0 then 99 else 109 * (10 : ℤ) ^ (2 * m) - 10 := by
  rcases m with _ | m'
  · simp only [Nat.mul_zero, ite_true]
    rw [a_eq_sum_f0]; decide
  · simp only [Nat.succ_ne_zero, ite_false]
    set m := m' + 1
    rw [a_eq_sum_f0, Finset.sum_range_succ]
    have htop : f0 (2 * m) ((2 * m : ℕ) : ℤ) = true := by
      rw [f0_even_eval m (2 * m) le_rfl]; simp
    rw [htop, if_pos rfl]
    have hsum : (∑ j ∈ Finset.range (2 * m), if f0 (2 * m) (j : ℤ) then (10 : ℤ) ^ j else 0) =
        ∑ r ∈ Finset.range m, (10 : ℤ) ^ (2 * r + 1) := by
      have hcongr : (∑ j ∈ Finset.range (2 * m), if f0 (2 * m) (j : ℤ) then (10 : ℤ) ^ j else 0) =
          ∑ j ∈ Finset.range (2 * m), if j % 2 = 1 then (10 : ℤ) ^ j else 0 := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjlt : j < 2 * m := Finset.mem_range.mp hj
        rw [f0_even_eval m j (by omega)]
        have hne : j ≠ 2 * m := by omega
        simp [hne]
      rw [hcongr]
      clear hcongr htop
      generalize m = n
      induction n with
      | zero => simp
      | succ k ih =>
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ, ih,
          Finset.sum_range_succ]
        have hev : ¬ (2 * k) % 2 = 1 := by omega
        have hodd : (2 * k + 1) % 2 = 1 := by omega
        rw [if_neg hev, if_pos hodd]
        ring
    rw [hsum, mul_add, odd_pow_sum]
    ring

private lemma a_odd (m : ℕ) :
    a (2 * m + 1) = a (2 * m) + (10 : ℤ) ^ (2 * m + 1) := by
  rw [a_eq_sum_f0 (2 * m + 1), a_eq_sum_f0 (2 * m), Finset.sum_range_succ]
  have htop : f0 (2 * m + 1) ((2 * m + 1 : ℕ) : ℤ) = true := by
    simp only [f0, Nat.abs_cast, decide_eq_true_eq]; left; trivial
  rw [htop, if_pos rfl]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjle : j ≤ 2 * m := by simp [Finset.mem_range] at hj; omega
  have heq : f0 (2 * m + 1) (j : ℤ) = f0 (2 * m) (j : ℤ) := by
    simp only [f0, Nat.abs_cast, decide_eq_decide]
    omega
  rw [heq]

private lemma a_0 : a 0 = 1 := by
  rw [a_eq_sum_f0]; decide

private lemma a_1 : a 1 = 11 := by
  rw [a_eq_sum_f0]; decide

private lemma a_closed (n : ℕ) :
    (a n : ℚ) = (-200 - 9 * (-10 : ℚ) ^ n + 2189 * (10 : ℚ) ^ n) / 1980 := by
  rcases n with _ | _ | n'
  · rw [a_0]; norm_num
  · rw [a_1]; norm_num
  · rcases Nat.even_or_odd (n' + 2) with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hm2 : n' + 2 = 2 * m := by omega
      have hm0 : m ≠ 0 := by omega
      rw [hm2]
      have h99_int := a_even m
      rw [if_neg hm0] at h99_int
      have h99 : (99 : ℚ) * (a (2 * m) : ℚ) = 109 * (10 : ℚ) ^ (2 * m) - 10 := by
        exact_mod_cast h99_int
      have hneg : (-10 : ℚ) ^ (2 * m) = (10 : ℚ) ^ (2 * m) := by
        rw [pow_mul, pow_mul]; norm_num
      rw [hneg]
      linarith
    · have hm2 : n' + 2 = 2 * m + 1 := by omega
      have hm0 : m ≠ 0 := by omega
      rw [hm2]
      have hodd : (a (2 * m + 1) : ℚ) = (a (2 * m) : ℚ) + (10 : ℚ) ^ (2 * m + 1) := by
        exact_mod_cast a_odd m
      have h99_int := a_even m
      rw [if_neg hm0] at h99_int
      have h99 : (99 : ℚ) * (a (2 * m) : ℚ) = 109 * (10 : ℚ) ^ (2 * m) - 10 := by
        exact_mod_cast h99_int
      have hneg : (-10 : ℚ) ^ (2 * m + 1) = -10 * (10 : ℚ) ^ (2 * m) := by
        rw [pow_succ, pow_mul, show (-10 : ℚ) ^ 2 = (10 : ℚ) ^ 2 by norm_num, ← pow_mul]; ring
      have hpos : (10 : ℚ) ^ (2 * m + 1) = 10 * (10 : ℚ) ^ (2 * m) := by
        rw [pow_succ]; ring
      rw [hodd, hneg, hpos]
      linarith

private lemma a_rec (n : ℕ) (hn : 3 ≤ n) :
    (a n : ℚ) = a (n - 1) + 100 * a (n - 2) - 100 * a (n - 3) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  rw [a_closed (k + 3), a_closed (k + 2), a_closed (k + 1), a_closed k]
  ring

private lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 10 * X) * (1 + 10 * X) : PowerSeries ℚ) =
      1 + 10 * X - X ^ 2 := by
  set A : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  have hlhs : A * ((1 - X) * (1 - 10 * X) * (1 + 10 * X) : PowerSeries ℚ) =
      A - A * X ^ 1 - PowerSeries.C (100 : ℚ) * (A * X ^ 2) +
        PowerSeries.C (100 : ℚ) * (A * X ^ 3) := by
    simp only [map_ofNat]
    ring
  have hrhs : (1 + 10 * X - X ^ 2 : PowerSeries ℚ) =
      PowerSeries.C (1 : ℚ) + PowerSeries.C (10 : ℚ) * X -
        PowerSeries.C (1 : ℚ) * X ^ 2 := by
    simp only [map_one, map_ofNat]
    ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_C, PowerSeries.coeff_X, PowerSeries.coeff_mk, A]
  by_cases hn : 3 ≤ n
  · have hrec := a_rec n hn
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n - 2 ≠ 0 by omega,
      ite_true, ite_false]
    linarith
  · have h0 : (a 0 : ℚ) = 1 := by rw [a_closed 0]; norm_num
    have h1 : (a 1 : ℚ) = 11 := by rw [a_closed 1]; norm_num
    have h2 : (a 2 : ℚ) = 110 := by rw [a_closed 2]; norm_num
    have hs21 : (2 - 1 : ℕ) = 1 := rfl
    interval_cases n <;>
      simp only [Nat.sub_self, hs21, h0, h1, h2] <;>
      norm_num

end OMA.Proof_oeis_a277952

theorem OMA.solution : type_of% @OMA.S_oeis_a277952.main :=
  ⟨OMA.Proof_oeis_a277952.gf_eq,
   OMA.Proof_oeis_a277952.a_rec,
   OMA.Proof_oeis_a277952.a_closed⟩
