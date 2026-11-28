import OMAStatements.S_oeis_a265724

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: under Rule 1 a cell is ON next iff it and both neighbours are OFF. By induction,
-- row 2m is the single cell 0 and row 2m+1 is everything but the cells -1, 0, 1. So row k has
-- 2k OFF cells (k even) or 3 (k odd), and the closed form follows by induction on n; the
-- recurrence and the generating function follow from it coefficientwise.

namespace OMA.S_oeis_a265724

open PowerSeries

lemma rule1 (l c r : Bool) : ruleOut 1 l c r = (!l && !c && !r) := by
  cases l <;> cases c <;> cases r <;> decide

lemma rows (m : ℕ) :
    (∀ i : ℤ, cell 1 (2 * m) i = decide (i = 0)) ∧
    (∀ i : ℤ, cell 1 (2 * m + 1) i = decide (i ≠ -1 ∧ i ≠ 0 ∧ i ≠ 1)) := by
  have hstep : ∀ m : ℕ, (∀ i : ℤ, cell 1 (2 * m) i = decide (i = 0)) →
      ∀ i : ℤ, cell 1 (2 * m + 1) i = decide (i ≠ -1 ∧ i ≠ 0 ∧ i ≠ 1) := by
    intro m h i
    show ruleOut 1 (cell 1 (2 * m) (i - 1)) (cell 1 (2 * m) i) (cell 1 (2 * m) (i + 1)) = _
    rw [h, h, h, rule1]
    by_cases h1 : i = -1
    · subst h1; decide
    by_cases h2 : i = 0
    · subst h2; decide
    by_cases h3 : i = 1
    · subst h3; decide
    have h4 : i - 1 ≠ 0 := by omega
    have h5 : i + 1 ≠ 0 := by omega
    simp [h1, h2, h3, h4, h5]
  induction m with
  | zero =>
    have h0 : ∀ i : ℤ, cell 1 (2 * 0) i = decide (i = 0) := fun i => rfl
    exact ⟨h0, hstep 0 h0⟩
  | succ m ih =>
    have he : ∀ i : ℤ, cell 1 (2 * (m + 1)) i = decide (i = 0) := by
      intro i
      show ruleOut 1 (cell 1 (2 * m + 1) (i - 1)) (cell 1 (2 * m + 1) i)
        (cell 1 (2 * m + 1) (i + 1)) = _
      rw [ih.2, ih.2, ih.2, rule1]
      by_cases h0 : i = 0
      · subst h0; decide
      by_cases h1 : i = -1
      · subst h1; decide
      by_cases h2 : i = 1
      · subst h2; decide
      simp [h0, h1, h2] <;> omega
    exact ⟨he, hstep (m + 1) he⟩

lemma off (k : ℕ) :
    ((2 * k + 1 : ℤ) - onCount 1 k) = if k % 2 = 0 then 2 * (k : ℤ) else 3 := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · have hs : (∑ j ∈ Finset.range (2 * (2 * m) + 1),
        if cell 1 (2 * m) ((j : ℤ) - ((2 * m : ℕ) : ℤ)) then 1 else 0) =
        ∑ j ∈ Finset.range (2 * (2 * m) + 1), if j = 2 * m then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [(rows m).1]
      congr 1
      apply propext
      simp only [decide_eq_true_eq]
      push_cast
      omega
    simp only [onCount]
    rw [hs, Finset.sum_ite_eq']
    simp only [Finset.mem_range, show 2 * m < 2 * (2 * m) + 1 by omega, if_true,
      show 2 * m % 2 = 0 by omega]
    push_cast; ring
  · have hs : (∑ j ∈ Finset.range (2 * (2 * m + 1) + 1),
        if cell 1 (2 * m + 1) ((j : ℤ) - ((2 * m + 1 : ℕ) : ℤ)) then 1 else 0) =
        ∑ j ∈ Finset.range (2 * (2 * m + 1) + 1),
          if j ∈ ({2 * m, 2 * m + 1, 2 * m + 2} : Finset ℕ) then 0 else 1 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [(rows m).2]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases h : j = 2 * m ∨ j = 2 * m + 1 ∨ j = 2 * m + 2
      · rw [if_pos h, if_neg]
        simp only [decide_eq_true_eq, not_and, not_not]
        push_cast
        omega
      · rw [if_neg h, if_pos]
        simp only [decide_eq_true_eq]
        push_cast
        omega
    simp only [onCount]
    rw [hs, Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul,
      mul_one, Finset.filter_not, Finset.card_sdiff]
    rw [show (_ ∩ _ : Finset ℕ) = ({2 * m, 2 * m + 1, 2 * m + 2} : Finset ℕ) from by
      ext j; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
        Finset.mem_singleton]; omega]
    rw [Finset.card_range, Finset.card_eq_three.mpr
      ⟨2 * m, 2 * m + 1, 2 * m + 2, by omega, by omega, by omega, rfl⟩]
    rw [if_neg (show ¬ (2 * m + 1) % 2 = 0 by omega)]
    push_cast
    omega

theorem closed (n : ℕ) :
    (a n : ℚ) = 1 / 2 * ((n : ℚ) ^ 2 + (-1 : ℚ) ^ n * (n : ℚ) + 4 * (n : ℚ) - (-1 : ℚ) ^ n + 1) := by
  induction n with
  | zero => simp [a, onCount, cell]
  | succ n ih =>
    have hs : a (n + 1) = a n + ((2 * (n + 1 : ℕ) + 1 : ℤ) - onCount 1 (n + 1)) := by
      simp only [a]; rw [Finset.sum_range_succ]
    rw [hs, off]
    push_cast
    rw [ih]
    rcases Nat.even_or_odd n with he | ho
    · have : ¬ (n + 1) % 2 = 0 := by have := Nat.even_iff.1 he; omega
      have hp : (-1 : ℚ) ^ n = 1 := he.neg_one_pow
      simp only [this, if_false]
      push_cast; rw [pow_succ (-1 : ℚ) n, hp]; ring
    · have : (n + 1) % 2 = 0 := by have := Nat.odd_iff.1 ho; omega
      have hp : (-1 : ℚ) ^ n = -1 := ho.neg_one_pow
      simp only [this, if_true]
      push_cast; rw [pow_succ (-1 : ℚ) n, hp]; ring

theorem even_form (n : ℕ) (he : Even n) : (a n : ℚ) = 1 / 2 * ((n : ℚ) ^ 2 + 5 * (n : ℚ)) := by
  rw [closed, he.neg_one_pow]; ring

theorem odd_form (n : ℕ) (ho : Odd n) :
    (a n : ℚ) = 1 / 2 * ((n : ℚ) ^ 2 + 3 * (n : ℚ) + 2) := by
  rw [closed, ho.neg_one_pow]; ring

theorem recur (n : ℕ) (hn : 5 ≤ n) :
    (a n : ℚ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
    show m + 5 - 5 = m by omega]
  simp only [closed]
  push_cast
  rw [pow_add, pow_add, pow_add, pow_add, pow_add]
  ring

theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) ^ 2 : PowerSeries ℚ) =
    X * (3 + 4 * X - 3 * X ^ 2) := by
  have hD : ((1 - X) ^ 3 * (1 + X) ^ 2 : ℚ⟦X⟧) =
      1 - X ^ 1 - (X ^ 2 + X ^ 2) + (X ^ 3 + X ^ 3) + X ^ 4 - X ^ 5 := by ring
  have hN : (X * (3 + 4 * X - 3 * X ^ 2) : ℚ⟦X⟧) =
      (X ^ 1 + X ^ 1 + X ^ 1) + (X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2) - (X ^ 3 + X ^ 3 + X ^ 3) := by
    ring
  rw [hD, hN]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mul_X_pow', coeff_mk,
    coeff_X_pow]
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> simp [closed] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have := recur (m + 5) (by omega)
    rw [if_pos (show 1 ≤ m + 5 by omega), if_pos (show 2 ≤ m + 5 by omega),
      if_pos (show 3 ≤ m + 5 by omega), if_pos (show 4 ≤ m + 5 by omega),
      if_pos (show 5 ≤ m + 5 by omega)]
    simp only [show m + 5 ≠ 1 by omega, show m + 5 ≠ 2 by omega, show m + 5 ≠ 3 by omega,
      if_false]
    linarith

end OMA.S_oeis_a265724

theorem OMA.solution : type_of% @OMA.S_oeis_a265724.main :=
  ⟨OMA.S_oeis_a265724.closed, OMA.S_oeis_a265724.even_form, OMA.S_oeis_a265724.odd_form,
    OMA.S_oeis_a265724.recur, OMA.S_oeis_a265724.gf⟩
