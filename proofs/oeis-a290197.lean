import OMAStatements.S_oeis_a290197

namespace OMA.S_oeis_a290197

theorem state_succ (t : ℕ) (x y : ℤ) : state (t + 1) x y =
    Nat.testBit 721 ((state t x y).toNat + 2 * ((state t (x - 1) y).toNat +
      (state t (x + 1) y).toNat + (state t x (y - 1)).toNat + (state t x (y + 1)).toNat)) := by
  rw [state]

theorem state_zero (x y : ℤ) : state 0 x y = decide (x = 0 ∧ y = 0) := by
  rw [state]

theorem state_one (x y : ℤ) : state 1 x y =
    decide (¬ (-1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 ∧ (x = 0 ∨ y = 0))) := by
  rw [state_succ 0 x y]
  simp only [state_zero]
  cases h0 : decide (x = 0 ∧ y = 0) <;> cases h1 : decide (x - 1 = 0 ∧ y = 0) <;>
    cases h2 : decide (x + 1 = 0 ∧ y = 0) <;> cases h3 : decide (x = 0 ∧ y - 1 = 0) <;>
    cases h4 : decide (x = 0 ∧ y + 1 = 0) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h0 h1 h2 h3 h4 <;>
    by_cases hq : (-1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 ∧ (x = 0 ∨ y = 0)) <;>
    (try simp only [hq, not_true, not_false_eq_true, decide_true, decide_false]) <;>
    first | decide | (exfalso; omega)

theorem state_two (x y : ℤ) : state 2 x y = decide (¬ ((x = 1 ∨ x = -1) ∧ (y = 1 ∨ y = -1))) := by
  rw [state_succ 1 x y]
  simp only [state_one]
  cases h0 : decide (¬ (-1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 ∧ (x = 0 ∨ y = 0))) <;>
    cases h1 : decide (¬ (-1 ≤ x - 1 ∧ x - 1 ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 ∧ (x - 1 = 0 ∨ y = 0))) <;>
    cases h2 : decide (¬ (-1 ≤ x + 1 ∧ x + 1 ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 ∧ (x + 1 = 0 ∨ y = 0))) <;>
    cases h3 : decide (¬ (-1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y - 1 ∧ y - 1 ≤ 1 ∧ (x = 0 ∨ y - 1 = 0))) <;>
    cases h4 : decide (¬ (-1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y + 1 ∧ y + 1 ≤ 1 ∧ (x = 0 ∨ y + 1 = 0))) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h0 h1 h2 h3 h4 <;>
    by_cases hq : ((x = 1 ∨ x = -1) ∧ (y = 1 ∨ y = -1)) <;>
    (try simp only [hq, not_true, not_false_eq_true, decide_true, decide_false]) <;>
    first | decide | (exfalso; omega)

theorem state_three (x y : ℤ) : state 3 x y = decide (¬ (-1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 ∧ ¬ (x = 0 ∧ y = 0))) := by
  rw [state_succ 2 x y]
  simp only [state_two]
  cases h0 : decide (¬ ((x = 1 ∨ x = -1) ∧ (y = 1 ∨ y = -1))) <;>
    cases h1 : decide (¬ ((x - 1 = 1 ∨ x - 1 = -1) ∧ (y = 1 ∨ y = -1))) <;>
    cases h2 : decide (¬ ((x + 1 = 1 ∨ x + 1 = -1) ∧ (y = 1 ∨ y = -1))) <;>
    cases h3 : decide (¬ ((x = 1 ∨ x = -1) ∧ (y - 1 = 1 ∨ y - 1 = -1))) <;>
    cases h4 : decide (¬ ((x = 1 ∨ x = -1) ∧ (y + 1 = 1 ∨ y + 1 = -1))) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h0 h1 h2 h3 h4 <;>
    by_cases hq : (-1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 ∧ ¬ (x = 0 ∧ y = 0)) <;>
    (try simp only [hq, not_true, not_false_eq_true, decide_true, decide_false]) <;>
    first | decide | (exfalso; omega)

theorem state_four (x y : ℤ) : state 4 x y = decide (¬ (x = 0 ∧ y = 0)) := by
  rw [state_succ 3 x y]
  simp only [state_three]
  cases h0 : decide (¬ (-1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 ∧ ¬ (x = 0 ∧ y = 0))) <;>
    cases h1 : decide (¬ (-1 ≤ x - 1 ∧ x - 1 ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 ∧ ¬ (x - 1 = 0 ∧ y = 0))) <;>
    cases h2 : decide (¬ (-1 ≤ x + 1 ∧ x + 1 ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 ∧ ¬ (x + 1 = 0 ∧ y = 0))) <;>
    cases h3 : decide (¬ (-1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y - 1 ∧ y - 1 ≤ 1 ∧ ¬ (x = 0 ∧ y - 1 = 0))) <;>
    cases h4 : decide (¬ (-1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y + 1 ∧ y + 1 ≤ 1 ∧ ¬ (x = 0 ∧ y + 1 = 0))) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h0 h1 h2 h3 h4 <;>
    by_cases hq : (x = 0 ∧ y = 0) <;>
    (try simp only [hq, not_true, not_false_eq_true, decide_true, decide_false]) <;>
    first | decide | (exfalso; omega)

theorem state_ge_four (t : ℕ) (ht : 4 ≤ t) (x y : ℤ) : state t x y = decide (¬ (x = 0 ∧ y = 0)) := by
  induction t, ht using Nat.le_induction generalizing x y with
  | base => exact state_four x y
  | succ t _ ih =>
  rw [state_succ t x y]
  simp only [ih]
  cases h0 : decide (¬ (x = 0 ∧ y = 0)) <;>
    cases h1 : decide (¬ (x - 1 = 0 ∧ y = 0)) <;>
    cases h2 : decide (¬ (x + 1 = 0 ∧ y = 0)) <;>
    cases h3 : decide (¬ (x = 0 ∧ y - 1 = 0)) <;>
    cases h4 : decide (¬ (x = 0 ∧ y + 1 = 0)) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h0 h1 h2 h3 h4 <;>
    by_cases hq : (x = 0 ∧ y = 0) <;>
    (try simp only [hq, not_true, not_false_eq_true, decide_true, decide_false]) <;>
    first | decide | (exfalso; omega)

theorem diag (n : ℕ) (hn : 4 ≤ n) (k : ℕ) : state n (k : ℤ) (k : ℤ) = decide (k ≠ 0) := by
  rw [state_ge_four n hn]
  simp

end OMA.S_oeis_a290197

open OMA.S_oeis_a290197

theorem OMA.solution : type_of% @OMA.S_oeis_a290197.main := by
  intro n hn
  unfold a
  simp only [diag n hn]
  rw [Finset.sum_range_succ']
  simp only [ne_eq, Nat.add_one_ne_zero, not_false_eq_true, decide_true, if_true,
    decide_eq_true_eq, not_true, if_false, add_zero]
  have e : ∀ i ∈ Finset.range n, 10 ^ (n - (i + 1)) = 10 ^ (n - 1 - i) := by
    intro i _; congr 1; omega
  rw [Finset.sum_congr rfl e, Finset.sum_range_reflect (fun j => 10 ^ j) n]
  push_cast
  rw [geom_sum_eq (by norm_num : (10:ℚ) ≠ 1)]
  norm_num
