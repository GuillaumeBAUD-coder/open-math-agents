import OMAStatements.S_oeis_a267538

namespace OMA.S_oeis_a267538




/-- One step from a single ON cell (relative position `d`). -/
lemma step0 (d : ℤ) :
    rule (decide (d - 1 = 0)) (decide (d = 0)) (decide (d + 1 = 0)) = decide (d ≠ 1) := by
  rcases (by omega : d ≤ -2 ∨ d = -1 ∨ d = 0 ∨ d = 1 ∨ d = 2 ∨ 3 ≤ d) with h | h | h | h | h | h
  · rw [decide_eq_false (by omega : ¬ d - 1 = 0), decide_eq_false (by omega : ¬ d = 0),
      decide_eq_false (by omega : ¬ d + 1 = 0), decide_eq_true (by omega : d ≠ 1)]; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_false (by omega : ¬ d - 1 = 0), decide_eq_false (by omega : ¬ d = 0),
      decide_eq_false (by omega : ¬ d + 1 = 0), decide_eq_true (by omega : d ≠ 1)]; decide

/-- One step from a single OFF cell at relative position 0 on an ON background. -/
lemma step1 (d : ℤ) :
    rule (decide (d - 1 ≠ 0)) (decide (d ≠ 0)) (decide (d + 1 ≠ 0)) = decide (d ≠ -1 ∧ d ≠ 0) := by
  rcases (by omega : d ≤ -2 ∨ d = -1 ∨ d = 0 ∨ d = 1 ∨ 2 ≤ d) with h | h | h | h | h
  · rw [decide_eq_true (by omega : d - 1 ≠ 0), decide_eq_true (by omega : d ≠ 0),
      decide_eq_true (by omega : d + 1 ≠ 0), decide_eq_true (by omega : d ≠ -1 ∧ d ≠ 0)]; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_true (by omega : d - 1 ≠ 0), decide_eq_true (by omega : d ≠ 0),
      decide_eq_true (by omega : d + 1 ≠ 0), decide_eq_true (by omega : d ≠ -1 ∧ d ≠ 0)]; decide

/-- One step from an OFF pair at relative positions 0, 1 on an ON background. -/
lemma step2 (d : ℤ) :
    rule (decide (d - 1 ≠ 0 ∧ d - 1 ≠ 1)) (decide (d ≠ 0 ∧ d ≠ 1)) (decide (d + 1 ≠ 0 ∧ d + 1 ≠ 1)) =
      decide (d ≠ -1 ∧ d ≠ 0) := by
  rcases (by omega : d ≤ -2 ∨ d = -1 ∨ d = 0 ∨ d = 1 ∨ d = 2 ∨ 3 ≤ d) with h | h | h | h | h | h
  · rw [decide_eq_true (by omega : d - 1 ≠ 0 ∧ d - 1 ≠ 1), decide_eq_true (by omega : d ≠ 0 ∧ d ≠ 1),
      decide_eq_true (by omega : d + 1 ≠ 0 ∧ d + 1 ≠ 1),
      decide_eq_true (by omega : d ≠ -1 ∧ d ≠ 0)]; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_true (by omega : d - 1 ≠ 0 ∧ d - 1 ≠ 1), decide_eq_true (by omega : d ≠ 0 ∧ d ≠ 1),
      decide_eq_true (by omega : d + 1 ≠ 0 ∧ d + 1 ≠ 1),
      decide_eq_true (by omega : d ≠ -1 ∧ d ≠ 0)]; decide

lemma s1 (i : ℤ) : state 1 i = decide (i ≠ 1) := step0 i

lemma s2 (i : ℤ) : state 2 i = decide (i ≠ 0 ∧ i ≠ 1) := by
  show rule (state 1 (i - 1)) (state 1 i) (state 1 (i + 1)) = _
  rw [s1, s1, s1]
  have h := step1 (i - 1)
  rw [show decide (i - 1 ≠ 1) = decide (i - 1 - 1 ≠ 0) from decide_eq_decide.mpr (by omega),
    show decide (i ≠ 1) = decide (i - 1 ≠ 0) from decide_eq_decide.mpr (by omega),
    show decide (i + 1 ≠ 1) = decide (i - 1 + 1 ≠ 0) from decide_eq_decide.mpr (by omega), h]
  exact decide_eq_decide.mpr (by omega)

/-- From time 2 on, the OFF cells are exactly `2 - t` and `3 - t`. -/
lemma s_ge2 (t : ℕ) (ht : 2 ≤ t) (i : ℤ) :
    state t i = decide (i - (2 - (t : ℤ)) ≠ 0 ∧ i - (2 - (t : ℤ)) ≠ 1) := by
  induction t, ht using Nat.le_induction generalizing i with
  | base =>
    rw [s2]; congr 1; apply propext; push_cast; omega
  | succ t _ ih =>
    show rule (state t (i - 1)) (state t i) (state t (i + 1)) = _
    rw [ih, ih, ih]
    have h := step2 (i - (2 - (t : ℤ)))
    rw [show i - 1 - (2 - (t : ℤ)) = i - (2 - (t : ℤ)) - 1 by ring,
      show i + 1 - (2 - (t : ℤ)) = i - (2 - (t : ℤ)) + 1 by ring, h]
    congr 1; apply propext; push_cast; omega

/-- The middle column. -/
lemma col (t : ℕ) : state t 0 = decide (t ≠ 2 ∧ t ≠ 3) := by
  rcases (by omega : t = 0 ∨ t = 1 ∨ 2 ≤ t) with h | h | h
  · subst h; decide
  · subst h; rw [s1]; decide
  · rw [s_ge2 t h]
    congr 1; apply propext; omega

lemma a_succ (n : ℕ) : a (n + 1) = 10 * a n + (if n + 1 = 2 ∨ n + 1 = 3 then 0 else 1) := by
  unfold a
  rw [Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun t ht => ?_
    have ht' := Finset.mem_range.mp ht
    split_ifs
    · rw [show n + 1 - t = (n - t) + 1 by omega, pow_succ]; ring
    · simp
  · rw [col]
    by_cases h : n + 1 = 2 ∨ n + 1 = 3
    · rw [if_pos h, decide_eq_false (by omega)]; simp
    · rw [if_neg h, decide_eq_true (by omega)]; simp

lemma a_small : a 0 = 1 ∧ a 1 = 11 ∧ a 2 = 110 ∧ a 3 = 1100 ∧ a 4 = 11001 := by
  have h0 : a 0 = 1 := by decide
  have h1 := a_succ 0
  have h2 := a_succ 1
  have h3 := a_succ 2
  have h4 := a_succ 3
  norm_num [h0] at h1 h2 h3 h4
  omega

/-- Barker's recurrence with Keller's range: `a(n) = 11 a(n-1) - 10 a(n-2)` for `n > 4`. -/
theorem recurrence (n : ℕ) (hn : 4 < n) : (a n : ℤ) = 11 * a (n - 1) - 10 * a (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 := a_succ (m + 1)
  have h2 := a_succ m
  simp only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  rw [if_neg (by omega)] at h1
  rw [if_neg (by omega)] at h2
  rw [h1, h2]
  push_cast
  ring

/-- Keller's formula: `a(n) = floor(9901 * 10^n / 9000)` for all `n ≥ 0`. -/
theorem keller (n : ℕ) : a n = 9901 * 10 ^ n / 9000 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := a_small
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n) with h | h | h | h
  · subst h; rw [h0]; norm_num
  · subst h; rw [h1]; norm_num
  · subst h; rw [h2]; norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have hk : 9 * a (k + 3) + 1 = 9901 * 10 ^ k := by
      induction k with
      | zero => rw [h3]; norm_num
      | succ k ih =>
        rw [show k + 1 + 3 = (k + 3) + 1 by ring, a_succ, if_neg (by omega), pow_succ]
        omega
    rw [show 9901 * 10 ^ (k + 3) = 9000 * a (k + 3) + 1000 by rw [pow_add]; omega]
    omega

open PowerSeries in
/-- Barker's g.f. `(1 - x^2 + x^4)/((1 - x)(1 - 10x))`, as an identity in `ℚ⟦X⟧`. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) =
    (1 - X ^ 2 + X ^ 4) * ((1 - X) * (1 - 10 * X))⁻¹ := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))
  have hden : constantCoeff ((1 - X) * (1 - 10 * X) : ℚ⟦X⟧) ≠ 0 := by simp
  have key : A * ((1 - X) * (1 - 10 * X)) = 1 - X ^ 2 + X ^ 4 := by
    have e1 : A * ((1 - X) * (1 - 10 * X)) =
        A - (C (11 : ℚ)) * (A * X ^ 1) + (C (10 : ℚ)) * (A * X ^ 2) := by
      simp only [map_ofNat]; ring
    rw [e1]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_one, coeff_X_pow, A,
      coeff_mk]
    obtain ⟨h0, h1, h2, h3, h4⟩ := a_small
    rcases Nat.lt_or_ge n 5 with hn | hn
    · interval_cases n <;> simp [h0, h1, h2, h3, h4] <;> norm_num
    · rw [if_pos (by omega), if_pos (by omega)]
      have hr := recurrence n (by omega)
      simp only [show n ≠ 0 by omega, show n ≠ 2 by omega, show n ≠ 4 by omega, if_false]
      have : (a n : ℚ) = 11 * a (n - 1) - 10 * a (n - 2) := by exact_mod_cast hr
      rw [this]; ring
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]

end OMA.S_oeis_a267538

theorem OMA.solution : type_of% @OMA.S_oeis_a267538.main :=
  ⟨fun n hn => OMA.S_oeis_a267538.recurrence n hn, OMA.S_oeis_a267538.gf,
    fun n => OMA.S_oeis_a267538.keller n⟩
