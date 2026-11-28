import OMAStatements.S_oeis_a267044

namespace OMA.S_oeis_a267044

open PowerSeries






/-- Barker's conjectures. -/
def Conjecture : Prop :=
  (∀ n : ℕ, 1 < n → (a n : ℚ) = (-550 + 450 * (-1) ^ n + 9901 * 10 ^ n) / 9900) ∧
  (∀ n : ℕ, 4 < n → (a n : ℤ) = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3)) ∧
  A = (1 - X ^ 2 + X ^ 4) * ((1 - X) * (1 + X) * (1 - 10 * X))⁻¹

/-- Odd rows from row 3 on: OFF exactly on `[-1, 1]`. -/
def pO : ℤ → Bool := fun x => decide (x < -1 ∨ 1 < x)
/-- Even rows from row 4 on: ON exactly on `[-2, 2]`. -/
def pE : ℤ → Bool := fun x => decide (-2 ≤ x ∧ x ≤ 2)

theorem state_one : state 91 1 = fun x => decide (x ≠ 0) := by
  funext x
  simp only [state, step]
  rcases (show x ≤ -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ 2 ≤ x by omega) with h | h | h | h | h
  · rw [decide_eq_false (show x - 1 ≠ 0 by omega), decide_eq_false (show x ≠ 0 by omega),
      decide_eq_false (show x + 1 ≠ 0 by omega), decide_eq_true (show x ≠ 0 by omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_false (show x - 1 ≠ 0 by omega), decide_eq_false (show x ≠ 0 by omega),
      decide_eq_false (show x + 1 ≠ 0 by omega), decide_eq_true (show x ≠ 0 by omega)]
    decide

theorem state_two : state 91 2 = fun x => decide (x = -1 ∨ x = 1) := by
  funext x
  rw [show state 91 2 = step 91 (state 91 1) from rfl, state_one]
  simp only [step]
  rcases (show x ≤ -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ 2 ≤ x by omega) with h | h | h | h | h
  · rw [decide_eq_true (show x - 1 ≠ 0 by omega), decide_eq_true (show x ≠ 0 by omega),
      decide_eq_true (show x + 1 ≠ 0 by omega), decide_eq_false (show ¬(x = -1 ∨ x = 1) by omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_true (show x - 1 ≠ 0 by omega), decide_eq_true (show x ≠ 0 by omega),
      decide_eq_true (show x + 1 ≠ 0 by omega), decide_eq_false (show ¬(x = -1 ∨ x = 1) by omega)]
    decide

theorem state_three : state 91 3 = pO := by
  funext x
  rw [show state 91 3 = step 91 (state 91 2) from rfl, state_two]
  simp only [step, pO]
  rcases (show x ≤ -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ 3 ≤ x by omega) with
    h | h | h | h | h | h | h
  · rw [decide_eq_false (show ¬(x - 1 = -1 ∨ x - 1 = 1) by omega),
      decide_eq_false (show ¬(x = -1 ∨ x = 1) by omega),
      decide_eq_false (show ¬(x + 1 = -1 ∨ x + 1 = 1) by omega),
      decide_eq_true (show x < -1 ∨ 1 < x by omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_false (show ¬(x - 1 = -1 ∨ x - 1 = 1) by omega),
      decide_eq_false (show ¬(x = -1 ∨ x = 1) by omega),
      decide_eq_false (show ¬(x + 1 = -1 ∨ x + 1 = 1) by omega),
      decide_eq_true (show x < -1 ∨ 1 < x by omega)]
    decide

theorem step_pO : step 91 pO = pE := by
  funext x
  simp only [step, pO, pE]
  rcases (show x ≤ -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ 4 ≤ x by
      omega) with h | h | h | h | h | h | h | h | h
  · rw [decide_eq_true (show x - 1 < -1 ∨ 1 < x - 1 by omega),
      decide_eq_true (show x < -1 ∨ 1 < x by omega),
      decide_eq_true (show x + 1 < -1 ∨ 1 < x + 1 by omega),
      decide_eq_false (show ¬(-2 ≤ x ∧ x ≤ 2) by omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_true (show x - 1 < -1 ∨ 1 < x - 1 by omega),
      decide_eq_true (show x < -1 ∨ 1 < x by omega),
      decide_eq_true (show x + 1 < -1 ∨ 1 < x + 1 by omega),
      decide_eq_false (show ¬(-2 ≤ x ∧ x ≤ 2) by omega)]
    decide

theorem step_pE : step 91 pE = pO := by
  funext x
  simp only [step, pO, pE]
  rcases (show x ≤ -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ 4 ≤ x by
      omega) with h | h | h | h | h | h | h | h | h
  · rw [decide_eq_false (show ¬(-2 ≤ x - 1 ∧ x - 1 ≤ 2) by omega),
      decide_eq_false (show ¬(-2 ≤ x ∧ x ≤ 2) by omega),
      decide_eq_false (show ¬(-2 ≤ x + 1 ∧ x + 1 ≤ 2) by omega),
      decide_eq_true (show x < -1 ∨ 1 < x by omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_false (show ¬(-2 ≤ x - 1 ∧ x - 1 ≤ 2) by omega),
      decide_eq_false (show ¬(-2 ≤ x ∧ x ≤ 2) by omega),
      decide_eq_false (show ¬(-2 ≤ x + 1 ∧ x + 1 ≤ 2) by omega),
      decide_eq_true (show x < -1 ∨ 1 < x by omega)]
    decide

theorem state_late (k : ℕ) : state 91 (2 * k + 3) = pO ∧ state 91 (2 * k + 4) = pE := by
  induction k with
  | zero =>
    refine ⟨state_three, ?_⟩
    rw [show state 91 (2 * 0 + 4) = step 91 (state 91 3) from rfl, state_three, step_pO]
  | succ k ih =>
    have h1 : state 91 (2 * (k + 1) + 3) = pO := by
      rw [show 2 * (k + 1) + 3 = 2 * k + 4 + 1 by ring,
        show state 91 (2 * k + 4 + 1) = step 91 (state 91 (2 * k + 4)) from rfl, ih.2, step_pE]
    refine ⟨h1, ?_⟩
    rw [show state 91 (2 * (k + 1) + 4) = step 91 (state 91 (2 * (k + 1) + 3)) from rfl, h1,
      step_pO]

/-- The centre column from row 3 on: 1 on even rows, 0 on odd rows. -/
theorem c_late (n : ℕ) (hn : 3 ≤ n) : c n = if Even n then 1 else 0 := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    rw [if_pos ⟨_, hm⟩, c, show n = 2 * k + 4 by omega, (state_late k).2]
    decide
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [if_neg (Nat.not_even_iff_odd.2 ⟨_, hm⟩), c, show n = 2 * k + 3 by omega,
      (state_late k).1]
    decide

theorem a_succ (n : ℕ) : a (n + 1) = 10 * a n + c (n + 1) := by
  rw [a, a, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [show n + 1 - k = n - k + 1 by omega, pow_succ]
  ring

theorem c0 : c 0 = 1 := by decide
theorem c1 : c 1 = 0 := by rw [c, state_one]; decide
theorem c2 : c 2 = 0 := by rw [c, state_two]; decide

theorem a0 : a 0 = 1 := by rw [a]; simp [c0]
theorem a1 : a 1 = 10 := by rw [a_succ, a0, c1]
theorem a2 : a 2 = 100 := by rw [a_succ, a1, c2]

/-- `9900 a(n) = 9901*10^n + 450*(-1)^n - 550` for `n >= 2`. -/
theorem closed (n : ℕ) (hn : 2 ≤ n) :
    9900 * (a n : ℤ) = 9901 * 10 ^ n + 450 * (-1) ^ n - 550 := by
  induction n, hn using Nat.le_induction with
  | base => rw [a2]; norm_num
  | succ n hn ih =>
    rw [a_succ, c_late (n + 1) (by omega)]
    push_cast
    have p10 : (10 : ℤ) ^ (n + 1) = 10 ^ n * 10 := pow_succ _ _
    rcases Nat.even_or_odd n with he | ho
    · have he' : ¬ Even (n + 1) := fun h => (Nat.not_even_iff_odd.2 he.add_one) h
      have q0 : ((-1 : ℤ)) ^ n = 1 := Even.neg_one_pow he
      have q1 : ((-1 : ℤ)) ^ (n + 1) = -1 := by rw [pow_succ, q0]; ring
      rw [if_neg he']
      push_cast
      rw [p10, q1]
      rw [q0] at ih
      linarith
    · have ho' : Even (n + 1) := ho.add_one
      have q0 : ((-1 : ℤ)) ^ n = -1 := Odd.neg_one_pow ho
      have q1 : ((-1 : ℤ)) ^ (n + 1) = 1 := by rw [pow_succ, q0]; ring
      rw [if_pos ho']
      push_cast
      rw [p10, q1]
      rw [q0] at ih
      linarith

theorem barker_closed (n : ℕ) (hn : 1 < n) :
    (a n : ℚ) = (-550 + 450 * (-1) ^ n + 9901 * 10 ^ n) / 9900 := by
  have h := closed n hn
  have h' : (9900 : ℚ) * (a n : ℚ) = 9901 * 10 ^ n + 450 * (-1) ^ n - 550 := by exact_mod_cast h
  rw [eq_div_iff (by norm_num)]
  linarith

theorem recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have h0 := closed (k + 5) (by omega)
  have h1 := closed (k + 4) (by omega)
  have h2 := closed (k + 3) (by omega)
  have h3 := closed (k + 2) (by omega)
  rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega]
  have key : 9900 * ((a (k + 5) : ℤ) - (10 * a (k + 4) + a (k + 3) - 10 * a (k + 2))) = 0 := by
    linear_combination h0 - 10 * h1 - h2 + 10 * h3
  omega

theorem gf_mul : A * ((1 - X) * (1 + X) * (1 - 10 * X)) = 1 - X ^ 2 + X ^ 4 := by
  have hD : A * ((1 - X) * (1 + X) * (1 - 10 * X)) =
      A - C 10 * (A * X ^ 1) - C 1 * (A * X ^ 2) + C 10 * (A * X ^ 3) := by
    simp only [map_one, map_ofNat]
    ring
  have hN : (1 - X ^ 2 + X ^ 4 : ℚ⟦X⟧) = C 1 * X ^ 0 - C 1 * X ^ 2 + C 1 * X ^ 4 := by
    simp only [map_one]
    ring
  rw [hD, hN]
  ext m
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk]
  rcases Nat.lt_or_ge m 5 with hm | hm
  · have e3 : (a 3 : ℚ) = 1000 := by
      have := closed 3 (by norm_num); norm_num at this
      have : (a 3 : ℤ) = 1000 := by linarith
      exact_mod_cast this
    have e4 : (a 4 : ℚ) = 10001 := by
      have := closed 4 (by norm_num); norm_num at this
      have : (a 4 : ℤ) = 10001 := by linarith
      exact_mod_cast this
    interval_cases m <;> norm_num [a0, a1, a2, e3, e4]
  · have hr := recurrence m (by omega)
    have hq : (a m : ℚ) = 10 * a (m - 1) + a (m - 2) - 10 * a (m - 3) := by exact_mod_cast hr
    have h1 : 1 ≤ m := by omega
    have h2 : 2 ≤ m := by omega
    have h3 : 3 ≤ m := by omega
    have h4 : 4 ≤ m := by omega
    have k0 : m - 0 ≠ 0 := by omega
    have k2 : m - 2 ≠ 0 := by omega
    have k4 : m - 4 ≠ 0 := by omega
    simp only [h1, h2, h3, h4, Nat.zero_le, k0, k2, k4, coeff_C, if_true, if_false, hq]
    ring

theorem proof : Conjecture := by
  refine ⟨barker_closed, recurrence, ?_⟩
  have h0 : constantCoeff ((1 - X) * (1 + X) * (1 - 10 * X) : ℚ⟦X⟧) ≠ 0 := by simp
  rw [← gf_mul, mul_assoc, PowerSeries.mul_inv_cancel _ h0, mul_one]

/-- Control: the first terms listed in the entry. -/
theorem a_values : a 0 = 1 ∧ a 1 = 10 ∧ a 2 = 100 ∧ a 3 = 1000 ∧ a 4 = 10001 ∧
    a 5 = 100010 ∧ a 6 = 1000101 := by
  have h3 := closed 3 (by norm_num)
  have h4 := closed 4 (by norm_num)
  have h5 := closed 5 (by norm_num)
  have h6 := closed 6 (by norm_num)
  norm_num at h3 h4 h5 h6
  refine ⟨a0, a1, a2, ?_, ?_, ?_, ?_⟩ <;> omega

end OMA.S_oeis_a267044

theorem OMA.solution : type_of% @OMA.S_oeis_a267044.main :=
  OMA.S_oeis_a267044.proof
