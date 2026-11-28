import OMAStatements.S_oeis_a266671

namespace OMA.S_oeis_a266671

open PowerSeries




lemma state_succ (t : ℕ) (i : ℤ) :
    state (t + 1) i = rule (state t (i - 1)) (state t i) (state t (i + 1)) := rfl

/-- Relative ON cells of the even stages and relative OFF cells of the odd stages. -/
def E : List ℤ := [(0 : ℤ)]
def O : List ℤ := [(-1 : ℤ)]

lemma s1 (i : ℤ) : state 1 i = decide (i ∉ O) := by
  show rule (decide (i - 1 = 0)) (decide (i = 0)) (decide (i + 1 = 0)) = _
  rcases (by omega : i ≤ -2 ∨ (-1 ≤ i ∧ i ≤ 1) ∨ 2 ≤ i) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_false (by omega : ¬ i - 1 = 0), decide_eq_false (by omega : ¬ i = 0),
      decide_eq_false (by omega : ¬ i + 1 = 0), decide_eq_true (by simp [E, O] <;> omega)]; decide
  · interval_cases i <;> decide
  · rw [decide_eq_false (by omega : ¬ i - 1 = 0), decide_eq_false (by omega : ¬ i = 0),
      decide_eq_false (by omega : ¬ i + 1 = 0), decide_eq_true (by simp [E, O] <;> omega)]; decide

/-- Even stage to the next odd stage, relative position e. -/
lemma stepEO (e : ℤ) :
    rule (decide (e - 1 ∈ E)) (decide (e ∈ E)) (decide (e + 1 ∈ E)) = decide (e ∉ O) := by
  rcases (by omega : e ≤ -5 ∨ (-4 ≤ e ∧ e ≤ 3) ∨ 4 ≤ e) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_false (by simp [E]; omega), decide_eq_false (by simp [E]; omega),
      decide_eq_false (by simp [E]; omega), decide_eq_true (by simp [O]; omega)]; decide
  · interval_cases e <;> decide
  · rw [decide_eq_false (by simp [E]; omega), decide_eq_false (by simp [E]; omega),
      decide_eq_false (by simp [E]; omega), decide_eq_true (by simp [O]; omega)]; decide

/-- Odd stage to the next even stage, relative position e (the frame moves by one). -/
lemma stepOE (e : ℤ) :
    rule (decide (e - 1 ∉ O)) (decide (e ∉ O)) (decide (e + 1 ∉ O)) = decide (e + 1 ∈ E) := by
  rcases (by omega : e ≤ -5 ∨ (-4 ≤ e ∧ e ≤ 3) ∨ 4 ≤ e) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_true (by simp [O]; omega), decide_eq_true (by simp [O]; omega),
      decide_eq_true (by simp [O]; omega), decide_eq_false (by simp [E]; omega)]; decide
  · interval_cases e <;> decide
  · rw [decide_eq_true (by simp [O]; omega), decide_eq_true (by simp [O]; omega),
      decide_eq_true (by simp [O]; omega), decide_eq_false (by simp [E]; omega)]; decide

lemma odd_of_even (s : ℕ) (h : ∀ i, state (2 * s) i = decide (i + (s : ℤ) ∈ E)) :
    ∀ i, state (2 * s + 1) i = decide (i + (s : ℤ) ∉ O) := by
  intro i
  rw [state_succ, h, h, h]
  have e1 : i - 1 + (s : ℤ) = (i + (s : ℤ)) - 1 := by ring
  have e2 : i + 1 + (s : ℤ) = (i + (s : ℤ)) + 1 := by ring
  rw [e1, e2, stepEO]

lemma even_of_odd (s : ℕ) (h : ∀ i, state (2 * s + 1) i = decide (i + (s : ℤ) ∉ O)) :
    ∀ i, state (2 * (s + 1)) i = decide (i + ((s + 1 : ℕ) : ℤ) ∈ E) := by
  intro i
  rw [show 2 * (s + 1) = (2 * s + 1) + 1 by ring, state_succ, h, h, h]
  have e1 : i - 1 + (s : ℤ) = (i + (s : ℤ)) - 1 := by ring
  have e2 : i + 1 + (s : ℤ) = (i + (s : ℤ)) + 1 := by ring
  have e3 : i + ((s + 1 : ℕ) : ℤ) = (i + (s : ℤ)) + 1 := by push_cast; ring
  rw [e1, e2, e3, stepOE]

/-- The glider: stages 2s + 1 and 2s + 2 for s >= 0. -/
lemma pattern (s : ℕ) (hs : 0 ≤ s) :
    (∀ i, state (2 * s + 1) i = decide (i + (s : ℤ) ∉ O)) ∧
      (∀ i, state (2 * (s + 1)) i = decide (i + ((s + 1 : ℕ) : ℤ) ∈ E)) := by
  induction s, hs using Nat.le_induction with
  | base =>
    have hb : ∀ i, state (2 * 0 + 1) i = decide (i + ((0 : ℕ) : ℤ) ∉ O) := fun i => by
      rw [s1]; norm_num
    exact ⟨hb, even_of_odd 0 hb⟩
  | succ s hs ih =>
    have ho := odd_of_even (s + 1) ih.2
    exact ⟨ho, even_of_odd (s + 1) ho⟩

lemma state_odd (s : ℕ) (hs : 0 ≤ s) (i : ℤ) : state (2 * s + 1) i = decide (i + (s : ℤ) ∉ O) :=
  (pattern s hs).1 i

lemma state_even (s : ℕ) (hs : 1 ≤ s) (i : ℤ) : state (2 * s) i = decide (i + (s : ℤ) ∈ E) := by
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
  exact (pattern r (by omega)).2 i

lemma sum_pow (m : ℕ) : ∑ k ∈ Finset.range m, (2 : ℚ) ^ k = (2 ^ m - 1) / 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

lemma a_even (m : ℕ) : a (2 * (m + 1)) = 1 * 2 ^ (3 * m + 3) := by
  unfold a
  have hf : (Finset.range (2 * (2 * (m + 1)) + 1)).filter
      (fun k : ℕ => state (2 * (m + 1)) ((k : ℤ) - ((2 * (m + 1) : ℕ) : ℤ)) = true) =
      {m + 1} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, state_even (m + 1) (by omega), decide_eq_true_eq, E,
      List.mem_cons, List.mem_nil_iff, or_false, Finset.mem_insert, Finset.mem_singleton]
    push_cast
    omega
  rw [← Finset.sum_filter, hf]
  rw [Finset.sum_singleton]
  rw [show 2 * (2 * (m + 1)) - (m + 1) = 3 * m + 3 + 0 by omega]
  simp only [pow_add]
  ring

lemma a_odd (m : ℕ) :
    (a (2 * (m + 0) + 1) : ℚ) = (2 ^ (4 * m + 3) - 1) / 1 - 1 * 2 ^ (3 * m + 2) := by
  set R := Finset.range (2 * (2 * (m + 0) + 1) + 1) with hR
  set w : ℕ → ℚ := fun k => 2 ^ (2 * (2 * (m + 0) + 1) - k) with hw
  have hsplit : ∑ k ∈ R, (if state (2 * (m + 0) + 1) ((k : ℤ) - (((2 * (m + 0) + 1) : ℕ) : ℤ)) then w k else 0) =
      ∑ k ∈ R, w k - ∑ k ∈ R.filter
        (fun k : ℕ => ¬ state (2 * (m + 0) + 1) ((k : ℤ) - (((2 * (m + 0) + 1) : ℕ) : ℤ)) = true), w k := by
    rw [← Finset.sum_filter, eq_sub_iff_add_eq, Finset.sum_filter_add_sum_filter_not]
  have hoff : R.filter
      (fun k : ℕ => ¬ state (2 * (m + 0) + 1) ((k : ℤ) - (((2 * (m + 0) + 1) : ℕ) : ℤ)) = true) =
      {m} := by
    ext k
    simp only [hR, Finset.mem_filter, Finset.mem_range, state_odd (m + 0) (by omega), decide_eq_true_eq, O,
      List.mem_cons, List.mem_nil_iff, or_false, not_not, Finset.mem_insert,
      Finset.mem_singleton]
    push_cast
    omega
  have htot : ∑ k ∈ R, w k = (2 ^ (4 * m + 3) - 1) / 1 := by
    rw [hR, hw, ← Finset.sum_range_reflect]
    have : ∀ k ∈ Finset.range (2 * (2 * (m + 0) + 1) + 1),
        (2 : ℚ) ^ (2 * (2 * (m + 0) + 1) - (2 * (2 * (m + 0) + 1) + 1 - 1 - k)) = 2 ^ k := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [show 2 * (2 * (m + 0) + 1) - (2 * (2 * (m + 0) + 1) + 1 - 1 - k) = k by omega]
    rw [Finset.sum_congr rfl this, sum_pow]
    ring_nf
  have hcast : (a (2 * (m + 0) + 1) : ℚ) =
      ∑ k ∈ R, (if state (2 * (m + 0) + 1) ((k : ℤ) - (((2 * (m + 0) + 1) : ℕ) : ℤ)) then w k else 0) := by
    unfold a
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    split_ifs <;> try simp [hw]
  rw [hcast, hsplit, htot, hoff]
  rw [Finset.sum_singleton]
  simp only [hw]
  rw [show 2 * (2 * (m + 0) + 1) - (m) = 3 * m + 2 + 0 by omega]
  simp only [pow_add]
  ring

lemma values : a 0 = 1 ∧ a 1 = 3 ∧ a 2 = 8 ∧ a 3 = 95 ∧ a 4 = 64 ∧ a 5 = 1791 ∧ a 6 = 512 ∧ a 7 = 30719 ∧ a 8 = 4096 ∧ a 9 = 507903 ∧ a 10 = 32768 ∧ a 11 = 8257535 ∧ a 12 = 262144 := by
  exact ⟨by decide,
    by have h : (a 1 : ℚ) = 3 := (by rw [show (1 : ℕ) = 2 * (0 + 0) + 1 from rfl, a_odd 0]; norm_num); exact_mod_cast h,
    by rw [show (2 : ℕ) = 2 * (0 + 1) from rfl, a_even 0]; norm_num,
    by have h : (a 3 : ℚ) = 95 := (by rw [show (3 : ℕ) = 2 * (1 + 0) + 1 from rfl, a_odd 1]; norm_num); exact_mod_cast h,
    by rw [show (4 : ℕ) = 2 * (1 + 1) from rfl, a_even 1]; norm_num,
    by have h : (a 5 : ℚ) = 1791 := (by rw [show (5 : ℕ) = 2 * (2 + 0) + 1 from rfl, a_odd 2]; norm_num); exact_mod_cast h,
    by rw [show (6 : ℕ) = 2 * (2 + 1) from rfl, a_even 2]; norm_num,
    by have h : (a 7 : ℚ) = 30719 := (by rw [show (7 : ℕ) = 2 * (3 + 0) + 1 from rfl, a_odd 3]; norm_num); exact_mod_cast h,
    by rw [show (8 : ℕ) = 2 * (3 + 1) from rfl, a_even 3]; norm_num,
    by have h : (a 9 : ℚ) = 507903 := (by rw [show (9 : ℕ) = 2 * (4 + 0) + 1 from rfl, a_odd 4]; norm_num); exact_mod_cast h,
    by rw [show (10 : ℕ) = 2 * (4 + 1) from rfl, a_even 4]; norm_num,
    by have h : (a 11 : ℚ) = 8257535 := (by rw [show (11 : ℕ) = 2 * (5 + 0) + 1 from rfl, a_odd 5]; norm_num); exact_mod_cast h,
    by rw [show (12 : ℕ) = 2 * (5 + 1) from rfl, a_even 5]; norm_num⟩

/-- Barker's recurrence, for n > 5. -/
theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 25 * a (n - 2) - 152 * a (n - 4) + 128 * a (n - 6) := by
  rcases Nat.lt_or_ge n 7 with hlt | hge
  · have v := values
    interval_cases n <;> simp_all
  · have key : (a n : ℚ) = 25 * a (n - 2) - 152 * a (n - 4) + 128 * a (n - 6) := by
      rcases Nat.even_or_odd n with ⟨s, hs⟩ | ⟨s, hs⟩
      · obtain ⟨r, rfl⟩ : ∃ r, s = r + 4 := ⟨s - 4, by omega⟩
        subst hs
        rw [show r + 4 + (r + 4) - 2 = 2 * ((r + 2) + 1) by omega,
          show r + 4 + (r + 4) - 4 = 2 * ((r + 1) + 1) by omega,
          show r + 4 + (r + 4) - 6 = 2 * (r + 1) by omega,
          show r + 4 + (r + 4) = 2 * ((r + 3) + 1) by omega,
          a_even, a_even, a_even, a_even]
        push_cast
        ring
      · obtain ⟨r, rfl⟩ : ∃ r, s = r + 3 := ⟨s - 3, by omega⟩
        subst hs
        rw [show 2 * (r + 3) + 1 - 2 = 2 * ((r + 2) + 0) + 1 by omega,
          show 2 * (r + 3) + 1 - 4 = 2 * ((r + 1) + 0) + 1 by omega,
          show 2 * (r + 3) + 1 - 6 = 2 * (r + 0) + 1 by omega,
          show 2 * (r + 3) + 1 = 2 * ((r + 3) + 0) + 1 by omega,
          a_odd, a_odd, a_odd, a_odd]
        ring
    exact_mod_cast key

/-- Barker's g.f., as an identity in Q[[x]]. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) =
    (1 + 3 * X - 17 * X ^ 2 + 20 * X ^ 3 + 16 * X ^ 4 - 128 * X ^ 5) *
      ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 8 * X ^ 2))⁻¹ := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have hden : constantCoeff (((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 8 * X ^ 2)) : ℚ⟦X⟧) ≠ 0 := by simp
  have key : A * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 8 * X ^ 2)) = 1 + 3 * X - 17 * X ^ 2 + 20 * X ^ 3 + 16 * X ^ 4 - 128 * X ^ 5 := by
    have e1 : A * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 8 * X ^ 2)) =
        A - C 25 * (A * X ^ 2) + C 152 * (A * X ^ 4) - C 128 * (A * X ^ 6) := by
      simp only [map_ofNat]; ring
    have e2 : (1 + 3 * X - 17 * X ^ 2 + 20 * X ^ 3 + 16 * X ^ 4 - 128 * X ^ 5 : ℚ⟦X⟧) =
        C 1 + X ^ 1 * C 3 - X ^ 2 * C 17 + X ^ 3 * C 20 + X ^ 4 * C 16 - X ^ 5 * C 128 := by
      simp only [map_ofNat, map_one]; ring
    rw [e1, e2]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', coeff_C,
      coeff_X_pow, hA, coeff_mk]
    have v := values
    rcases Nat.lt_or_ge n 7 with hn | hn
    · interval_cases n <;> simp_all <;> norm_num
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
      simp only [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, if_false]
      have hr := recurrence n (by omega)
      have : (a n : ℚ) = 25 * a (n - 2) - 152 * a (n - 4) + 128 * a (n - 6) := by
        exact_mod_cast hr
      rw [this]; ring
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]

/-- Controls: the entry's data a(0..19). -/
theorem controls : a 0 = 1 ∧ a 1 = 3 ∧ a 2 = 8 ∧ a 3 = 95 ∧ a 4 = 64 ∧ a 5 = 1791 ∧ a 6 = 512 ∧ a 7 = 30719 ∧ a 8 = 4096 ∧ a 9 = 507903 ∧ a 10 = 32768 ∧ a 11 = 8257535 ∧ a 12 = 262144 ∧ a 13 = 133169151 ∧ a 14 = 2097152 ∧ a 15 = 2139095039 ∧ a 16 = 16777216 ∧ a 17 = 34292629503 ∧ a 18 = 134217728 ∧ a 19 = 549218942975 := by
  exact ⟨(values).1,
    (values).2.1,
    (values).2.2.1,
    (values).2.2.2.1,
    (values).2.2.2.2.1,
    (values).2.2.2.2.2.1,
    (values).2.2.2.2.2.2.1,
    (values).2.2.2.2.2.2.2.1,
    (values).2.2.2.2.2.2.2.2.1,
    (values).2.2.2.2.2.2.2.2.2.1,
    (values).2.2.2.2.2.2.2.2.2.2.1,
    (values).2.2.2.2.2.2.2.2.2.2.2.1,
    (values).2.2.2.2.2.2.2.2.2.2.2.2,
    by have h : (a 13 : ℚ) = 133169151 := (by rw [show (13 : ℕ) = 2 * (6 + 0) + 1 from rfl, a_odd 6]; norm_num); exact_mod_cast h,
    by rw [show (14 : ℕ) = 2 * (6 + 1) from rfl, a_even 6]; norm_num,
    by have h : (a 15 : ℚ) = 2139095039 := (by rw [show (15 : ℕ) = 2 * (7 + 0) + 1 from rfl, a_odd 7]; norm_num); exact_mod_cast h,
    by rw [show (16 : ℕ) = 2 * (7 + 1) from rfl, a_even 7]; norm_num,
    by have h : (a 17 : ℚ) = 34292629503 := (by rw [show (17 : ℕ) = 2 * (8 + 0) + 1 from rfl, a_odd 8]; norm_num); exact_mod_cast h,
    by rw [show (18 : ℕ) = 2 * (8 + 1) from rfl, a_even 8]; norm_num,
    by have h : (a 19 : ℚ) = 549218942975 := (by rw [show (19 : ℕ) = 2 * (9 + 0) + 1 from rfl, a_odd 9]; norm_num); exact_mod_cast h⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 25 * a (n - 2) - 152 * a (n - 4) + 128 * a (n - 6)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 + 3 * X - 17 * X ^ 2 + 20 * X ^ 3 + 16 * X ^ 4 - 128 * X ^ 5) *
        ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 8 * X ^ 2))⁻¹ :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a266671

theorem OMA.solution : type_of% @OMA.S_oeis_a266671.main :=
  OMA.S_oeis_a266671.conjecture
