import OMAStatements.S_oeis_a267270

namespace OMA.S_oeis_a267270

open PowerSeries




lemma state_succ (t : ℕ) (i : ℤ) :
    state (t + 1) i = rule (state t (i - 1)) (state t i) (state t (i + 1)) := rfl

/-- Relative ON cells of the even stages and relative OFF cells of the odd stages. -/
def E : List ℤ := [(0 : ℤ), 1]
def O : List ℤ := [(0 : ℤ)]

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
  rcases (by omega : e ≤ -4 ∨ (-3 ≤ e ∧ e ≤ 4) ∨ 5 ≤ e) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_false (by simp [E]; omega), decide_eq_false (by simp [E]; omega),
      decide_eq_false (by simp [E]; omega), decide_eq_true (by simp [O]; omega)]; decide
  · interval_cases e <;> decide
  · rw [decide_eq_false (by simp [E]; omega), decide_eq_false (by simp [E]; omega),
      decide_eq_false (by simp [E]; omega), decide_eq_true (by simp [O]; omega)]; decide

/-- Odd stage to the next even stage, relative position e (the frame moves by one). -/
lemma stepOE (e : ℤ) :
    rule (decide (e - 1 ∉ O)) (decide (e ∉ O)) (decide (e + 1 ∉ O)) = decide (e + 1 ∈ E) := by
  rcases (by omega : e ≤ -4 ∨ (-3 ≤ e ∧ e ≤ 4) ∨ 5 ≤ e) with h | ⟨h1, h2⟩ | h
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

lemma sum_pow (m : ℕ) : ∑ k ∈ Finset.range m, (10 : ℚ) ^ k = (10 ^ m - 1) / 9 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

lemma a_even (m : ℕ) : a (2 * (m + 1)) = 11 * 10 ^ (3 * m + 2) := by
  unfold a
  have hf : (Finset.range (2 * (2 * (m + 1)) + 1)).filter
      (fun k : ℕ => state (2 * (m + 1)) ((k : ℤ) - ((2 * (m + 1) : ℕ) : ℤ)) = true) =
      {m + 1, m + 2} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, state_even (m + 1) (by omega), decide_eq_true_eq, E,
      List.mem_cons, List.mem_nil_iff, or_false, Finset.mem_insert, Finset.mem_singleton]
    push_cast
    omega
  rw [← Finset.sum_filter, hf]
  rw [Finset.sum_insert (by simp <;> omega), Finset.sum_singleton]
  rw [show 2 * (2 * (m + 1)) - (m + 1) = 3 * m + 2 + 1 by omega,
    show 2 * (2 * (m + 1)) - (m + 2) = 3 * m + 2 + 0 by omega]
  simp only [pow_add]
  ring

lemma a_odd (m : ℕ) :
    (a (2 * (m + 0) + 1) : ℚ) = (10 ^ (4 * m + 3) - 1) / 9 - 1 * 10 ^ (3 * m + 1) := by
  set R := Finset.range (2 * (2 * (m + 0) + 1) + 1) with hR
  set w : ℕ → ℚ := fun k => 10 ^ (2 * (2 * (m + 0) + 1) - k) with hw
  have hsplit : ∑ k ∈ R, (if state (2 * (m + 0) + 1) ((k : ℤ) - (((2 * (m + 0) + 1) : ℕ) : ℤ)) then w k else 0) =
      ∑ k ∈ R, w k - ∑ k ∈ R.filter
        (fun k : ℕ => ¬ state (2 * (m + 0) + 1) ((k : ℤ) - (((2 * (m + 0) + 1) : ℕ) : ℤ)) = true), w k := by
    rw [← Finset.sum_filter, eq_sub_iff_add_eq, Finset.sum_filter_add_sum_filter_not]
  have hoff : R.filter
      (fun k : ℕ => ¬ state (2 * (m + 0) + 1) ((k : ℤ) - (((2 * (m + 0) + 1) : ℕ) : ℤ)) = true) =
      {m + 1} := by
    ext k
    simp only [hR, Finset.mem_filter, Finset.mem_range, state_odd (m + 0) (by omega), decide_eq_true_eq, O,
      List.mem_cons, List.mem_nil_iff, or_false, not_not, Finset.mem_insert,
      Finset.mem_singleton]
    push_cast
    omega
  have htot : ∑ k ∈ R, w k = (10 ^ (4 * m + 3) - 1) / 9 := by
    rw [hR, hw, ← Finset.sum_range_reflect]
    have : ∀ k ∈ Finset.range (2 * (2 * (m + 0) + 1) + 1),
        (10 : ℚ) ^ (2 * (2 * (m + 0) + 1) - (2 * (2 * (m + 0) + 1) + 1 - 1 - k)) = 10 ^ k := by
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
  rw [show 2 * (2 * (m + 0) + 1) - (m + 1) = 3 * m + 1 + 0 by omega]
  simp only [pow_add]
  ring

lemma values : a 0 = 1 ∧ a 1 = 101 ∧ a 2 = 1100 ∧ a 3 = 1101111 ∧ a 4 = 1100000 ∧ a 5 = 11101111111 ∧ a 6 = 1100000000 ∧ a 7 = 111101111111111 ∧ a 8 = 1100000000000 ∧ a 9 = 1111101111111111111 ∧ a 10 = 1100000000000000 ∧ a 11 = 11111101111111111111111 ∧ a 12 = 1100000000000000000 := by
  exact ⟨by decide,
    by have h : (a 1 : ℚ) = 101 := (by rw [show (1 : ℕ) = 2 * (0 + 0) + 1 from rfl, a_odd 0]; norm_num); exact_mod_cast h,
    by rw [show (2 : ℕ) = 2 * (0 + 1) from rfl, a_even 0]; norm_num,
    by have h : (a 3 : ℚ) = 1101111 := (by rw [show (3 : ℕ) = 2 * (1 + 0) + 1 from rfl, a_odd 1]; norm_num); exact_mod_cast h,
    by rw [show (4 : ℕ) = 2 * (1 + 1) from rfl, a_even 1]; norm_num,
    by have h : (a 5 : ℚ) = 11101111111 := (by rw [show (5 : ℕ) = 2 * (2 + 0) + 1 from rfl, a_odd 2]; norm_num); exact_mod_cast h,
    by rw [show (6 : ℕ) = 2 * (2 + 1) from rfl, a_even 2]; norm_num,
    by have h : (a 7 : ℚ) = 111101111111111 := (by rw [show (7 : ℕ) = 2 * (3 + 0) + 1 from rfl, a_odd 3]; norm_num); exact_mod_cast h,
    by rw [show (8 : ℕ) = 2 * (3 + 1) from rfl, a_even 3]; norm_num,
    by have h : (a 9 : ℚ) = 1111101111111111111 := (by rw [show (9 : ℕ) = 2 * (4 + 0) + 1 from rfl, a_odd 4]; norm_num); exact_mod_cast h,
    by rw [show (10 : ℕ) = 2 * (4 + 1) from rfl, a_even 4]; norm_num,
    by have h : (a 11 : ℚ) = 11111101111111111111111 := (by rw [show (11 : ℕ) = 2 * (5 + 0) + 1 from rfl, a_odd 5]; norm_num); exact_mod_cast h,
    by rw [show (12 : ℕ) = 2 * (5 + 1) from rfl, a_even 5]; norm_num⟩

/-- Barker's recurrence, for n > 6. -/
theorem recurrence (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 11001 * a (n - 2) - 10011000 * a (n - 4) + 10000000 * a (n - 6) := by
  have key : (a n : ℚ) = 11001 * a (n - 2) - 10011000 * a (n - 4) + 10000000 * a (n - 6) := by
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
    (1 + 101 * X - 9901 * X ^ 2 - 9990 * X ^ 3 - 990100 * X ^ 4 - 1100000 * X ^ 5 + 1000000 * X ^ 6) *
      ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 1000 * X ^ 2))⁻¹ := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have hden : constantCoeff (((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 1000 * X ^ 2)) : ℚ⟦X⟧) ≠ 0 := by simp
  have key : A * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 1000 * X ^ 2)) = 1 + 101 * X - 9901 * X ^ 2 - 9990 * X ^ 3 - 990100 * X ^ 4 - 1100000 * X ^ 5 + 1000000 * X ^ 6 := by
    have e1 : A * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 1000 * X ^ 2)) =
        A - C 11001 * (A * X ^ 2) + C 10011000 * (A * X ^ 4) - C 10000000 * (A * X ^ 6) := by
      simp only [map_ofNat]; ring
    have e2 : (1 + 101 * X - 9901 * X ^ 2 - 9990 * X ^ 3 - 990100 * X ^ 4 - 1100000 * X ^ 5 + 1000000 * X ^ 6 : ℚ⟦X⟧) =
        C 1 + X ^ 1 * C 101 - X ^ 2 * C 9901 - X ^ 3 * C 9990 - X ^ 4 * C 990100 - X ^ 5 * C 1100000 + X ^ 6 * C 1000000 := by
      simp only [map_ofNat, map_one]; ring
    rw [e1, e2]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', coeff_C,
      coeff_X_pow, hA, coeff_mk]
    have v := values
    rcases Nat.lt_or_ge n 7 with hn | hn
    · interval_cases n <;> simp_all <;> norm_num
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
      simp only [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, if_false]
      have hr := recurrence n (by omega)
      have : (a n : ℚ) = 11001 * a (n - 2) - 10011000 * a (n - 4) + 10000000 * a (n - 6) := by
        exact_mod_cast hr
      rw [this]; ring
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]

/-- Controls: the entry's data a(0..15). -/
theorem controls : a 0 = 1 ∧ a 1 = 101 ∧ a 2 = 1100 ∧ a 3 = 1101111 ∧ a 4 = 1100000 ∧ a 5 = 11101111111 ∧ a 6 = 1100000000 ∧ a 7 = 111101111111111 ∧ a 8 = 1100000000000 ∧ a 9 = 1111101111111111111 ∧ a 10 = 1100000000000000 ∧ a 11 = 11111101111111111111111 ∧ a 12 = 1100000000000000000 ∧ a 13 = 111111101111111111111111111 ∧ a 14 = 1100000000000000000000 ∧ a 15 = 1111111101111111111111111111111 := by
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
    by have h : (a 13 : ℚ) = 111111101111111111111111111 := (by rw [show (13 : ℕ) = 2 * (6 + 0) + 1 from rfl, a_odd 6]; norm_num); exact_mod_cast h,
    by rw [show (14 : ℕ) = 2 * (6 + 1) from rfl, a_even 6]; norm_num,
    by have h : (a 15 : ℚ) = 1111111101111111111111111111111 := (by rw [show (15 : ℕ) = 2 * (7 + 0) + 1 from rfl, a_odd 7]; norm_num); exact_mod_cast h⟩

/-- Both of Barker's conjectures. -/
theorem barker :
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 11001 * a (n - 2) - 10011000 * a (n - 4) + 10000000 * a (n - 6)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 + 101 * X - 9901 * X ^ 2 - 9990 * X ^ 3 - 990100 * X ^ 4 - 1100000 * X ^ 5 + 1000000 * X ^ 6) *
        ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 1000 * X ^ 2))⁻¹ :=
  ⟨recurrence, gf⟩

/-- Keller's closed form for odd n; the exponent 3n/2 - 1/2 is the natural number (3n - 1)/2. -/
theorem keller_odd (n : ℕ) (hn : Odd n) :
    (a n : ℚ) = (10 ^ (2 * n + 1) - 9 * 10 ^ ((3 * n - 1) / 2) - 1) / 9 := by
  obtain ⟨m, rfl⟩ := hn
  have h := a_odd m
  rw [show 2 * (m + 0) + 1 = 2 * m + 1 by omega] at h
  rw [h, show (3 * (2 * m + 1) - 1) / 2 = 3 * m + 1 by omega,
    show 2 * (2 * m + 1) + 1 = 4 * m + 3 by omega]
  ring

/-- Keller's closed form for even n > 0; the exponent 3n/2 - 3 is a natural number there. -/
theorem keller_even (n : ℕ) (hn : Even n) (hpos : 0 < n) :
    a n = 1100 * 10 ^ (3 * n / 2 - 3) := by
  obtain ⟨s, rfl⟩ := hn
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  rw [show m + 1 + (m + 1) = 2 * (m + 1) by omega, a_even m,
    show 3 * (2 * (m + 1)) / 2 - 3 = 3 * m by omega, pow_add]
  ring

/-- Keller's conjecture, both parities. -/
theorem conjecture :
    (∀ n : ℕ, Odd n → (a n : ℚ) = (10 ^ (2 * n + 1) - 9 * 10 ^ ((3 * n - 1) / 2) - 1) / 9) ∧
    (∀ n : ℕ, Even n → 0 < n → a n = 1100 * 10 ^ (3 * n / 2 - 3)) :=
  ⟨keller_odd, keller_even⟩

end OMA.S_oeis_a267270

theorem OMA.solution : type_of% @OMA.S_oeis_a267270.main :=
  OMA.S_oeis_a267270.conjecture
