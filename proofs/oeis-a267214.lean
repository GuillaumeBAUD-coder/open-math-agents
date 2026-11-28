import OMAStatements.S_oeis_a267214

-- Problem: A267214: Total number of OFF (white) cells after n iterations of the "Rule 109" elementary cellular automaton starting with a single ON (bl
-- Upstream: formal-conjectures statements/oeis-a267214.lean:0 (declaration OMA.S_oeis_a267214.main)
-- Credit: @tczyzycki (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a267214

open OMA.S_oeis_a267214

private lemma ruleOut_symm (l c r : Bool) : ruleOut 109 l c r = ruleOut 109 r c l := by
  cases l <;> cases c <;> cases r <;> decide

private lemma cell_succ (t : ℕ) (i : ℤ) :
    cell 109 (t + 1) i = ruleOut 109 (cell 109 t (i - 1)) (cell 109 t i) (cell 109 t (i + 1)) :=
  rfl

private lemma cell_neg (t : ℕ) : ∀ i : ℤ, cell 109 t (-i) = cell 109 t i := by
  induction t with
  | zero =>
    intro i
    simp [cell]
  | succ t ih =>
    intro i
    simp only [cell]
    have h1 : -i - 1 = -(i + 1) := by omega
    have h2 : -i + 1 = -(i - 1) := by omega
    rw [h1, h2, ih (i + 1), ih i, ih (i - 1), ruleOut_symm]

private lemma cell_bg (t : ℕ) : ∀ i : ℤ, (t : ℤ) < |i| → cell 109 t i = decide (t % 2 = 1) := by
  induction t with
  | zero =>
    intro i hi
    have hne : i ≠ 0 := by
      intro h; subst h; simp at hi
    simp [cell, hne]
  | succ t ih =>
    intro i hi
    simp only [cell]
    have h1 : (t : ℤ) < |i - 1| := by
      rcases le_or_gt 0 i with h | h
      · rw [abs_of_nonneg h] at hi
        rw [abs_of_nonneg (by omega)]; omega
      · rw [abs_of_neg h] at hi
        rw [abs_of_neg (by omega)]; omega
    have h2 : (t : ℤ) < |i| := by omega
    have h3 : (t : ℤ) < |i + 1| := by
      rcases le_or_gt 0 i with h | h
      · rw [abs_of_nonneg h] at hi
        rw [abs_of_nonneg (by omega)]; omega
      · rw [abs_of_neg h] at hi
        rw [abs_of_neg (by omega)]; omega
    rw [ih (i - 1) h1, ih i h2, ih (i + 1) h3]
    have hm : t % 2 = 0 ∨ t % 2 = 1 := by omega
    rcases hm with h | h
    · have h' : (t + 1) % 2 = 1 := by omega
      rw [h, h']; decide
    · have h' : (t + 1) % 2 = 0 := by omega
      rw [h, h']; decide

private lemma cell_core : ∀ t : ℕ,
    (1 ≤ t → cell 109 t 0 = decide (t % 3 ≠ 0) ∧
             cell 109 t 1 = decide (t % 3 = 2) ∧
             cell 109 t 2 = true) ∧
    (5 ≤ t → cell 109 t 3 = decide (t % 3 = 0)) ∧
    (4 ≤ t → ∀ i : ℤ, 0 ≤ i → cell 109 t (i + 4) = cell 109 (t - 4) i) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases ht5 : t < 5
    · interval_cases t
      · refine ⟨by omega, by omega, by omega⟩
      · refine ⟨fun _ => by decide, by omega, by omega⟩
      · refine ⟨fun _ => by decide, by omega, by omega⟩
      · refine ⟨fun _ => by decide, by omega, by omega⟩
      · refine ⟨fun _ => by decide, by omega, fun _ i hi => ?_⟩
        rcases eq_or_lt_of_le hi with rfl | hpos
        · decide
        · rw [cell_bg 4 (i + 4) (by rw [abs_of_nonneg (by omega)]; omega),
              cell_bg 0 i (by rw [abs_of_nonneg (by omega)]; omega)]
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 5 := ⟨t - 5, by omega⟩
      have hm_lt : s + 4 < s + 5 := by omega
      have hih_m := ih (s + 4) hm_lt
      have ⟨hc0, hc1, hc2⟩ := hih_m.1 (by omega)
      have hshift_m := hih_m.2.2 (by omega)
      have hmod : (s + 4) % 3 = 0 ∨ (s + 4) % 3 = 1 ∨ (s + 4) % 3 = 2 := by omega
      have hc3_m : 1 ≤ s → cell 109 (s + 4) 3 = decide ((s + 4) % 3 = 0) :=
        fun hs => hih_m.2.1 (by omega)
      have hstep : s + 5 = (s + 4) + 1 := rfl
      refine ⟨fun _ => ?_, fun _ => ?_, fun _ i hi => ?_⟩
      · -- (A) for s + 5
        refine ⟨?_, ?_, ?_⟩
        · -- i = 0
          rw [hstep, cell_succ, show (0 : ℤ) - 1 = -(1 : ℤ) by omega,
            show (0 : ℤ) + 1 = 1 by omega, cell_neg, hc0, hc1]
          rcases hmod with h | h | h
          · have h' : (s + 5) % 3 = 1 := by omega
            rw [h, h']; decide
          · have h' : (s + 5) % 3 = 2 := by omega
            rw [h, h']; decide
          · have h' : (s + 5) % 3 = 0 := by omega
            rw [h, h']; decide
        · -- i = 1
          rw [hstep, cell_succ, show (1 : ℤ) - 1 = 0 by omega,
            show (1 : ℤ) + 1 = 2 by omega, hc0, hc1, hc2]
          rcases hmod with h | h | h
          · have h' : (s + 5) % 3 = 1 := by omega
            rw [h, h']; decide
          · have h' : (s + 5) % 3 = 2 := by omega
            rw [h, h']; decide
          · have h' : (s + 5) % 3 = 0 := by omega
            rw [h, h']; decide
        · -- i = 2
          rcases eq_or_ne s 0 with rfl | hs0
          · decide
          · have hc3 := hc3_m (by omega)
            rw [hstep, cell_succ, show (2 : ℤ) - 1 = 1 by omega,
              show (2 : ℤ) + 1 = 3 by omega, hc1, hc2, hc3]
            rcases hmod with h | h | h <;> (rw [h]; decide)
      · -- (B) for s + 5, i = 3
        rcases eq_or_ne s 0 with rfl | hs0
        · decide
        · have hc3 := hc3_m (by omega)
          have hc4 : cell 109 (s + 4) 4 = cell 109 s 0 := by
            have := hshift_m 0 (by omega)
            simpa using this
          have hih_s := ih s (by omega)
          have hcs0 : cell 109 s 0 = decide (s % 3 ≠ 0) := (hih_s.1 (by omega)).1
          rw [hstep, cell_succ, show (3 : ℤ) - 1 = 2 by omega,
            show (3 : ℤ) + 1 = 4 by omega, hc2, hc3, hc4, hcs0]
          rcases hmod with h | h | h
          · have h1 : s % 3 = 2 := by omega
            have h2 : (s + 5) % 3 = 1 := by omega
            rw [h, h1, h2]; decide
          · have h1 : s % 3 = 0 := by omega
            have h2 : (s + 5) % 3 = 2 := by omega
            rw [h, h1, h2]; decide
          · have h1 : s % 3 = 1 := by omega
            have h2 : (s + 5) % 3 = 0 := by omega
            rw [h, h1, h2]; decide
      · -- (C) for s + 5, i ≥ 0
        have hsub : s + 5 - 4 = s + 1 := by omega
        rw [hsub]
        rcases eq_or_lt_of_le hi with rfl | hpos
        · -- i = 0
          rcases eq_or_ne s 0 with rfl | hs0
          · decide
          · have hc3 := hc3_m (by omega)
            have hc4 : cell 109 (s + 4) 4 = cell 109 s 0 := by
              have := hshift_m 0 (by omega); simpa using this
            have hc5 : cell 109 (s + 4) 5 = cell 109 s 1 := by
              have := hshift_m 1 (by omega); simpa using this
            have hih_s := ih s (by omega)
            have hcs1 : cell 109 s 1 = decide (s % 3 = 2) := (hih_s.1 (by omega)).2.1
            have h3eq1 : cell 109 (s + 4) 3 = cell 109 s 1 := by
              rw [hc3, hcs1]
              have : (s + 4) % 3 = 0 ↔ s % 3 = 2 := by omega
              simp [this]
            rw [hstep, cell_succ (s + 4), cell_succ s, show (0 : ℤ) + 4 = 4 by omega,
              show (4 : ℤ) - 1 = 3 by omega, show (4 : ℤ) + 1 = 5 by omega,
              show (0 : ℤ) - 1 = -(1 : ℤ) by omega, show (0 : ℤ) + 1 = 1 by omega,
              cell_neg, h3eq1, hc4, hc5]
        · -- i ≥ 1
          have h1 : cell 109 (s + 4) (i + 4 - 1) = cell 109 s (i - 1) := by
            have := hshift_m (i - 1) (by omega)
            have heq : i - 1 + 4 = i + 4 - 1 := by omega
            simpa [heq] using this
          have h2 : cell 109 (s + 4) (i + 4) = cell 109 s i := by
            simpa using hshift_m i (by omega)
          have h3 : cell 109 (s + 4) (i + 4 + 1) = cell 109 s (i + 1) := by
            have := hshift_m (i + 1) (by omega)
            have heq : i + 1 + 4 = i + 4 + 1 := by omega
            simpa [heq] using this
          rw [hstep, cell_succ (s + 4), cell_succ s, h1, h2, h3]

private lemma cell_shift4 (t : ℕ) (i : ℤ) (hi : 0 ≤ i) :
    cell 109 (t + 4) (i + 4) = cell 109 t i := by
  have := (cell_core (t + 4)).2.2 (by omega) i hi
  simpa using this

private lemma onCount_eq_half (t : ℕ) :
    onCount 109 t =
      (if cell 109 t 0 then 1 else 0) +
      2 * ∑ k ∈ Finset.range t, (if cell 109 t (k + 1 : ℕ) then 1 else 0) := by
  unfold onCount
  have hsplit : 2 * t + 1 = t + (t + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have h1 :
      ∑ x ∈ Finset.range t, (if cell 109 t ((x : ℤ) - (t : ℤ)) then 1 else 0) =
      ∑ k ∈ Finset.range t, (if cell 109 t ((k + 1 : ℕ) : ℤ) then 1 else 0) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [Finset.mem_range] at hk
    have hneg : ((t - 1 - k : ℕ) : ℤ) - (t : ℤ) = -((k + 1 : ℕ) : ℤ) := by omega
    rw [hneg, cell_neg]
  have h2 :
      ∑ x ∈ Finset.range (t + 1), (if cell 109 t (((t + x : ℕ) : ℤ) - (t : ℤ)) then 1 else 0) =
      (if cell 109 t 0 then 1 else 0) +
      ∑ k ∈ Finset.range t, (if cell 109 t ((k + 1 : ℕ) : ℤ) then 1 else 0) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_add, add_sub_cancel_left, Nat.cast_zero]
    rw [add_comm]
  rw [h1, h2]
  omega

private lemma onCount_add_four (t : ℕ) (ht : 1 ≤ t) :
    onCount 109 (t + 4) =
      onCount 109 t + (if t % 3 = 1 then 6 else if t % 3 = 2 then 5 else 3) := by
  rw [onCount_eq_half (t + 4), onCount_eq_half t]
  have hsum :
      ∑ k ∈ Finset.range (t + 4), (if cell 109 (t + 4) ((k + 1 : ℕ) : ℤ) then 1 else 0) =
      (∑ x ∈ Finset.range 3, (if cell 109 (t + 4) ((x + 1 : ℕ) : ℤ) then 1 else 0)) +
      (∑ x ∈ Finset.range (t + 1), (if cell 109 (t + 4) ((3 + x + 1 : ℕ) : ℤ) then 1 else 0)) := by
    have hsplit : Finset.range (t + 4) = Finset.range (3 + (t + 1)) := by congr 1; omega
    rw [hsplit, Finset.sum_range_add]
  have htail :
      ∑ x ∈ Finset.range (t + 1), (if cell 109 (t + 4) ((3 + x + 1 : ℕ) : ℤ) then 1 else 0) =
      (if cell 109 t 0 then 1 else 0) +
      ∑ k ∈ Finset.range t, (if cell 109 t ((k + 1 : ℕ) : ℤ) then 1 else 0) := by
    rw [Finset.sum_range_succ']
    rw [add_comm]
    congr 1
    · have hc4 : cell 109 (t + 4) ((3 + 0 + 1 : ℕ) : ℤ) = cell 109 t 0 := by
        simpa using cell_shift4 t 0 (by omega)
      rw [hc4]
    · refine Finset.sum_congr rfl ?_
      intro k _
      have heq : ((3 + (k + 1) + 1 : ℕ) : ℤ) = ((k + 1 : ℕ) : ℤ) + 4 := by omega
      rw [heq, cell_shift4 t ((k + 1 : ℕ) : ℤ) (by omega)]
  have hhead :
      ∑ x ∈ Finset.range 3, (if cell 109 (t + 4) ((x + 1 : ℕ) : ℤ) then 1 else 0) =
      (if cell 109 (t + 4) 1 then 1 else 0) +
      (if cell 109 (t + 4) 2 then 1 else 0) +
      (if cell 109 (t + 4) 3 then 1 else 0) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.range_zero, Finset.sum_empty, zero_add]
    rfl
  rw [hsum, hhead, htail]
  have hct0 : cell 109 t 0 = decide (t % 3 ≠ 0) := ((cell_core t).1 ht).1
  have ⟨h0, h1, h2⟩ := (cell_core (t + 4)).1 (by omega)
  have h3 := (cell_core (t + 4)).2.1 (by omega)
  rw [hct0, h0, h1, h2, h3]
  have hmod : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
  rcases hmod with h | h | h
  · have h' : (t + 4) % 3 = 1 := by omega
    simp [h, h']; omega
  · have h' : (t + 4) % 3 = 2 := by omega
    simp [h, h']; omega
  · have h' : (t + 4) % 3 = 0 := by omega
    simp [h, h']; omega

private def offCount (k : ℕ) : ℤ :=
  (2 * k + 1 : ℤ) - onCount 109 k

private lemma offCount_add_four (t : ℕ) (ht : 1 ≤ t) :
    offCount (t + 4) - offCount t =
      if t % 3 = 1 then 2 else if t % 3 = 2 then 3 else 5 := by
  unfold offCount
  have h := onCount_add_four t ht
  split_ifs at h ⊢ <;> omega

private lemma offCount_rec (n : ℕ) (hn : 8 ≤ n) :
    offCount n = offCount (n - 3) + offCount (n - 4) - offCount (n - 7) := by
  have h1 := offCount_add_four (n - 4) (by omega)
  have h2 := offCount_add_four (n - 7) (by omega)
  have hn1 : n - 4 + 4 = n := by omega
  have hn2 : n - 7 + 4 = n - 3 := by omega
  rw [hn1] at h1
  rw [hn2] at h2
  have hmod : (n - 4) % 3 = (n - 7) % 3 := by omega
  rw [hmod] at h1
  omega

private lemma a_succ (n : ℕ) : a (n + 1) = a n + offCount (n + 1) := by
  unfold a offCount
  rw [Finset.sum_range_succ]

private lemma a_rec_int (n : ℕ) (hn : 8 ≤ n) :
    a n = a (n - 1) + a (n - 3) - a (n - 5) - a (n - 7) + a (n - 8) := by
  have h0 : a n - a (n - 1) = offCount n := by
    have := a_succ (n - 1)
    have heq : n - 1 + 1 = n := by omega
    rw [heq] at this; omega
  have h3 : a (n - 3) - a (n - 4) = offCount (n - 3) := by
    have := a_succ (n - 4)
    have heq : n - 4 + 1 = n - 3 := by omega
    rw [heq] at this; omega
  have h4 : a (n - 4) - a (n - 5) = offCount (n - 4) := by
    have := a_succ (n - 5)
    have heq : n - 5 + 1 = n - 4 := by omega
    rw [heq] at this; omega
  have h7 : a (n - 7) - a (n - 8) = offCount (n - 7) := by
    have := a_succ (n - 8)
    have heq : n - 8 + 1 = n - 7 := by omega
    rw [heq] at this; omega
  have hr := offCount_rec n hn
  omega

private lemma a_rec_rat (n : ℕ) (hn : 8 ≤ n) :
    (a n : ℚ) = a (n - 1) + a (n - 3) - a (n - 5) - a (n - 7) + a (n - 8) := by
  exact_mod_cast a_rec_int n hn

private lemma a_vals :
    a 0 = 0 ∧ a 1 = 2 ∧ a 2 = 2 ∧ a 3 = 7 ∧ a 4 = 9 ∧ a 5 = 13 ∧ a 6 = 16 ∧ a 7 = 26 := by
  decide

open PowerSeries in
private lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℚ)) *
        ((1 - X) ^ 3 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2) : PowerSeries ℚ) =
      X * (2 + 5 * X ^ 2 + 2 * X ^ 4 - 2 * X ^ 5 + 3 * X ^ 6) := by
  have hpoly :
      ((1 - X) ^ 3 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2) : PowerSeries ℚ) =
        1 - X - X ^ 3 + X ^ 5 + X ^ 7 - X ^ 8 := by
    ring
  have hrhs :
      (X * (2 + 5 * X ^ 2 + 2 * X ^ 4 - 2 * X ^ 5 + 3 * X ^ 6) : PowerSeries ℚ) =
        C 2 * X ^ 1 + C 5 * X ^ 3 + C 2 * X ^ 5 - C 2 * X ^ 6 + C 3 * X ^ 7 := by
    simp only [map_ofNat]
    ring
  rw [hpoly, hrhs]
  ext n
  set F : PowerSeries ℚ := PowerSeries.mk (fun k => (a k : ℚ))
  have hF : ∀ k, coeff k F = (a k : ℚ) := fun k => coeff_mk k _
  have hmul :
      coeff n (F * (1 - X - X ^ 3 + X ^ 5 + X ^ 7 - X ^ 8)) =
        coeff n F - coeff n (F * X ^ 1) - coeff n (F * X ^ 3) +
        coeff n (F * X ^ 5) + coeff n (F * X ^ 7) - coeff n (F * X ^ 8) := by
    have heq :
        F * (1 - X - X ^ 3 + X ^ 5 + X ^ 7 - X ^ 8) =
          F - F * X ^ 1 - F * X ^ 3 + F * X ^ 5 + F * X ^ 7 - F * X ^ 8 := by
      ring
    rw [heq]
    simp only [map_sub, map_add]
  rw [hmul]
  simp only [map_sub, map_add, coeff_mul_X_pow', hF, coeff_C]
  have ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := a_vals
  by_cases hn : 8 ≤ n
  · have hrec := a_rec_rat n hn
    have h1n : 1 ≤ n := by omega
    have h3n : 3 ≤ n := by omega
    have h5n : 5 ≤ n := by omega
    have h6n : 6 ≤ n := by omega
    have h7n : 7 ≤ n := by omega
    have hs1 : n - 1 ≠ 0 := by omega
    have hs3 : n - 3 ≠ 0 := by omega
    have hs5 : n - 5 ≠ 0 := by omega
    have hs6 : n - 6 ≠ 0 := by omega
    have hs7 : n - 7 ≠ 0 := by omega
    simp only [h1n, h3n, h5n, h6n, h7n, hn, hs1, hs3, hs5, hs6, hs7, ↓reduceIte]
    linarith
  · interval_cases n <;>
      simp [h0, h1, h2, h3, h4, h5, h6, h7] <;>
      norm_num

end OMA.P_oeis_a267214

theorem OMA.solution : type_of% @OMA.S_oeis_a267214.main :=
  ⟨OMA.P_oeis_a267214.a_rec_rat, OMA.P_oeis_a267214.gf_eq⟩
