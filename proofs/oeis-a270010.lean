import OMAStatements.S_oeis_a270010

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: with code 7 a cell is ON next iff c + 2s <= 2 (c its value, s the number of ON
-- neighbours). Stage 1 is all ON (the origin has s = 0, its neighbours have c = 0, s = 1), and
-- an all-ON plane becomes all OFF and back. So for n >= 1 the count is (2n+1)^2 (n odd) or 0
-- (n even); the recurrence and the generating function follow coefficientwise.

namespace OMA.S_oeis_a270010

open PowerSeries

lemma cell1 (i j : ℤ) : cell 7 1 i j = true := by
  show Nat.testBit 7 _ = true
  simp only [cell]
  by_cases h0 : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h0; decide
  by_cases h1 : (i = 1 ∨ i = -1) ∧ j = 0
  · obtain ⟨h | h, rfl⟩ := h1 <;> subst h <;> decide
  by_cases h2 : i = 0 ∧ (j = 1 ∨ j = -1)
  · obtain ⟨rfl, h | h⟩ := h2 <;> subst h <;> decide
  have e1 : ¬ (i = 0 ∧ j = 0) := h0
  have e2 : ¬ (i + 1 = 0 ∧ j = 0) := by omega
  have e3 : ¬ (i - 1 = 0 ∧ j = 0) := by omega
  have e4 : ¬ (i = 0 ∧ j + 1 = 0) := by omega
  have e5 : ¬ (i = 0 ∧ j - 1 = 0) := by omega
  simp only [e1, e2, e3, e4, e5, decide_false]
  decide

lemma cellc (t : ℕ) (i j : ℤ) : cell 7 (t + 1) i j = decide (t % 2 = 0) := by
  induction t generalizing i j with
  | zero => simpa using cell1 i j
  | succ t ih =>
    show Nat.testBit 7 _ = _
    rw [ih, ih, ih, ih, ih]
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · have : ¬ (t + 1) % 2 = 0 := by omega
      simp only [h, this, decide_true, decide_false]
      decide
    · have : (t + 1) % 2 = 0 := by omega
      simp only [h, this, decide_true, show ¬ (1 = 0) by omega, decide_false]
      decide

lemma ac (n : ℕ) (hn : 1 ≤ n) : a n = if n % 2 = 1 then (2 * (n : ℤ) + 1) ^ 2 else 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  simp only [a, onCount, cellc]
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · have : (t + 1) % 2 = 1 := by omega
    simp [h, this]
    push_cast; ring
  · have : ¬ (t + 1) % 2 = 1 := by omega
    simp [h, this]

lemma a0 : a 0 = 1 := by decide +kernel

theorem closed (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = -1 * ((-1 + (-1 : ℚ) ^ n) * (1 + 2 * (n : ℚ)) ^ 2) / 2 := by
  rw [ac n hn]
  rcases Nat.even_or_odd n with he | ho
  · have : ¬ n % 2 = 1 := by have := Nat.even_iff.1 he; omega
    simp [this, he.neg_one_pow]
  · have : n % 2 = 1 := Nat.odd_iff.1 ho
    simp [this, ho.neg_one_pow]; ring

theorem even_zero (n : ℕ) (hn : 1 ≤ n) (he : Even n) : (a n : ℚ) = 0 := by
  rw [ac n hn]
  have : ¬ n % 2 = 1 := by have := Nat.even_iff.1 he; omega
  simp [this]

theorem odd_form (n : ℕ) (ho : Odd n) : (a n : ℚ) = 4 * (n : ℚ) ^ 2 + 4 * (n : ℚ) + 1 := by
  have h1 : 1 ≤ n := by obtain ⟨k, rfl⟩ := ho; omega
  rw [ac n h1]
  have : n % 2 = 1 := Nat.odd_iff.1 ho
  simp [this]; ring

theorem recur (n : ℕ) (hn : 7 ≤ n) : (a n : ℚ) = 3 * a (n - 2) - 3 * a (n - 4) + a (n - 6) := by
  rw [ac n (by omega), ac (n - 2) (by omega), ac (n - 4) (by omega), ac (n - 6) (by omega)]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have h0 : ¬ n % 2 = 1 := by omega
    have h1 : ¬ (n - 2) % 2 = 1 := by omega
    have h2 : ¬ (n - 4) % 2 = 1 := by omega
    have h3 : ¬ (n - 6) % 2 = 1 := by omega
    simp [h0, h1, h2, h3]
  · have h1 : (n - 2) % 2 = 1 := by omega
    have h2 : (n - 4) % 2 = 1 := by omega
    have h3 : (n - 6) % 2 = 1 := by omega
    simp only [h, h1, h2, h3, if_true]
    push_cast [show 2 ≤ n by omega, show 4 ≤ n by omega, show 6 ≤ n by omega]
    ring

theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) ^ 3 : PowerSeries ℚ) =
    1 + 9 * X - 3 * X ^ 2 + 22 * X ^ 3 + 3 * X ^ 4 + X ^ 5 - X ^ 6 := by
  set A := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have hL : A * ((1 - X) ^ 3 * (1 + X) ^ 3) =
      A - C (3 : ℚ) * (A * X ^ 2) + C (3 : ℚ) * (A * X ^ 4) - A * X ^ 6 := by
    simp only [map_ofNat]; ring
  have hR : (1 + 9 * X - 3 * X ^ 2 + 22 * X ^ 3 + 3 * X ^ 4 + X ^ 5 - X ^ 6 : ℚ⟦X⟧) =
      C (1 : ℚ) * X ^ 0 + C (9 : ℚ) * X ^ 1 - C (3 : ℚ) * X ^ 2 + C (22 : ℚ) * X ^ 3
        + C (3 : ℚ) * X ^ 4 + C (1 : ℚ) * X ^ 5 - C (1 : ℚ) * X ^ 6 := by
    simp only [map_ofNat, map_one]; ring
  rw [hL, hR, hA]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  rcases Nat.lt_or_ge n 7 with hn | hn
  · have q1 := ac 1 le_rfl
    have q2 := ac 2 (by norm_num)
    have q3 := ac 3 (by norm_num)
    have q4 := ac 4 (by norm_num)
    have q5 := ac 5 (by norm_num)
    have q6 := ac 6 (by norm_num)
    norm_num at q1 q2 q3 q4 q5 q6
    have r1 : (a 1 : ℚ) = 9 := by exact_mod_cast q1
    have r2 : (a 2 : ℚ) = 0 := by exact_mod_cast q2
    have r3 : (a 3 : ℚ) = 49 := by exact_mod_cast q3
    have r4 : (a 4 : ℚ) = 0 := by exact_mod_cast q4
    have r5 : (a 5 : ℚ) = 121 := by exact_mod_cast q5
    have r6 : (a 6 : ℚ) = 0 := by exact_mod_cast q6
    interval_cases n <;> simp [a0, r1, r2, r3, r4, r5, r6] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    have q := recur (m + 7) (by omega)
    rw [show m + 7 - 2 = m + 5 by omega, show m + 7 - 4 = m + 3 by omega,
      show m + 7 - 6 = m + 1 by omega] at q
    rw [if_pos (show 2 ≤ m + 7 by omega), if_pos (show 4 ≤ m + 7 by omega),
      if_pos (show 6 ≤ m + 7 by omega),
      show m + 7 - 2 = m + 5 by omega, show m + 7 - 4 = m + 3 by omega,
      show m + 7 - 6 = m + 1 by omega]
    simp only [coeff_C, show m + 7 - 0 ≠ 0 by omega, show m + 7 - 1 ≠ 0 by omega,
      show m + 5 ≠ 0 by omega, show m + 7 - 3 ≠ 0 by omega, show m + 3 ≠ 0 by omega,
      show m + 7 - 5 ≠ 0 by omega, show m + 1 ≠ 0 by omega, if_false, ite_self]
    linarith

end OMA.S_oeis_a270010

theorem OMA.solution : type_of% @OMA.S_oeis_a270010.main :=
  ⟨OMA.S_oeis_a270010.closed, OMA.S_oeis_a270010.even_zero, OMA.S_oeis_a270010.odd_form,
    OMA.S_oeis_a270010.recur, OMA.S_oeis_a270010.gf⟩
