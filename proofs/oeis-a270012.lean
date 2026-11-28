import OMAStatements.S_oeis_a270012

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: with code 7 a cell is ON next iff c + 2s <= 2 (c its value, s the number of ON
-- neighbours). Stage 1 is all ON, and an all-ON plane becomes all OFF and back. So stage k >= 1
-- has (2k+1)^2 ON cells (k odd) or 0 (k even); the closed form of the partial sums follows by
-- induction, the recurrence by ring, and the generating function coefficientwise.

namespace OMA.S_oeis_a270012

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

lemma ac (n : ℕ) (hn : 1 ≤ n) : (onCount 7 n : ℤ) = if n % 2 = 1 then (2 * (n : ℤ) + 1) ^ 2 else 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  simp only [onCount, cellc]
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · have : (t + 1) % 2 = 1 := by omega
    simp [h, this]
    push_cast; ring
  · have : ¬ (t + 1) % 2 = 1 := by omega
    simp [h, this]

theorem closed (n : ℕ) : (a n : ℚ) = 1 / 4 * (7 - 3 * (-1 : ℚ) ^ n) +
    (11 / 6 - 2 * (-1 : ℚ) ^ n) * (n : ℚ) - (-2 + (-1 : ℚ) ^ n) * (n : ℚ) ^ 2 +
    2 * (n : ℚ) ^ 3 / 3 := by
  induction n with
  | zero => simp [a, onCount, cell]; norm_num; decide
  | succ n ih =>
    have hs : a (n + 1) = a n + (onCount 7 (n + 1) : ℤ) := by
      simp only [a]; rw [Finset.sum_range_succ]
    rw [hs, ac (n + 1) (by omega)]
    push_cast
    rw [ih]
    rcases Nat.even_or_odd n with he | ho
    · have : (n + 1) % 2 = 1 := by have := Nat.even_iff.1 he; omega
      have hp : (-1 : ℚ) ^ n = 1 := he.neg_one_pow
      simp only [this, if_true]
      push_cast; rw [pow_succ (-1 : ℚ) n, hp]; ring
    · have : ¬ (n + 1) % 2 = 1 := by have := Nat.odd_iff.1 ho; omega
      have hp : (-1 : ℚ) ^ n = -1 := ho.neg_one_pow
      simp only [this, if_false]
      push_cast; rw [pow_succ (-1 : ℚ) n, hp]; ring

theorem even_form (n : ℕ) (he : Even n) :
    (a n : ℚ) = (4 * (n : ℚ) ^ 3 + 6 * (n : ℚ) ^ 2 - (n : ℚ) + 6) / 6 := by
  rw [closed, he.neg_one_pow]; ring

theorem odd_form (n : ℕ) (ho : Odd n) :
    (a n : ℚ) = (4 * (n : ℚ) ^ 3 + 18 * (n : ℚ) ^ 2 + 23 * (n : ℚ) + 15) / 6 := by
  rw [closed, ho.neg_one_pow]; ring

theorem recur (n : ℕ) (hn : 7 ≤ n) : (a n : ℚ) = a (n - 1) + 3 * a (n - 2) - 3 * a (n - 3) -
    3 * a (n - 4) + 3 * a (n - 5) + a (n - 6) - a (n - 7) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
    show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega,
    show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega,
    show m + 7 - 7 = m by omega]
  simp only [closed]
  push_cast
  simp only [pow_add]
  ring

theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 4 * (1 + X) ^ 3 : PowerSeries ℚ) =
    1 + 9 * X - 3 * X ^ 2 + 22 * X ^ 3 + 3 * X ^ 4 + X ^ 5 - X ^ 6 := by
  set A := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have hL : A * ((1 - X) ^ 4 * (1 + X) ^ 3) =
      A - A * X ^ 1 - C (3 : ℚ) * (A * X ^ 2) + C (3 : ℚ) * (A * X ^ 3) + C (3 : ℚ) * (A * X ^ 4)
        - C (3 : ℚ) * (A * X ^ 5) - A * X ^ 6 + A * X ^ 7 := by
    simp only [map_ofNat]; ring
  have hR : (1 + 9 * X - 3 * X ^ 2 + 22 * X ^ 3 + 3 * X ^ 4 + X ^ 5 - X ^ 6 : ℚ⟦X⟧) =
      C (1 : ℚ) * X ^ 0 + C (9 : ℚ) * X ^ 1 - C (3 : ℚ) * X ^ 2 + C (22 : ℚ) * X ^ 3
        + C (3 : ℚ) * X ^ 4 + C (1 : ℚ) * X ^ 5 - C (1 : ℚ) * X ^ 6 := by
    simp only [map_ofNat, map_one]; ring
  rw [hL, hR, hA]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  rcases Nat.lt_or_ge n 7 with hn | hn
  · interval_cases n <;> simp [closed] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    have q := recur (m + 7) (by omega)
    rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
      show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega,
      show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega,
      show m + 7 - 7 = m by omega] at q
    rw [if_pos (show 1 ≤ m + 7 by omega), if_pos (show 2 ≤ m + 7 by omega),
      if_pos (show 3 ≤ m + 7 by omega), if_pos (show 4 ≤ m + 7 by omega),
      if_pos (show 5 ≤ m + 7 by omega), if_pos (show 6 ≤ m + 7 by omega),
      if_pos (show 7 ≤ m + 7 by omega),
      show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
      show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega,
      show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega,
      show m + 7 - 7 = m by omega]
    simp only [coeff_C, show m + 7 - 0 ≠ 0 by omega, show m + 6 ≠ 0 by omega,
      show m + 5 ≠ 0 by omega, show m + 4 ≠ 0 by omega, show m + 3 ≠ 0 by omega,
      show m + 2 ≠ 0 by omega, show m + 1 ≠ 0 by omega, if_false, ite_self]
    linarith

end OMA.S_oeis_a270012

theorem OMA.solution : type_of% @OMA.S_oeis_a270012.main :=
  ⟨OMA.S_oeis_a270012.closed, OMA.S_oeis_a270012.even_form, OMA.S_oeis_a270012.odd_form,
    OMA.S_oeis_a270012.recur, OMA.S_oeis_a270012.gf⟩
