import OMAStatements.S_oeis_a273336

namespace OMA.S_oeis_a273336

open PowerSeries




/-- The pattern: stages 0 to 2 explicitly, and from stage 3 on every cell but the origin is ON. -/
def P : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | 1, x, y => decide (2 ≤ x.natAbs + y.natAbs)
  | 2, x, y => !decide (x.natAbs ≤ 1 ∧ y.natAbs ≤ 1 ∧ ¬(x = 0 ∧ y = 0))
  | _ + 3, x, y => !decide (x = 0 ∧ y = 0)

theorem P_three (m : ℕ) (x y : ℤ) : P (m + 3) x y = !decide (x = 0 ∧ y = 0) := rfl

/-- Away from the origin every stage t >= 1 is ON. -/
theorem P_far (t : ℕ) (ht : 0 < t) (u v : ℤ) (h : 3 ≤ u.natAbs + v.natAbs) : P t u v = true := by
  rcases (by omega : t = 1 ∨ t = 2 ∨ 3 ≤ t) with rfl | rfl | h3
  · exact decide_eq_true (by omega)
  · show (!decide (u.natAbs ≤ 1 ∧ v.natAbs ≤ 1 ∧ ¬(u = 0 ∧ v = 0))) = true
    rw [decide_eq_false (by omega)]; rfl
  · obtain ⟨m, rfl⟩ : ∃ m, t = m + 3 := ⟨t - 3, by omega⟩
    rw [P_three, decide_eq_false (by omega)]; rfl

/-- One step of Rule 657 maps the pattern at stage t to the pattern at stage t + 1. -/
theorem step (t : ℕ) (x y : ℤ) :
    Nat.testBit 657 ((P t x y).toNat + 2 * ((P t (x - 1) y).toNat + (P t (x + 1) y).toNat +
      (P t x (y - 1)).toNat + (P t x (y + 1)).toNat)) = P (t + 1) x y := by
  rcases (by omega : x.natAbs + y.natAbs ≤ 3 ∨ 4 ≤ x.natAbs + y.natAbs) with h | h
  · have hx1 : -3 ≤ x := by omega
    have hx2 : x ≤ 3 := by omega
    have hy1 : -3 ≤ y := by omega
    have hy2 : y ≤ 3 := by omega
    rcases (by omega : t < 3 ∨ 3 ≤ t) with ht | ht
    · interval_cases t <;> interval_cases x <;> interval_cases y <;> rfl
    · obtain ⟨m, rfl⟩ : ∃ m, t = m + 3 := ⟨t - 3, by omega⟩
      rw [show m + 3 + 1 = m + 1 + 3 by ring]
      simp only [P_three]
      interval_cases x <;> interval_cases y <;> rfl
  · rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht
      have e : ∀ u v : ℤ, 3 ≤ u.natAbs + v.natAbs → P 0 u v = false := fun u v huv =>
        decide_eq_false (by omega)
      rw [e x y (by omega), e (x - 1) y (by omega), e (x + 1) y (by omega),
        e x (y - 1) (by omega), e x (y + 1) (by omega),
        P_far 1 (by omega) x y (by omega)]
      rfl
    · rw [P_far t ht x y (by omega), P_far t ht (x - 1) y (by omega),
        P_far t ht (x + 1) y (by omega), P_far t ht x (y - 1) (by omega),
        P_far t ht x (y + 1) (by omega), P_far (t + 1) (by omega) x y (by omega)]
      rfl

/-- Stage t is the pattern `P t`. -/
theorem state_eq (t : ℕ) : ∀ x y, state t x y = P t x y := by
  induction t with
  | zero => intro x y; rfl
  | succ t ih =>
    intro x y
    show Nat.testBit 657 _ = _
    rw [ih, ih, ih, ih, ih]
    exact step t x y

/-- From stage 3 on only the origin is OFF. -/
theorem count_big (t : ℕ) (ht : 3 ≤ t) : count t + 1 = (2 * t + 1) ^ 2 := by
  have hs : ∀ x y : ℤ, state t x y = !decide (x = 0 ∧ y = 0) := by
    intro x y
    obtain ⟨m, rfl⟩ : ∃ m, t = m + 3 := ⟨t - 3, by omega⟩
    rw [state_eq, P_three]
  unfold count
  have e : (Finset.Icc (-(t : ℤ)) t ×ˢ Finset.Icc (-(t : ℤ)) t).filter
      (fun p => state t p.1 p.2 = true) =
      (Finset.Icc (-(t : ℤ)) t ×ˢ Finset.Icc (-(t : ℤ)) t).erase (0, 0) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_erase, hs, ne_eq, Prod.mk.injEq,
      Bool.not_eq_true', decide_eq_false_iff_not]
    tauto
  have hmem : ((0 : ℤ), (0 : ℤ)) ∈ Finset.Icc (-(t : ℤ)) t ×ˢ Finset.Icc (-(t : ℤ)) t := by
    simp only [Finset.mem_product, Finset.mem_Icc]; omega
  rw [e, Finset.card_erase_add_one hmem, Finset.card_product, Int.card_Icc,
    show ((t : ℤ) + 1 - -(t : ℤ)).toNat = 2 * t + 1 by omega]
  ring

/-- The counts of stages 0, 1, 2, read off the explicit pattern. -/
theorem count_small : count 0 = 1 ∧ count 1 = 4 ∧ count 2 = 17 := by
  have e : ∀ t, count t = ((Finset.Icc (-(t : ℤ)) t ×ˢ Finset.Icc (-(t : ℤ)) t).filter
      (fun p => P t p.1 p.2 = true)).card := by
    intro t; unfold count; simp only [state_eq]
  have i0 : Finset.Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ) = {0} := by decide
  have i1 : Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {-1, 0, 1} := by decide
  have i2 : Finset.Icc (-((2 : ℕ) : ℤ)) ((2 : ℕ) : ℤ) = {-2, -1, 0, 1, 2} := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [e, i0]; decide
  · rw [e, i1]; decide
  · rw [e, i2]; decide

theorem a_two : a 2 = 22 := by
  obtain ⟨h0, h1, h2⟩ := count_small
  simp only [a, Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2]

/-- Barker's closed form, for n > 1. -/
theorem closed (n : ℕ) (hn : 1 < n) :
    (a n : ℚ) = 2 / 3 * (2 * n ^ 3 + 6 * n ^ 2 + 4 * n - 15) := by
  induction n, hn using Nat.le_induction with
  | base => rw [a_two]; norm_num
  | succ n hn ih =>
    have hc := count_big (n + 1) (by omega)
    have hc' : (count (n + 1) : ℚ) = (2 * (n + 1 : ℚ) + 1) ^ 2 - 1 := by
      have : ((count (n + 1) + 1 : ℕ) : ℚ) = (((2 * (n + 1) + 1) ^ 2 : ℕ) : ℚ) := by
        rw [hc]
      push_cast at this
      linarith
    rw [show a (n + 1) = a n + count (n + 1) from Finset.sum_range_succ _ (n + 1)]
    push_cast
    rw [ih, hc']
    ring

theorem a_zero : a 0 = 1 := by
  simp only [a, Finset.sum_range_succ, Finset.sum_range_zero, count_small.1, zero_add]

theorem a_one : a 1 = 5 := by
  simp only [a, Finset.sum_range_succ, Finset.sum_range_zero, count_small.1, count_small.2.1]

theorem val (n N : ℕ) (hn : 1 < n) (hN : (N : ℚ) = 2 / 3 * (2 * n ^ 3 + 6 * n ^ 2 + 4 * n - 15)) :
    a n = N := by
  have h := (closed n hn).trans hN.symm
  exact_mod_cast h

/-- Controls: the entry's terms a(0..15). -/
theorem controls : a 0 = 1 ∧ a 1 = 5 ∧ a 2 = 22 ∧ a 3 = 70 ∧ a 4 = 150 ∧ a 5 = 270 ∧
    a 6 = 438 ∧ a 7 = 662 ∧ a 8 = 950 ∧ a 9 = 1310 ∧ a 10 = 1750 ∧ a 11 = 2278 ∧
    a 12 = 2902 ∧ a 13 = 3630 ∧ a 14 = 4470 ∧ a 15 = 5430 :=
  ⟨a_zero, a_one, a_two, val 3 70 (by norm_num) (by norm_num), val 4 150 (by norm_num) (by norm_num),
    val 5 270 (by norm_num) (by norm_num), val 6 438 (by norm_num) (by norm_num),
    val 7 662 (by norm_num) (by norm_num), val 8 950 (by norm_num) (by norm_num),
    val 9 1310 (by norm_num) (by norm_num), val 10 1750 (by norm_num) (by norm_num),
    val 11 2278 (by norm_num) (by norm_num), val 12 2902 (by norm_num) (by norm_num),
    val 13 3630 (by norm_num) (by norm_num), val 14 4470 (by norm_num) (by norm_num),
    val 15 5430 (by norm_num) (by norm_num)⟩

/-- Barker's recurrence, for n > 5. -/
theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
    show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega]
  have q : (a (m + 6) : ℚ) =
      4 * a (m + 5) - 6 * a (m + 4) + 4 * a (m + 3) - a (m + 2) := by
    rw [closed (m + 6) (by omega), closed (m + 5) (by omega), closed (m + 4) (by omega),
      closed (m + 3) (by omega), closed (m + 2) (by omega)]
    push_cast
    ring
  exact_mod_cast q

/-- Barker's g.f. with the denominator cleared. -/
theorem gf : mk (fun n => (a n : ℤ)) * (1 - X) ^ 4 =
    1 + X + 8 * X ^ 2 + 8 * X ^ 3 - 17 * X ^ 4 + 7 * X ^ 5 := by
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have c4 : (C (4 : ℤ) : PowerSeries ℤ) = 4 := map_ofNat C 4
  have c6 : (C (6 : ℤ) : PowerSeries ℤ) = 6 := map_ofNat C 6
  have c7 : (C (7 : ℤ) : PowerSeries ℤ) = 7 := map_ofNat C 7
  have c8 : (C (8 : ℤ) : PowerSeries ℤ) = 8 := map_ofNat C 8
  have c17 : (C (17 : ℤ) : PowerSeries ℤ) = 17 := map_ofNat C 17
  have hD : A * (1 - X) ^ 4 =
      A - C 4 * (A * X ^ 1) + C 6 * (A * X ^ 2) - C 4 * (A * X ^ 3) + A * X ^ 4 := by
    rw [c4, c6]; ring
  have hN : (1 + X + 8 * X ^ 2 + 8 * X ^ 3 - 17 * X ^ 4 + 7 * X ^ 5 : PowerSeries ℤ) =
      1 + X ^ 1 + X ^ 2 * C 8 + X ^ 3 * C 8 - X ^ 4 * C 17 + X ^ 5 * C 7 := by
    rw [c7, c8, c17]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', hA, coeff_mk,
    coeff_one, coeff_X_pow]
  obtain ⟨v0, v1, v2, v3, v4, v5, -⟩ := controls
  rcases Nat.lt_or_ge n 6 with h | h
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5]
  · have r := recurrence n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, if_true, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega,
      if_false]
    linear_combination r

/-- All three of Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 1 < n → (a n : ℚ) = 2 / 3 * (2 * n ^ 3 + 6 * n ^ 2 + 4 * n - 15)) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)) ∧
    mk (fun n => (a n : ℤ)) * (1 - X) ^ 4 =
      1 + X + 8 * X ^ 2 + 8 * X ^ 3 - 17 * X ^ 4 + 7 * X ^ 5 :=
  ⟨closed, recurrence, gf⟩

end OMA.S_oeis_a273336

theorem OMA.solution : type_of% @OMA.S_oeis_a273336.main :=
  OMA.S_oeis_a273336.conjecture
