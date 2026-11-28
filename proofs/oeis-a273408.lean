import OMAStatements.S_oeis_a273408

/-!
Proof of the three conjectures of OEIS A273408 (partial sums of the ON-cell counts of Rule 675
started from a single ON cell), for the formulation with `cell 675`.

Rule 675 = 1010100011 in binary: the new value of a cell is bit c + 2k of 675, where c is the
cell and k the number of its ON orthogonal neighbours. One step turns the OFF background ON
(bit 0), keeps the lone origin ON (bit 1) and leaves its four neighbours OFF (bit 2 is 0), so
stage 1 is ON everywhere except at the four orthogonal neighbours of the origin. That
configuration is a fixed point (bits 1, 5, 7 and 9 are set, bit 8 is clear). Hence the count
over the (2n+1) × (2n+1) square is 1 at stage 0 and (2n+1)^2 - 4 at every later stage, and the
partial sums satisfy 3 a(n) = 4n^3 + 12n^2 - n + 3. The recurrence and the generating function
follow from this closed form (the fourth difference of a cubic vanishes).
-/

namespace OMA.Helpers

open OMA.S_oeis_a273408

/-- The four orthogonal neighbours of the origin. -/
abbrev a273408_P (x y : ℤ) : Prop :=
  (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1)

/-- Every stage n ≥ 1: everything ON except the four orthogonal neighbours of the origin. -/
def a273408_C : ℤ → ℤ → Bool := fun x y => !(decide (a273408_P x y))

/-- One synchronous update of the plane under Rule 675. -/
def a273408_step (g : ℤ → ℤ → Bool) : ℤ → ℤ → Bool := fun i j =>
  Nat.testBit 675 ((g i j).toNat + 2 * ((g (i + 1) j).toNat + (g (i - 1) j).toNat +
    (g i (j + 1)).toNat + (g i (j - 1)).toNat))

theorem a273408_cell_zero : cell 675 0 = fun i j => decide (i = 0 ∧ j = 0) := rfl

theorem a273408_cell_succ (t : ℕ) : cell 675 (t + 1) = a273408_step (cell 675 t) := rfl

theorem a273408_step_initial :
    a273408_step (fun i j => decide (i = 0 ∧ j = 0)) = a273408_C := by
  funext x y
  simp only [a273408_step, a273408_C, a273408_P]
  by_cases h0 : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h0
    decide
  by_cases h1 : (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1)
  · rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · have e1 : ¬ (x + 1 = 0 ∧ y = 0) := by omega
    have e2 : ¬ (x - 1 = 0 ∧ y = 0) := by omega
    have e3 : ¬ (x = 0 ∧ y + 1 = 0) := by omega
    have e4 : ¬ (x = 0 ∧ y - 1 = 0) := by omega
    simp only [h0, h1, e1, e2, e3, e4, decide_false]
    decide

theorem a273408_step_C : a273408_step a273408_C = a273408_C := by
  funext x y
  simp only [a273408_step, a273408_C]
  by_cases h0 : a273408_P x y <;> by_cases h1 : a273408_P (x + 1) y <;>
    by_cases h2 : a273408_P (x - 1) y <;> by_cases h3 : a273408_P x (y + 1) <;>
    by_cases h4 : a273408_P x (y - 1) <;>
    simp only [h0, h1, h2, h3, h4, decide_true, decide_false, Bool.not_true, Bool.not_false] <;>
    first | decide | (exfalso; simp only [a273408_P] at *; omega)

theorem a273408_state_succ (n : ℕ) : cell 675 (n + 1) = a273408_C := by
  induction n with
  | zero => rw [a273408_cell_succ, a273408_cell_zero, a273408_step_initial]
  | succ n ih => rw [a273408_cell_succ, ih, a273408_step_C]

theorem a273408_onCount_zero : onCount 675 0 = 1 := by
  decide

theorem a273408_onCount_succ (m : ℕ) : onCount 675 (m + 1) = (2 * (m + 1) + 1) ^ 2 - 4 := by
  unfold onCount
  rw [a273408_state_succ]
  set N := m + 1 with hN
  set R := Finset.range (2 * N + 1) with hR
  rw [← Finset.sum_product' (f := fun (i j : ℕ) =>
    if a273408_C ((i : ℤ) - N) ((j : ℤ) - N) = true then 1 else 0)]
  rw [Finset.sum_boole, Nat.cast_id]
  have hsplit := Finset.card_filter_add_card_filter_not (s := R ×ˢ R)
    (fun p : ℕ × ℕ => a273408_C ((p.1 : ℤ) - N) ((p.2 : ℤ) - N) = true)
  have hneg : (R ×ˢ R).filter
      (fun p : ℕ × ℕ => ¬ a273408_C ((p.1 : ℤ) - N) ((p.2 : ℤ) - N) = true) =
      {(N + 1, N), (N - 1, N), (N, N + 1), (N, N - 1)} := by
    ext ⟨i, j⟩
    simp only [hR, Finset.mem_filter, Finset.mem_product, Finset.mem_range, a273408_C,
      a273408_P, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Bool.not_eq_true,
      Bool.not_eq_false', decide_eq_true_eq]
    omega
  have h4 : ({(N + 1, N), (N - 1, N), (N, N + 1), (N, N - 1)} : Finset (ℕ × ℕ)).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    all_goals simp only [ne_eq, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]
    all_goals omega
  have hcard : (R ×ˢ R).card = (2 * N + 1) ^ 2 := by
    rw [Finset.card_product, hR, Finset.card_range, sq]
  rw [hneg, h4, hcard] at hsplit
  omega

theorem a273408_closed (n : ℕ) : 3 * a n = 4 * (n : ℤ) ^ 3 + 12 * (n : ℤ) ^ 2 - n + 3 := by
  induction n with
  | zero => simp [a, a273408_onCount_zero]
  | succ n ih =>
    have hs : a (n + 1) = a n + (onCount 675 (n + 1) : ℤ) := Finset.sum_range_succ _ _
    have h4 : 4 ≤ (2 * (n + 1) + 1) ^ 2 := by nlinarith
    rw [hs, a273408_onCount_succ]
    push_cast [Nat.cast_sub h4]
    linear_combination ih

theorem a273408_closedQ (n : ℕ) :
    3 * (a n : ℚ) = 4 * (n : ℚ) ^ 3 + 12 * (n : ℚ) ^ 2 - n + 3 := by
  have h := congrArg (Int.cast : ℤ → ℚ) (a273408_closed n)
  push_cast at h
  exact h

theorem a273408_gf :
    PowerSeries.mk (fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 4 =
      1 + 2 * PowerSeries.X + 9 * PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3 := by
  have hA := a273408_closedQ
  have v0 : (a 0 : ℚ) = 1 := by have := hA 0; push_cast at this; linarith
  have v1 : (a 1 : ℚ) = 6 := by have := hA 1; push_cast at this; linarith
  have v2 : (a 2 : ℚ) = 27 := by have := hA 2; push_cast at this; linarith
  have v3 : (a 3 : ℚ) = 72 := by have := hA 3; push_cast at this; linarith
  set A := PowerSeries.mk (fun n => (a n : ℚ)) with hAdef
  have e : A * (1 - PowerSeries.X) ^ 4 =
      PowerSeries.X ^ 0 * A - PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 1 * A)
      + PowerSeries.C (6 : ℚ) * (PowerSeries.X ^ 2 * A)
      - PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 3 * A)
      + PowerSeries.X ^ 4 * A := by
    simp only [map_ofNat]
    ring
  have e2 : (1 + 2 * PowerSeries.X + 9 * PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3 :
      PowerSeries ℚ) =
      PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 1
        + PowerSeries.C (9 : ℚ) * PowerSeries.X ^ 2
        - PowerSeries.C (4 : ℚ) * PowerSeries.X ^ 3 := by
    simp only [map_ofNat, map_one]
    ring
  rw [e, e2]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
  simp only [PowerSeries.coeff_X_pow_mul', hAdef, PowerSeries.coeff_mk]
  by_cases hk : 4 ≤ k
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    rw [show m + 4 - 0 = m + 4 by omega, show m + 4 - 1 = m + 3 by omega,
      show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega,
      show m + 4 - 4 = m by omega]
    have h4 := hA (m + 4)
    have h5 := hA (m + 3)
    have h6 := hA (m + 2)
    have h7 := hA (m + 1)
    have h8 := hA m
    push_cast at h4 h5 h6 h7 h8
    linear_combination (h4 - 4 * h5 + 6 * h6 - 4 * h7 + h8) / 3
  · interval_cases k <;> simp [v0, v1, v2, v3] <;> norm_num

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a273408.main := by
  refine ⟨?_, ?_, OMA.Helpers.a273408_gf⟩
  · intro n
    have h := OMA.Helpers.a273408_closedQ n
    rw [eq_div_iff (by norm_num : (3 : ℚ) ≠ 0)]
    linarith
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
    have h4 := OMA.Helpers.a273408_closedQ (m + 4)
    have h5 := OMA.Helpers.a273408_closedQ (m + 3)
    have h6 := OMA.Helpers.a273408_closedQ (m + 2)
    have h7 := OMA.Helpers.a273408_closedQ (m + 1)
    have h8 := OMA.Helpers.a273408_closedQ m
    push_cast at h4 h5 h6 h7 h8
    linear_combination (h4 - 4 * h5 + 6 * h6 - 4 * h7 + h8) / 3
