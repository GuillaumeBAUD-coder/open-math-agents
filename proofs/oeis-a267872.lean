import OMAStatements.S_oeis_a267872

/-!
Proof of the two conjectures of OEIS A267872 (Rule 237 started from a single ON cell).

Rule 237 sends a neighbourhood to OFF only for 100 and 001. Hence row 1 is ON everywhere
except at x = -1 and x = 1, row 2 is ON everywhere, and since 111 goes to 1 every later row
stays all ON. So a(0) = a(1) = 1 and a(n) = 2n + 1 for n ≥ 2. The recurrence (for n > 3)
follows directly; for the generating function we show A * (1-X)^2 = N coefficientwise and
divide by (1-X)^2, which has constant coefficient 1.
-/

namespace OMA.Helpers

open OMA.S_oeis_a267872

/-- Rule 237 in closed form: the next state is OFF only for the neighbourhoods 100 and 001. -/
theorem a267872_step_eq (s : ℤ → Bool) (x : ℤ) :
    step 237 s x = (s x || s (x - 1) == s (x + 1)) := by
  unfold step
  cases s (x - 1) <;> cases s x <;> cases s (x + 1) <;> decide

/-- Row 1: every cell is ON except the two neighbours of the origin. -/
theorem a267872_state_one (x : ℤ) : state 237 1 x = decide (x ≠ 1 ∧ x ≠ -1) := by
  show step 237 (fun y => decide (y = 0)) x = decide (x ≠ 1 ∧ x ≠ -1)
  rw [a267872_step_eq]
  by_cases h0 : x = 0
  · subst h0; decide
  · by_cases h1 : x = 1
    · subst h1; decide
    · by_cases h2 : x = -1
      · subst h2; decide
      · have e1 : x - 1 ≠ 0 := by omega
        have e2 : x + 1 ≠ 0 := by omega
        simp [h0, h1, h2, e1, e2]

/-- Row 2: every cell is ON. -/
theorem a267872_state_two (x : ℤ) : state 237 2 x = true := by
  show step 237 (state 237 1) x = true
  rw [a267872_step_eq]
  simp only [a267872_state_one]
  by_cases h1 : x = 1
  · subst h1; decide
  · by_cases h2 : x = -1
    · subst h2; decide
    · simp [h1, h2]

/-- From time 2 on, every cell is ON, since rule 237 sends 111 to 1. -/
theorem a267872_state_add_two (n : ℕ) (x : ℤ) : state 237 (n + 2) x = true := by
  induction n generalizing x with
  | zero => exact a267872_state_two x
  | succ k ih =>
    show step 237 (state 237 (k + 2)) x = true
    rw [a267872_step_eq, ih, ih, ih]
    decide

theorem a267872_a_of_two_le (n : ℕ) (hn : 2 ≤ n) : a n = 2 * n + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold a onCount
  simp only [a267872_state_add_two, Bool.toNat_true, Finset.sum_const, Finset.card_range,
    smul_eq_mul, mul_one]

theorem a267872_a_zero : a 0 = 1 := by
  unfold a onCount
  simp [state]

theorem a267872_a_one : a 1 = 1 := by
  unfold a onCount
  simp [Finset.sum_range_succ, a267872_state_one]

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a267872.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    rw [OMA.Helpers.a267872_a_of_two_le n (by omega),
      OMA.Helpers.a267872_a_of_two_le (n - 1) (by omega),
      OMA.Helpers.a267872_a_of_two_le (n - 2) (by omega)]
    omega
  · unfold OMA.S_oeis_a267872.A
    rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    set f : PowerSeries ℚ := PowerSeries.mk (fun n => (OMA.S_oeis_a267872.a n : ℚ)) with hf
    have e1 : f * (1 - PowerSeries.X) ^ 2
        = f - f * PowerSeries.X ^ 1 - f * PowerSeries.X ^ 1 + f * PowerSeries.X ^ 2 := by ring
    have e2 : (1 - PowerSeries.X + 4 * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 : PowerSeries ℚ)
        = PowerSeries.X ^ 0 - PowerSeries.X ^ 1
          + (PowerSeries.X ^ 2 + PowerSeries.X ^ 2 + PowerSeries.X ^ 2 + PowerSeries.X ^ 2)
          - (PowerSeries.X ^ 3 + PowerSeries.X ^ 3) := by ring
    rw [e1, e2]
    ext k
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', hf, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow]
    rcases k with _ | _ | _ | _ | k
    · simp [OMA.Helpers.a267872_a_zero]
    · simp [OMA.Helpers.a267872_a_zero, OMA.Helpers.a267872_a_one]
    · simp [OMA.Helpers.a267872_a_zero, OMA.Helpers.a267872_a_one,
        OMA.Helpers.a267872_a_of_two_le 2 le_rfl]
      norm_num
    · simp [OMA.Helpers.a267872_a_one, OMA.Helpers.a267872_a_of_two_le 2 le_rfl,
        OMA.Helpers.a267872_a_of_two_le 3 (by norm_num)]
      norm_num
    · have h4 := OMA.Helpers.a267872_a_of_two_le (k + 1 + 1 + 1 + 1) (by omega)
      have h3 := OMA.Helpers.a267872_a_of_two_le (k + 1 + 1 + 1 + 1 - 1) (by omega)
      have h2 := OMA.Helpers.a267872_a_of_two_le (k + 1 + 1 + 1 + 1 - 2) (by omega)
      have q4 : ((OMA.S_oeis_a267872.a (k + 1 + 1 + 1 + 1) : ℕ) : ℚ) = 2 * (k + 4 : ℚ) + 1 := by
        rw [h4]; push_cast; ring
      have q3 : ((OMA.S_oeis_a267872.a (k + 1 + 1 + 1 + 1 - 1) : ℕ) : ℚ) = 2 * (k + 3 : ℚ) + 1 := by
        rw [h3]; rw [show k + 1 + 1 + 1 + 1 - 1 = k + 3 by omega]; push_cast; ring
      have q2 : ((OMA.S_oeis_a267872.a (k + 1 + 1 + 1 + 1 - 2) : ℕ) : ℚ) = 2 * (k + 2 : ℚ) + 1 := by
        rw [h2]; rw [show k + 1 + 1 + 1 + 1 - 2 = k + 2 by omega]; push_cast; ring
      split_ifs <;> first | contradiction | omega | (rw [q4, q3, q2]; ring)
