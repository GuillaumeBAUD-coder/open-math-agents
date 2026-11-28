import OMAStatements.S_oeis_a267872

/-!
Proof of the two conjectures of OEIS A267872 (Rule 237 started from a single ON cell).

Rule 237 sends a neighbourhood to OFF only for 100 and 001. Hence row 1 is ON everywhere
except at x = -1 and x = 1, row 2 is ON everywhere, and since 111 goes to 1 every later row
stays all ON. So a(0) = a(1) = 1 and a(n) = 2n + 1 for n ≥ 2, and both the recurrence (for
n > 3) and the generating-function identity follow by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a267872

/-- Rule 237 in closed form: the next state is OFF only for the neighbourhoods 100 and 001. -/
theorem a267872_rule_eq (l c r : Bool) : rule l c r = (c || l == r) := by
  cases l <;> cases c <;> cases r <;> decide

/-- Row 1: every cell is ON except the two neighbours of the origin. -/
theorem a267872_state_one (x : ℤ) : state 1 x = decide (x ≠ 1 ∧ x ≠ -1) := by
  show rule (decide (x - 1 = 0)) (decide (x = 0)) (decide (x + 1 = 0)) = decide (x ≠ 1 ∧ x ≠ -1)
  rw [a267872_rule_eq]
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
theorem a267872_state_two (x : ℤ) : state 2 x = true := by
  show rule (state 1 (x - 1)) (state 1 x) (state 1 (x + 1)) = true
  rw [a267872_rule_eq]
  simp only [a267872_state_one]
  by_cases h1 : x = 1
  · subst h1; decide
  · by_cases h2 : x = -1
    · subst h2; decide
    · simp [h1, h2]

/-- From time 2 on, every cell is ON, since rule 237 sends 111 to 1. -/
theorem a267872_state_add_two (n : ℕ) (x : ℤ) : state (n + 2) x = true := by
  induction n generalizing x with
  | zero => exact a267872_state_two x
  | succ k ih =>
    show rule (state (k + 2) (x - 1)) (state (k + 2) x) (state (k + 2) (x + 1)) = true
    rw [ih, ih, ih]
    decide

theorem a267872_a_of_two_le (n : ℕ) (hn : 2 ≤ n) : a n = 2 * n + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold a
  rw [Finset.filter_true_of_mem (fun x _ => a267872_state_add_two m x), Int.card_Icc]
  omega

theorem a267872_a_zero : a 0 = 1 := by
  unfold a
  have h : (Finset.Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ)).filter (fun x => state 0 x = true)
      = {0} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, -⟩
      push_cast at h1 h2
      omega
    · rintro rfl
      decide
  rw [h, Finset.card_singleton]

theorem a267872_a_one : a 1 = 1 := by
  unfold a
  have h : (Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ)).filter (fun x => state 1 x = true)
      = {0} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, a267872_state_one,
      decide_eq_true_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      push_cast at h1 h2
      omega
    · rintro rfl
      decide
  rw [h, Finset.card_singleton]

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a267872.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    rw [OMA.Helpers.a267872_a_of_two_le n (by omega),
      OMA.Helpers.a267872_a_of_two_le (n - 1) (by omega),
      OMA.Helpers.a267872_a_of_two_le (n - 2) (by omega)]
    omega
  · set f : PowerSeries ℤ := PowerSeries.mk (fun n => (OMA.S_oeis_a267872.a n : ℤ)) with hf
    have e1 : f * (1 - PowerSeries.X) ^ 2
        = f - f * PowerSeries.X ^ 1 - f * PowerSeries.X ^ 1 + f * PowerSeries.X ^ 2 := by ring
    have e2 : (1 - PowerSeries.X + 4 * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 : PowerSeries ℤ)
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
    · simp [OMA.Helpers.a267872_a_one, OMA.Helpers.a267872_a_of_two_le 2 le_rfl,
        OMA.Helpers.a267872_a_of_two_le 3 (by norm_num)]
    · have h4 := OMA.Helpers.a267872_a_of_two_le (k + 1 + 1 + 1 + 1) (by omega)
      have h3 := OMA.Helpers.a267872_a_of_two_le (k + 1 + 1 + 1 + 1 - 1) (by omega)
      have h2 := OMA.Helpers.a267872_a_of_two_le (k + 1 + 1 + 1 + 1 - 2) (by omega)
      split_ifs <;> first | contradiction | omega
