import OMAStatements.S_oeis_a383702

open Polynomial

private lemma row_succ (k : ℕ) :
    OMA.S_oeis_a383702.row (k + 1) =
      OMA.S_oeis_a383702.row k * (X + C (4 * (k : ℤ) + 3)) := by
  unfold OMA.S_oeis_a383702.row
  exact Finset.prod_range_succ _ k

private lemma coeff_step_0 (p : Polynomial ℤ) (c : ℤ) :
    (p * (X + C c)).coeff 0 = c * p.coeff 0 := by
  rw [mul_add, coeff_add, coeff_mul_X_zero, coeff_mul_C, zero_add, mul_comm]

private lemma coeff_step_1 (p : Polynomial ℤ) (c : ℤ) :
    (p * (X + C c)).coeff 1 = p.coeff 0 + c * p.coeff 1 := by
  rw [mul_add, coeff_add, show (1 : ℕ) = 0 + 1 from rfl, coeff_mul_X, coeff_mul_C,
    mul_comm (p.coeff 1) c]

private lemma coeff_step_2 (p : Polynomial ℤ) (c : ℤ) :
    (p * (X + C c)).coeff 2 = p.coeff 1 + c * p.coeff 2 := by
  rw [mul_add, coeff_add, show (2 : ℕ) = 1 + 1 from rfl, coeff_mul_X, coeff_mul_C,
    mul_comm (p.coeff 2) c]

theorem OMA.solution : type_of% @OMA.S_oeis_a383702.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 3 := ⟨n - 3, by omega⟩
  have h1 : m + 3 - 1 = m + 2 := by omega
  have h2 : m + 3 - 2 = m + 1 := by omega
  have h3 : m + 3 - 3 = m := by omega
  rw [h1, h2, h3]
  unfold OMA.S_oeis_a383702.a
  rw [row_succ (m + 2), coeff_step_2,
      row_succ (m + 1), coeff_step_1, coeff_step_2,
      row_succ m, coeff_step_0, coeff_step_1, coeff_step_2]
  push_cast
  ring
