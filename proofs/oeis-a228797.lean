import OMAStatements.S_oeis_a228797
import Mathlib

namespace OMA.A228797Proof

open OMA.S_oeis_a228797

lemma total_succ (n : ℕ) : (state (n + 1)).total
    = (state n).total + 3 * (state n).bothZero + (state n).bottomOnly := by
  simp only [state, extend, Columns.total]
  ring

lemma zero_succ (n : ℕ) : (state (n + 1)).bothZero = (state n).total := by
  simp only [state, extend]

lemma bottom_succ (n : ℕ) : (state (n + 1)).bottomOnly = (state n).bothZero := by
  simp only [state, extend]

lemma zero_eq (n : ℕ) : (state n).bothZero = a n := by
  cases n with
  | zero => simp [state, a]
  | succ k => rw [zero_succ]; rfl

lemma a_rec (n : ℕ) : a (n + 3) = a (n + 2) + 3 * a (n + 1) + a n := by
  have h : a (n + 3) = (state (n + 2)).total := rfl
  have h2 : a (n + 2) = (state (n + 1)).total := rfl
  rw [h, total_succ, bottom_succ, zero_eq, zero_eq, h2]

lemma cf_rec (n : ℕ) : closedForm (n + 3)
    = closedForm (n + 2) + 3 * closedForm (n + 1) + closedForm n := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold closedForm
  linear_combination
    ((1 - Real.sqrt 2) ^ n * (2 - Real.sqrt 2) + (1 + Real.sqrt 2) ^ n * (Real.sqrt 2 + 2)) / 2 * hs

lemma a_eq_cf (n : ℕ) : (a n : ℝ) = closedForm n ∧ (a (n + 1) : ℝ) = closedForm (n + 1)
    ∧ (a (n + 2) : ℝ) = closedForm (n + 2) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · simp [a, closedForm]; norm_num
    · simp [a, state, Columns.total, closedForm]; ring
    · simp [a, state, extend, Columns.total, closedForm]
      linear_combination (-1 : ℝ) * hs
  | succ k ih =>
    refine ⟨ih.2.1, ih.2.2, ?_⟩
    rw [a_rec, cf_rec]
    push_cast
    rw [ih.1, ih.2.1, ih.2.2]

end OMA.A228797Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a228797.main := by
  refine ⟨?_, ?_⟩
  · intro n
    match n with
    | 0 => simp [OMA.S_oeis_a228797.productCoeff, OMA.S_oeis_a228797.a]
    | 1 => simp [OMA.S_oeis_a228797.productCoeff, OMA.S_oeis_a228797.a,
        OMA.S_oeis_a228797.state, OMA.S_oeis_a228797.Columns.total]
    | 2 => simp [OMA.S_oeis_a228797.productCoeff, OMA.S_oeis_a228797.a,
        OMA.S_oeis_a228797.state, OMA.S_oeis_a228797.extend, OMA.S_oeis_a228797.Columns.total]
    | k + 3 =>
      have h := OMA.A228797Proof.a_rec k
      simp only [OMA.S_oeis_a228797.productCoeff]
      have : k + 3 ≠ 1 := by omega
      rw [if_neg this, h]
      ring
  · intro n _
    exact (OMA.A228797Proof.a_eq_cf n).1
