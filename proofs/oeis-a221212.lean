import OMAStatements.S_oeis_a221212
import Mathlib

-- Problem: oeis-a221212 (disproof: the recurrence fails at n = 7)
-- Credit: @Aijy0264561
-- x 3 = phi + 2, x 5 = 4 phi + 3, x 7 = 11 phi + 7 round to 4, 9, 25 (1.6 < phi < 1.625), but
-- 3 * a 5 - a 3 = 23. Barker's g.f. is right; the recurrence it implies holds only for n > 9.

namespace OMA.A221212proof

open OMA.S_oeis_a221212

lemma phi_bounds : (1.6 : ℝ) < Real.goldenRatio ∧ Real.goldenRatio < 1.625 := by
  have h5 : (0 : ℝ) ≤ 5 := by norm_num
  have lo : (2.2 : ℝ) < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hi : Real.sqrt 5 < 2.25 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [Real.goldenRatio]
  constructor <;> linarith

lemma x3 : x 3 = Real.goldenRatio + 2 := by simp [x]
lemma x5 : x 5 = 4 * Real.goldenRatio + 3 := by
  simp [x, Nat.fib_add_two]; ring
lemma x7 : x 7 = 11 * Real.goldenRatio + 7 := by
  simp [x, Nat.fib_add_two]; ring

lemma round_of {y : ℝ} {k : ℤ} (h1 : (k : ℝ) - 1 / 2 ≤ y) (h2 : y < k + 1 / 2) : round y = k := by
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> linarith

lemma a3 : a 3 = 4 := by
  obtain ⟨l, h⟩ := phi_bounds
  unfold a; rw [x3]; exact round_of (by push_cast; linarith) (by push_cast; linarith)
lemma a5 : a 5 = 9 := by
  obtain ⟨l, h⟩ := phi_bounds
  unfold a; rw [x5]; exact round_of (by push_cast; linarith) (by push_cast; linarith)
lemma a7 : a 7 = 25 := by
  obtain ⟨l, h⟩ := phi_bounds
  unfold a; rw [x7]; exact round_of (by push_cast; linarith) (by push_cast; linarith)

theorem not_main : ¬ (type_of% @OMA.S_oeis_a221212.main) := by
  intro h
  have := h.1 7 (by norm_num)
  rw [show 7 - 2 = 5 from rfl, show 7 - 4 = 3 from rfl, a7, a5, a3] at this
  norm_num at this

end OMA.A221212proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a221212.main) := OMA.A221212proof.not_main
