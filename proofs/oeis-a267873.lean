import OMAStatements.S_oeis_a267873
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Disproof sketch: Rule 235 from a single ON cell gives stage 1 = ON except cells 0 and 1,
-- stage 2 = ON except cell 0, and every cell ON from stage 3 on. Hence a(2) = 4, a(3) = 7,
-- a(4) = 9, and the stated recurrence a(n) = 2 a(n-1) - a(n-2) fails at n = 4 (it would give 10).
-- The recurrence as stated in the OEIS entry (for n > 2) is off by two indices; it holds for
-- n > 4, and the generating function in the entry is consistent with the data.

namespace OMA.A267873Disproof

open OMA.S_oeis_a267873

lemma s1 (x : ℤ) : state 235 1 x = decide (x ≠ 0 ∧ x ≠ 1) := by
  show step 235 (state 235 0) x = _
  simp only [step, state]
  (rcases (show x ≤ -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ 4 ≤ x by omega)
     with h|h|h|h|h|h|h|h|h <;>
   first
   | (subst h; decide)
   | (simp (disch := omega) only [decide_eq_true, decide_eq_false]; decide))

lemma s2 (x : ℤ) : state 235 2 x = decide (x ≠ 0) := by
  show step 235 (state 235 1) x = _
  simp only [step, s1]
  (rcases (show x ≤ -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ 4 ≤ x by omega)
     with h|h|h|h|h|h|h|h|h <;>
   first
   | (subst h; decide)
   | (simp (disch := omega) only [decide_eq_true, decide_eq_false]; decide))

lemma s3 (x : ℤ) : state 235 3 x = true := by
  show step 235 (state 235 2) x = _
  simp only [step, s2]
  (rcases (show x ≤ -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ 4 ≤ x by omega)
     with h|h|h|h|h|h|h|h|h <;>
   first
   | (subst h; decide)
   | (simp (disch := omega) only [decide_eq_true, decide_eq_false]; decide))

lemma s4 (x : ℤ) : state 235 4 x = true := by
  show step 235 (state 235 3) x = _
  simp only [step, s3]
  decide

lemma a2 : a 2 = 4 := by simp [a, onCount, Finset.sum_range_succ, s2]
lemma a3 : a 3 = 7 := by simp [a, onCount, Finset.sum_range_succ, s3]
lemma a4 : a 4 = 9 := by simp [a, onCount, Finset.sum_range_succ, s4]

theorem not_main : ¬ ((∀ n : ℕ, 2 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2)) ∧
    A = (1 - PowerSeries.X + 3 * PowerSeries.X ^ 2 - PowerSeries.X ^ 4) *
      ((1 - PowerSeries.X) ^ 2)⁻¹) := by
  rintro ⟨h, -⟩
  have := h 4 (by norm_num)
  simp only [show 4 - 1 = 3 by rfl, show 4 - 2 = 2 by rfl, a2, a3, a4] at this
  norm_num at this

end OMA.A267873Disproof

open OMA.A267873Disproof in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267873.main) := not_main
