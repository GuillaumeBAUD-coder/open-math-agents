import OMAStatements.S_oeis_a267884
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: Rule 233 from a single ON cell: stage 1 is ON except cells -1, 0, 1; stage 2 is ON
-- except -1 and 1; stage 3 is ON except 0; from stage 4 on every cell is ON (111 -> 1).
-- Each stage is checked cell by cell (finitely many cases near 0, the rest by a uniform rule),
-- so the OFF counts are 0, 3, 2, 1, 0, 0, ... and a(n) = 6 for n >= 3; the g.f. follows by
-- comparing coefficients of A * (1 - X).

open PowerSeries

namespace OMA.A267884Proof

open OMA.S_oeis_a267884

lemma s1 (x : ℤ) : state 233 1 x = decide (x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1) := by
  simp only [state, step]; (rcases (show x ≤ -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ 4 ≤ x by omega)
     with h|h|h|h|h|h|h|h|h <;>
   first
   | (subst h; decide)
   | (simp (disch := omega) only [decide_eq_true, decide_eq_false]; decide))
lemma s2 (x : ℤ) : state 233 2 x = decide (x ≠ -1 ∧ x ≠ 1) := by
  show step 233 (state 233 1) x = _
  simp only [step, s1]; (rcases (show x ≤ -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ 4 ≤ x by omega)
     with h|h|h|h|h|h|h|h|h <;>
   first
   | (subst h; decide)
   | (simp (disch := omega) only [decide_eq_true, decide_eq_false]; decide))
lemma s3 (x : ℤ) : state 233 3 x = decide (x ≠ 0) := by
  show step 233 (state 233 2) x = _
  simp only [step, s2]; (rcases (show x ≤ -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ 4 ≤ x by omega)
     with h|h|h|h|h|h|h|h|h <;>
   first
   | (subst h; decide)
   | (simp (disch := omega) only [decide_eq_true, decide_eq_false]; decide))
lemma s4 (x : ℤ) : state 233 4 x = true := by
  show step 233 (state 233 3) x = _
  simp only [step, s3]; (rcases (show x ≤ -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ 4 ≤ x by omega)
     with h|h|h|h|h|h|h|h|h <;>
   first
   | (subst h; decide)
   | (simp (disch := omega) only [decide_eq_true, decide_eq_false]; decide))
lemma sge (n : ℕ) (x : ℤ) : state 233 (n + 4) x = true := by
  induction n generalizing x with
  | zero => exact s4 x
  | succ n ih =>
    show step 233 (state 233 (n + 4)) x = _
    simp only [step, ih]; decide

lemma off_ge (n : ℕ) : offCount (state 233 (n + 4)) (n + 4) = 0 := by
  unfold offCount
  apply Finset.sum_eq_zero
  intro i _
  simp [sge]

lemma off0 : offCount (state 233 0) 0 = 0 := by decide
lemma off1 : offCount (state 233 1) 1 = 3 := by
  simp [offCount, Finset.sum_range_succ, s1]
lemma off2 : offCount (state 233 2) 2 = 2 := by
  simp [offCount, Finset.sum_range_succ, s2]
lemma off3 : offCount (state 233 3) 3 = 1 := by
  simp [offCount, Finset.sum_range_succ, s3]

lemma a_val (n : ℕ) : a (n + 3) = 6 := by
  induction n with
  | zero => simp [a, Finset.sum_range_succ, off0, off1, off2, off3]
  | succ n ih =>
    rw [a, Finset.sum_range_succ, ← a, ih, show n + 1 + 3 = n + 4 by ring, off_ge]

theorem main' :
    (∀ n : ℕ, 2 < n → a n = 6) ∧
    (∀ n : ℕ, 3 < n → a n = a (n - 1)) ∧
    A = X * (3 + 2 * X + X ^ 2) * (1 - X)⁻¹ := by
  have hv : ∀ n, 2 < n → a n = 6 := by
    intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
    exact a_val j
  refine ⟨hv, fun n hn => by rw [hv n (by omega), hv (n - 1) (by omega)], ?_⟩
  have a0 : a 0 = 0 := by simp [a, off0]
  have a1 : a 1 = 3 := by simp [a, Finset.sum_range_succ, off0, off1]
  have a2 : a 2 = 5 := by simp [a, Finset.sum_range_succ, off0, off1, off2]
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  have e : A * (1 - X) = A - A * X ^ 1 := by ring
  have e2 : X * (3 + 2 * X + X ^ 2) = C (3:ℚ) * X ^ 1 + C (2:ℚ) * X ^ 2 + X ^ 3 := by
    simp only [map_ofNat]; ring
  rw [e, e2]
  ext n
  simp only [A, map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_mk, coeff_C]
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with h | h | h | h | h
  · subst h; simp [a0]
  · subst h; simp [a0, a1]
  · subst h; simp [a1, a2]; norm_num
  · subst h; simp [a2, hv 3 (by norm_num)]; norm_num
  · rw [hv n (by omega), hv (n - 1) (by omega)]
    simp [show 1 ≤ n by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
      show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega]
end OMA.A267884Proof

open OMA.A267884Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a267884.main := main'
