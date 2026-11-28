import OMAReductions.R_oeis_a270006_R1
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Code 5 on the von Neumann neighbourhood: at step 1 every cell except the origin is ON, and from step 2 on
-- the whole plane alternates (all OFF at even steps, all ON at odd steps), by induction with the state as a constant function.
-- Hence a n = 0 for even n and (2n+1)^2 for odd n >= 2; the recurrence and g.f. follow by parity and coefficient comparison.

namespace OMA.R_oeis_a270006_R1_Proof

open OMA.S_oeis_a270006 OMA.R_oeis_a270006_R1
open PowerSeries

theorem cell_succ (code t : ℕ) (i j : ℤ) : cell code (t + 1) i j =
    code.testBit ((cell code t i j).toNat + 2 * ((cell code t (i + 1) j).toNat +
      (cell code t (i - 1) j).toNat + (cell code t i (j + 1)).toNat +
      (cell code t i (j - 1)).toNat)) := rfl

theorem dif (p : Prop) [Decidable p] : decide p = if p then true else false := by
  split_ifs with h <;> simp [h]

theorem s1 (i j : ℤ) : cell 5 (0 + 1) i j = !decide (i = 0 ∧ j = 0) := by
  rw [cell_succ]
  simp only [cell, dif]
  split_ifs <;> first | decide | omega

theorem s2 (i j : ℤ) : cell 5 (1 + 1) i j = false := by
  rw [cell_succ]
  simp only [s1, dif]
  split_ifs <;> first | decide | omega

theorem alt : ∀ t, 2 ≤ t → cell 5 t = fun _ _ => decide (t % 2 = 1) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => funext i j; rw [s2]; decide
  | succ t ht ih =>
    funext i j
    rw [cell_succ, ih]
    by_cases h : t % 2 = 1
    · have h' : ¬ ((t + 1) % 2 = 1) := by omega
      simp only [h, h', decide_true, decide_false]
      decide
    · have h' : (t + 1) % 2 = 1 := by omega
      simp only [h, h', decide_true, decide_false]
      decide

theorem count (n : ℕ) (hn : 2 ≤ n) : onCount 5 n = if n % 2 = 1 then (2 * n + 1) ^ 2 else 0 := by
  by_cases h : n % 2 = 1 <;> simp [onCount, alt n hn, h, Finset.sum_const, pow_two]

theorem qform (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℚ) = if n % 2 = 1 then (2 * (n : ℚ) + 1) ^ 2 else 0 := by
  unfold a
  rw [count n hn]
  split_ifs <;> push_cast <;> ring

theorem a0 : (a 0 : ℚ) = 1 := by
  have : a 0 = 1 := by unfold a onCount; decide +kernel
  rw [this]; norm_num

theorem a1 : (a 1 : ℚ) = 8 := by
  have hc : cell 5 1 = fun i j => !decide (i = 0 ∧ j = 0) := funext fun i => funext fun j => s1 i j
  have : a 1 = 8 := by unfold a onCount; rw [hc]; decide +kernel
  rw [this]; norm_num

theorem rec (n : ℕ) (hn : 8 ≤ n) : (a n : ℚ) = 3 * a (n - 2) - 3 * a (n - 4) + a (n - 6) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  rw [show m + 8 - 2 = m + 6 by omega, show m + 8 - 4 = m + 4 by omega,
    show m + 8 - 6 = m + 2 by omega, qform (m + 8) (by omega), qform (m + 6) (by omega),
    qform (m + 4) (by omega), qform (m + 2) (by omega)]
  by_cases h : m % 2 = 1
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    push_cast; ring
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    ring

theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) ^ 3 : PowerSeries ℚ) =
    1 + 8 * X - 3 * X ^ 2 + 25 * X ^ 3 + 3 * X ^ 4 - 2 * X ^ 5 - X ^ 6 + X ^ 7 := by
  set A := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have hD : A * ((1 - X) ^ 3 * (1 + X) ^ 3) =
      A - C 3 * (A * X ^ 2) + C 3 * (A * X ^ 4) - A * X ^ 6 := by
    simp only [map_ofNat]; ring
  have hN : (1 + 8 * X - 3 * X ^ 2 + 25 * X ^ 3 + 3 * X ^ 4 - 2 * X ^ 5 - X ^ 6 + X ^ 7 : ℚ⟦X⟧) =
      C 1 * X ^ 0 + C 8 * X ^ 1 - C 3 * X ^ 2 + C 25 * X ^ 3 + C 3 * X ^ 4 - C 2 * X ^ 5 -
        C 1 * X ^ 6 + C 1 * X ^ 7 := by
    simp only [map_ofNat, map_one, one_mul, pow_one, pow_zero, mul_one]
  rw [hD, hN]
  apply PowerSeries.ext
  intro n
  simp only [map_sub, map_add, coeff_C_mul_X_pow, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk]
  by_cases hn : n < 8
  · have q2 := qform 2 (by norm_num)
    have q3 := qform 3 (by norm_num)
    have q4 := qform 4 (by norm_num)
    have q5 := qform 5 (by norm_num)
    have q6 := qform 6 (by norm_num)
    have q7 := qform 7 (by norm_num)
    norm_num at q2 q3 q4 q5 q6 q7
    interval_cases n <;> norm_num [a0, a1, q2, q3, q4, q5, q6, q7]
  · have h := rec n (by omega)
    simp (disch := omega) only [coeff_C, if_pos, if_neg]
    linarith only [h]

theorem h1 : OMA.R_oeis_a270006_R1.H1 := by
  intro n hn
  rw [qform n hn]
  rcases Nat.even_or_odd n with he | ho
  · rw [if_neg (by have := Nat.even_iff.mp he; omega), he.neg_one_pow]; ring
  · rw [if_pos (Nat.odd_iff.mp ho), ho.neg_one_pow]; ring

theorem h2 : OMA.R_oeis_a270006_R1.H2 := by
  intro n hn he
  rw [qform n hn, if_neg (by have := Nat.even_iff.mp he; omega)]

theorem h3 : OMA.R_oeis_a270006_R1.H3 := by
  intro n hn ho
  rw [qform n hn, if_pos (Nat.odd_iff.mp ho)]

theorem h4 : OMA.R_oeis_a270006_R1.H4 := ⟨rec, gf⟩

end OMA.R_oeis_a270006_R1_Proof

theorem OMA.solution : OMA.R_oeis_a270006_R1.H2 := OMA.R_oeis_a270006_R1_Proof.h2
