import OMAStatements.S_oeis_a002660
import Mathlib

-- Proof of Sean A. Irvine's conjecture in OEIS A002660 (statement by @ivillar).
-- Idea: (x + 2x^2 + 2x^3 - 2x^4)/(1 - x)^2 has coefficients b(d) = d^2 for 1 ≤ d ≤ 3 and
-- b(d) = 3d for d ≥ 4, so Σ_{d | n} b(d) is exactly the defining sum of a(n).

namespace OMAA002660Helpers

open PowerSeries OMA.S_oeis_a002660

def b (m : ℕ) : ℚ := if m = 0 then 0 else if m ≤ 3 then (m : ℚ) ^ 2 else 3 * m

theorem key : mk b * (1 - X) ^ 2 = (X + 2 * X ^ 2 + 2 * X ^ 3 - 2 * X ^ 4 : PowerSeries ℚ) := by
  have e1 : mk b * (1 - X : PowerSeries ℚ) ^ 2 = mk b - mk b * X ^ 1 - mk b * X ^ 1 + mk b * X ^ 2 := by
    ring
  have e2 : (X + 2 * X ^ 2 + 2 * X ^ 3 - 2 * X ^ 4 : PowerSeries ℚ) =
      X ^ 1 + X ^ 2 + X ^ 2 + X ^ 3 + X ^ 3 - X ^ 4 - X ^ 4 := by ring
  rw [e1, e2]
  ext n
  simp only [map_add, map_sub, coeff_mk, coeff_mul_X_pow', coeff_X_pow]
  rcases n with _ | _ | _ | _ | _ | _ | n
  · simp [b]
  · simp [b]
  · simp [b]; norm_num
  · simp [b]; norm_num
  · simp [b]; norm_num
  · simp [b]; norm_num
  · simp only [show n + 6 - 1 = n + 5 by omega, show n + 6 - 2 = n + 4 by omega, b]
    simp only [show ¬ (n + 6 = 0) by omega, show ¬ (n + 5 = 0) by omega, show ¬ (n + 4 = 0) by omega,
      show ¬ (n + 6 ≤ 3) by omega, show ¬ (n + 5 ≤ 3) by omega, show ¬ (n + 4 ≤ 3) by omega,
      show (1 ≤ n + 6) by omega, show (2 ≤ n + 6) by omega,
      show ¬ (n + 6 = 1) by omega, show ¬ (n + 6 = 2) by omega, show ¬ (n + 6 = 3) by omega,
      show ¬ (n + 6 = 4) by omega, if_true, if_false]
    push_cast; ring

theorem G_eq : G = mk b := by
  have h : constantCoeff ((1 - X : PowerSeries ℚ) ^ 2) ≠ 0 := by simp
  rw [G, ← key, mul_assoc, PowerSeries.mul_inv_cancel _ h, mul_one]

theorem sum_eq (n : ℕ) : (a n : ℚ) = ∑ d ∈ n.divisors, b d := by
  simp only [a, Finset.sum_filter]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  simp only [b, hd0, if_false]
  split_ifs <;> first | omega | ring

end OMAA002660Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a002660.main := by
  intro n _
  rw [OMAA002660Helpers.G_eq, OMAA002660Helpers.sum_eq n]
  simp only [PowerSeries.coeff_mk]
