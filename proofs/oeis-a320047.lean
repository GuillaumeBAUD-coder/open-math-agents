import OMAStatements.S_oeis_a320047
import Mathlib

open OMA.S_oeis_a320047 Polynomial

theorem Pstep (l : ℕ) : P (l + 1) = P l + (C (1 : ℚ) + C (6 : ℚ) * C ((l + 1 : ℕ) : ℚ) *
    (X - C ((l + 1 : ℕ) : ℚ))) := by
  simp only [P]
  rw [Finset.sum_Icc_succ_top (by omega)]
  congr 1
  simp [Finset.sum_range_succ, R]

theorem c01 (l : ℕ) : (P l).coeff 0 = -(2 * (l : ℚ) ^ 3 + 3 * (l : ℚ) ^ 2) ∧
    (P l).coeff 1 = 3 * (l : ℚ) * ((l : ℚ) + 1) := by
  induction l with
  | zero => simp [P]
  | succ l ih =>
    simp only [Pstep, coeff_add, ih.1, ih.2, mul_assoc, coeff_C_mul, coeff_C, coeff_X, coeff_sub,
      mul_sub]
    norm_num
    constructor <;> ring

theorem CF (n : ℕ) (hn : 0 < n) : a n = (4 - 4 * (-1) ^ n - 3 * (-5 + (-1) ^ n) * (n : ℚ) -
      3 * (-3 + (-1) ^ n) * (n : ℚ) ^ 2 + (1 + (-1) ^ (1 + n)) * (n : ℚ) ^ 3) / 8 := by
  rcases Nat.even_or_odd' n with ⟨l, rfl | rfl⟩
  · have hl : (2 * l) % 2 = 0 := by omega
    simp only [a, hl, U, (c01 _).2, show (2 * l) / 2 = l by omega]
    norm_num [pow_add, pow_mul]
    push_cast
    ring
  · have hl : (2 * l + 1) % 2 = 1 := by omega
    simp only [a, hl, U, (c01 _).1, show (2 * l + 1 + 1) / 2 = l + 1 by omega]
    norm_num [pow_add, pow_mul]
    push_cast
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a320047.main := by
  refine ⟨CF, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  simp only [show m + 9 - 2 = m + 7 by omega, show m + 9 - 4 = m + 5 by omega,
    show m + 9 - 6 = m + 3 by omega, show m + 9 - 8 = m + 1 by omega]
  rw [CF _ (by omega), CF _ (by omega), CF _ (by omega), CF _ (by omega), CF _ (by omega)]
  simp only [pow_add]
  push_cast
  norm_num
  ring
