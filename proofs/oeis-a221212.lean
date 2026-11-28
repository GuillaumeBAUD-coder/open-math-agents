import OMAStatements.S_oeis_a221212
import Mathlib

open OMA.S_oeis_a221212 PowerSeries

namespace P221212

theorem phi_bounds : (1.6 : ℝ) < Real.goldenRatio ∧ Real.goldenRatio < 1.62 := by
  have h5 : Real.sqrt 5 < 2.24 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h5' : (2.2 : ℝ) < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  unfold Real.goldenRatio
  constructor <;> linarith

theorem x2 : x 2 = Real.goldenRatio + 1 := rfl
theorem x3 : x 3 = Real.goldenRatio + 2 := rfl
theorem x4 : x 4 = 3 * Real.goldenRatio + 2 := by
  show (if (0 + 4) % 2 = 0 then (Nat.fib (0 + 4) : ℝ) * Real.goldenRatio + Nat.fib (0 + 3) else x (0 + 3) + x (0 + 1)) = _
  norm_num [Nat.fib_add_two]
theorem x6 : x 6 = 8 * Real.goldenRatio + 5 := by
  show (if (2 + 4) % 2 = 0 then (Nat.fib (2 + 4) : ℝ) * Real.goldenRatio + Nat.fib (2 + 3) else x (2 + 3) + x (2 + 1)) = _
  norm_num [Nat.fib_add_two]
theorem x5 : x 5 = 4 * Real.goldenRatio + 3 := by
  show (if (1 + 4) % 2 = 0 then (Nat.fib (1 + 4) : ℝ) * Real.goldenRatio + Nat.fib (1 + 3) else x (1 + 3) + x (1 + 1)) = _
  rw [if_neg (by norm_num)]
  rw [show 1 + 3 = 4 from rfl, show 1 + 1 = 2 from rfl, x4, x2]
  ring
theorem x7 : x 7 = 11 * Real.goldenRatio + 7 := by
  show (if (3 + 4) % 2 = 0 then (Nat.fib (3 + 4) : ℝ) * Real.goldenRatio + Nat.fib (3 + 3) else x (3 + 3) + x (3 + 1)) = _
  rw [if_neg (by norm_num)]
  rw [show 3 + 3 = 6 from rfl, show 3 + 1 = 4 from rfl, x6, x4]
  ring

theorem r (y : ℝ) (z : ℤ) (h1 : (z : ℝ) - 1 / 2 ≤ y) (h2 : y < (z : ℝ) + 1 / 2) : round y = z := by
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> linarith

theorem a3 : a 3 = 4 := by
  obtain ⟨h1, h2⟩ := phi_bounds
  unfold a; rw [x3]; exact r _ _ (by push_cast; linarith) (by push_cast; linarith)
theorem a5 : a 5 = 9 := by
  obtain ⟨h1, h2⟩ := phi_bounds
  unfold a; rw [x5]; exact r _ _ (by push_cast; linarith) (by push_cast; linarith)
theorem a7 : a 7 = 25 := by
  obtain ⟨h1, h2⟩ := phi_bounds
  unfold a; rw [x7]; exact r _ _ (by push_cast; linarith) (by push_cast; linarith)

end P221212

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a221212.main) := by
  intro h
  have := h.1 7 (by norm_num)
  rw [show (7 : ℕ) - 2 = 5 from rfl, show (7 : ℕ) - 4 = 3 from rfl, P221212.a7, P221212.a5,
    P221212.a3] at this
  norm_num at this
