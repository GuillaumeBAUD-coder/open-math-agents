import OMAStatements.S_oeis_a296516
import Mathlib

open OMA.S_oeis_a296516 PowerSeries

noncomputable def P296516.f (m : ℕ) : ℚ := (Nat.fib (2 * m + 1) : ℚ)
noncomputable def P296516.g (m : ℕ) : ℚ := (Nat.fib (m + 2) : ℚ)

theorem P296516.hF (m : ℕ) : P296516.f (m + 2) = 3 * P296516.f (m + 1) - P296516.f m := by
  unfold P296516.f
  have e1 : Nat.fib (2 * (m + 2) + 1) = Nat.fib (2 * m + 4) + Nat.fib (2 * m + 3) := by
    rw [show 2 * (m + 2) + 1 = 2 * m + 3 + 2 by ring, Nat.fib_add_two]; ring_nf
  have e2 : Nat.fib (2 * m + 4) = Nat.fib (2 * m + 3) + Nat.fib (2 * m + 2) := by
    rw [show 2 * m + 4 = 2 * m + 2 + 2 by ring, Nat.fib_add_two]; ring_nf
  have e3 : Nat.fib (2 * m + 3) = Nat.fib (2 * m + 2) + Nat.fib (2 * m + 1) := by
    rw [show 2 * m + 3 = 2 * m + 1 + 2 by ring, Nat.fib_add_two]; ring_nf
  rw [e1, show 2 * (m + 1) + 1 = 2 * m + 3 by ring]
  push_cast
  rw [e2, e3]
  push_cast
  ring

theorem P296516.hG (m : ℕ) : P296516.g (m + 2) = P296516.g (m + 1) + P296516.g m := by
  unfold P296516.g
  rw [show m + 2 + 2 = (m + 2) + 2 by ring, Nat.fib_add_two]
  push_cast
  ring_nf

theorem P296516.hb (m : ℕ) (hm : 1 ≤ m) :
    a m = (P296516.f m + P296516.g m - (m : ℚ) ^ 2 + (m : ℚ) - 2) / 2 := by
  simp only [a, P296516.f, P296516.g, show m ≠ 0 by omega, if_false]

theorem P296516.rec8 (m : ℕ) : a (m + 8) - 7 * a (m + 7) + 18 * a (m + 6) - 20 * a (m + 5) + 6 * a (m + 4) +
    6 * a (m + 3) - 5 * a (m + 2) + a (m + 1) = 0 := by
  have b1 := P296516.hb (m + 1) (by omega)
  have b2 := P296516.hb (m + 2) (by omega)
  have b3 := P296516.hb (m + 3) (by omega)
  have b4 := P296516.hb (m + 4) (by omega)
  have b5 := P296516.hb (m + 5) (by omega)
  have b6 := P296516.hb (m + 6) (by omega)
  have b7 := P296516.hb (m + 7) (by omega)
  have b8 := P296516.hb (m + 8) (by omega)
  rw [b1, b2, b3, b4, b5, b6, b7, b8]
  have f8 : P296516.f (m + 8) = 3 * P296516.f (m + 7) - P296516.f (m + 6) := P296516.hF (m + 6)
  have f7 : P296516.f (m + 7) = 3 * P296516.f (m + 6) - P296516.f (m + 5) := P296516.hF (m + 5)
  have f6 : P296516.f (m + 6) = 3 * P296516.f (m + 5) - P296516.f (m + 4) := P296516.hF (m + 4)
  have f5 : P296516.f (m + 5) = 3 * P296516.f (m + 4) - P296516.f (m + 3) := P296516.hF (m + 3)
  have f4 : P296516.f (m + 4) = 3 * P296516.f (m + 3) - P296516.f (m + 2) := P296516.hF (m + 2)
  have f3 : P296516.f (m + 3) = 3 * P296516.f (m + 2) - P296516.f (m + 1) := P296516.hF (m + 1)
  have g8 : P296516.g (m + 8) = P296516.g (m + 7) + P296516.g (m + 6) := P296516.hG (m + 6)
  have g7 : P296516.g (m + 7) = P296516.g (m + 6) + P296516.g (m + 5) := P296516.hG (m + 5)
  have g6 : P296516.g (m + 6) = P296516.g (m + 5) + P296516.g (m + 4) := P296516.hG (m + 4)
  have g5 : P296516.g (m + 5) = P296516.g (m + 4) + P296516.g (m + 3) := P296516.hG (m + 3)
  have g4 : P296516.g (m + 4) = P296516.g (m + 3) + P296516.g (m + 2) := P296516.hG (m + 2)
  have g3 : P296516.g (m + 3) = P296516.g (m + 2) + P296516.g (m + 1) := P296516.hG (m + 1)
  rw [f8, f7, f6, f5, f4, f3, g8, g7, g6, g5, g4, g3]
  push_cast
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a296516.main := by
  refine ⟨?_, ?_⟩
  · have hL : (PowerSeries.mk a * ((1 - X) ^ 3 * (1 - 3 * X + X ^ 2) * (1 - X - X ^ 2)) : PowerSeries ℚ) = PowerSeries.mk a - C (7 : ℚ) * (PowerSeries.mk a * X ^ 1) + C (18 : ℚ) * (PowerSeries.mk a * X ^ 2) - C (20 : ℚ) * (PowerSeries.mk a * X ^ 3) + C (6 : ℚ) * (PowerSeries.mk a * X ^ 4) + C (6 : ℚ) * (PowerSeries.mk a * X ^ 5) - C (5 : ℚ) * (PowerSeries.mk a * X ^ 6) + (PowerSeries.mk a * X ^ 7) := by
      (try simp only [map_ofNat, map_one, map_neg, one_mul, pow_one]) <;> ring
    have hR : ((1 - X) ^ 3 * (1 - 3 * X + X ^ 2) * (1 - X - X ^ 2) + X * (1 - 5 * X + 9 * X ^ 2 - 5 * X ^ 3 - 2 * X ^ 4 + X ^ 5) : PowerSeries ℚ) = 1 - C (6 : ℚ) * X ^ 1 + C (13 : ℚ) * X ^ 2 - C (11 : ℚ) * X ^ 3 + X ^ 4 + C (4 : ℚ) * X ^ 5 - C (4 : ℚ) * X ^ 6 + X ^ 7 := by
      (try simp only [map_ofNat, map_one, map_neg, one_mul, pow_one]) <;> ring
    rw [hL, hR]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk,
      coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | n
    · norm_num [a, Nat.fib_add_two]
    · norm_num [a, Nat.fib_add_two]
    · norm_num [a, Nat.fib_add_two]
    · norm_num [a, Nat.fib_add_two]
    · norm_num [a, Nat.fib_add_two]
    · norm_num [a, Nat.fib_add_two]
    · norm_num [a, Nat.fib_add_two]
    · norm_num [a, Nat.fib_add_two]
    · simp only [show n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 8 by omega]
      simp only [show n + 8 - 1 = n + 7 by omega, show n + 8 - 2 = n + 6 by omega, show n + 8 - 3 = n + 5 by omega, show n + 8 - 4 = n + 4 by omega, show n + 8 - 5 = n + 3 by omega, show n + 8 - 6 = n + 2 by omega, show n + 8 - 7 = n + 1 by omega]
      try simp only [show (n + 8 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 8 = 1) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 8 = 2) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 8 = 3) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 8 = 4) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 8 = 5) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 8 = 6) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 8 = 7) = False by simp only [eq_iff_iff, iff_false]; omega, if_false]
      try simp only [show 1 ≤ n + 8 by omega, show 2 ≤ n + 8 by omega, show 3 ≤ n + 8 by omega, show 4 ≤ n + 8 by omega, show 5 ≤ n + 8 by omega, show 6 ≤ n + 8 by omega, show 7 ≤ n + 8 by omega, if_true]
      try simp only [show (n + 1 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 2 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 3 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 4 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 5 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 6 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 7 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 8 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, if_false]
      have h := P296516.rec8 n
      linear_combination h
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega, show m + 8 - 3 = m + 5 by omega,
      show m + 8 - 4 = m + 4 by omega, show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega,
      show m + 8 - 7 = m + 1 by omega]
    linear_combination P296516.rec8 m
