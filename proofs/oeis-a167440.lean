import OMAStatements.S_oeis_a167440
import Mathlib

-- Proof of Colin Barker's conjectures in OEIS A167440 (statement by @ivillar).
-- Idea: T_5(x) = 16x^5 - 20x^3 + 5x, so a(n) = 2*T_5(2^(n-1)) = 32^n - 5*8^n + 5*2^n; the
-- recurrence and the g.f. follow from this closed form.

namespace OMAA167440Helpers

open Polynomial OMA.S_oeis_a167440

theorem T5 : Chebyshev.T ℚ 5 = 16 * X ^ 5 - 20 * X ^ 3 + 5 * X := by
  have h2 := Chebyshev.T_add_two ℚ 0
  have h3 := Chebyshev.T_add_two ℚ 1
  have h4 := Chebyshev.T_add_two ℚ 2
  have h5 := Chebyshev.T_add_two ℚ 3
  norm_num at h2 h3 h4 h5
  rw [h5, h4, h3, h2]
  ring

theorem a_closed (n : ℕ) (hn : 1 ≤ n) : a n = 2 ^ n * (5 - 5 * 4 ^ n + 16 ^ n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [a, gegenbauerC, Nat.cast_ofNat, T5, Nat.add_sub_cancel, eval_add, eval_sub, eval_mul,
    eval_pow, eval_X, eval_ofNat]
  have h4 : (4 : ℚ) ^ (m + 1) = ((2 : ℚ) ^ (m + 1)) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h16 : (16 : ℚ) ^ (m + 1) = ((2 : ℚ) ^ (m + 1)) ^ 4 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4, h16, pow_succ]
  ring

def g (n : ℕ) : ℚ := if n = 0 then 0 else 2 ^ n * (5 - 5 * 4 ^ n + 16 ^ n)

theorem key : PowerSeries.mk g *
    ((2 * PowerSeries.X - 1) * (8 * PowerSeries.X - 1) * (32 * PowerSeries.X - 1)) =
    -2 * PowerSeries.X * (256 * PowerSeries.X ^ 2 + 320 * PowerSeries.X + 1) := by
  set F := PowerSeries.mk g
  have e1 : F * ((2 * PowerSeries.X - 1) * (8 * PowerSeries.X - 1) * (32 * PowerSeries.X - 1)) =
      PowerSeries.C (512 : ℚ) * (PowerSeries.X ^ 3 * F) - PowerSeries.C (336 : ℚ) * (PowerSeries.X ^ 2 * F) +
        PowerSeries.C (42 : ℚ) * (PowerSeries.X ^ 1 * F) - F := by
    rw [map_ofNat PowerSeries.C 512, map_ofNat PowerSeries.C 336, map_ofNat PowerSeries.C 42]; ring
  have e2 : (-2 * PowerSeries.X * (256 * PowerSeries.X ^ 2 + 320 * PowerSeries.X + 1) : PowerSeries ℚ) =
      -(PowerSeries.C (512 : ℚ) * PowerSeries.X ^ 3) - PowerSeries.C (640 : ℚ) * PowerSeries.X ^ 2 -
        PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 1 := by
    rw [map_ofNat PowerSeries.C 512, map_ofNat PowerSeries.C 640, map_ofNat PowerSeries.C 2]; ring
  rw [e1, e2]
  ext n
  simp only [F, map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 3
  · interval_cases n <;> norm_num [g]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simp [g, pow_succ]
    ring

end OMAA167440Helpers

open Polynomial OMA.S_oeis_a167440 OMAA167440Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a167440.main := by
  refine ⟨a_closed, fun n hn => ?_, ?_⟩
  · rw [a_closed n (by omega), a_closed (n - 1) (by omega), a_closed (n - 2) (by omega),
      a_closed (n - 3) (by omega)]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega, show m + 3 - 3 = m by omega]
    ring
  · have hfun : (fun n => if n = 0 then 0 else a n) = g := by
      funext n
      by_cases h : n = 0
      · simp [h, g]
      · simp [h, g, a_closed n (by omega)]
    rw [hfun, G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp), key]

