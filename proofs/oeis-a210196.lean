import OMAStatements.S_oeis_a210196
import Mathlib

-- Proof of Knud Werner's conjecture in OEIS A210196 (statement by @ivillar).
-- Idea: with s(n) = u(n,x) + v(n,x) one has x*s(n) = (1+2x)^n - 1, hence v(n+1,x) = 2(1+2x)^n - 1.

namespace OMAA210196Helpers

open Polynomial OMA.S_oeis_a210196

theorem s_eq (n : ℕ) : X * (u (n + 1) + v (n + 1)) = (1 + 2 * X) ^ (n + 1) - 1 := by
  induction n with
  | zero => simp [u, v]; ring
  | succ n ih =>
    rw [u, v]
    linear_combination (1 + 2 * X) * ih

theorem v_eq (n : ℕ) : v (n + 1) = 2 * (1 + 2 * X : ℤ[X]) ^ n - 1 := by
  cases n with
  | zero => simp [v]; ring
  | succ n =>
    rw [v]
    linear_combination 2 * s_eq n

theorem coeff_pow (n k : ℕ) : ((1 + 2 * X : ℤ[X]) ^ n).coeff k = 2 ^ k * (n.choose k : ℤ) := by
  induction n generalizing k with
  | zero => cases k <;> simp [Polynomial.coeff_one]
  | succ n ih =>
    rw [pow_succ, mul_add, mul_one]
    cases k with
    | zero => simp [ih, mul_comm]
    | succ k =>
      rw [coeff_add, show (1 + 2 * X : ℤ[X]) ^ n * (2 * X) = (2 * (1 + 2 * X) ^ n) * X by ring,
        coeff_mul_X, ih, coeff_ofNat_mul, ih, Nat.choose_succ_succ']
      push_cast; ring

end OMAA210196Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a210196.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [OMA.S_oeis_a210196.T, OMAA210196Helpers.v_eq, Nat.add_sub_cancel]
  refine ⟨?_, fun k hk _ => ?_⟩
  · rw [Polynomial.coeff_sub, Polynomial.coeff_ofNat_mul, OMAA210196Helpers.coeff_pow]; simp
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Polynomial.coeff_sub, Polynomial.coeff_ofNat_mul, OMAA210196Helpers.coeff_pow,
      Polynomial.coeff_one]
    simp; ring
