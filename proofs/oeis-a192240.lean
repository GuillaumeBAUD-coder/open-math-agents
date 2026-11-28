import OMAStatements.S_oeis_a192240
import Mathlib

-- Proof of Rigoberto Florez's conjecture in OEIS A192240 (statement by @ivillar).
-- Idea: modulo x^2 - x - 1 we have (x-1)*x = 1, so (x-1)^i ≡ (-1)^i (F(i+1) - F(i)*x); expanding
-- (x+3)^n = ((x-1) + 4)^n by the binomial theorem gives the constant term of the reduction.

namespace OMAA192240Helpers

open Polynomial OMA.S_oeis_a192240

theorem hM : (X ^ 2 - X - 1 : ℤ[X]).Monic := by monicity!

/-- (x - 1)^i ≡ (-1)^i (F(i+1) - F(i) x) modulo x^2 - x - 1. -/
theorem dvd_pow (i : ℕ) : (X ^ 2 - X - 1 : ℤ[X]) ∣
    (X - 1) ^ i - (C ((-1) ^ i * (Nat.fib (i + 1) : ℤ)) - C ((-1) ^ i * (Nat.fib i : ℤ)) * X) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : (X - 1 : ℤ[X]) ^ (i + 1) -
        (C ((-1) ^ (i + 1) * (Nat.fib (i + 1 + 1) : ℤ)) - C ((-1) ^ (i + 1) * (Nat.fib (i + 1) : ℤ)) * X) =
        (X - 1) * ((X - 1) ^ i - (C ((-1) ^ i * (Nat.fib (i + 1) : ℤ)) -
          C ((-1) ^ i * (Nat.fib i : ℤ)) * X)) +
        (X ^ 2 - X - 1) * C ((-1) ^ (i + 1) * (Nat.fib i : ℤ)) := by
      rw [Nat.fib_add_two]
      simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
      push_cast
      ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_mul_right _ _)

theorem main_dvd (n : ℕ) : (X ^ 2 - X - 1 : ℤ[X]) ∣ (X + 3) ^ n -
    (C (∑ i ∈ Finset.range (n + 1), (-1) ^ i * (Nat.fib (i + 1) : ℤ) * (n.choose i : ℤ) * 4 ^ (n - i)) -
     C (∑ i ∈ Finset.range (n + 1), (-1) ^ i * (Nat.fib i : ℤ) * (n.choose i : ℤ) * 4 ^ (n - i)) * X) := by
  have e1 : (X + 3 : ℤ[X]) ^ n = ((X - 1) + 4) ^ n := by ring
  rw [e1, add_pow]
  have e2 : ∑ m ∈ Finset.range (n + 1), (X - 1 : ℤ[X]) ^ m * 4 ^ (n - m) * (n.choose m : ℤ[X]) -
      (C (∑ i ∈ Finset.range (n + 1), (-1) ^ i * (Nat.fib (i + 1) : ℤ) * (n.choose i : ℤ) * 4 ^ (n - i)) -
       C (∑ i ∈ Finset.range (n + 1), (-1) ^ i * (Nat.fib i : ℤ) * (n.choose i : ℤ) * 4 ^ (n - i)) * X) =
      ∑ m ∈ Finset.range (n + 1), C ((n.choose m : ℤ) * 4 ^ (n - m)) *
        ((X - 1) ^ m - (C ((-1) ^ m * (Nat.fib (m + 1) : ℤ)) - C ((-1) ^ m * (Nat.fib m : ℤ)) * X)) := by
    simp only [map_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_ofNat]
    ring
  rw [e2]
  exact Finset.dvd_sum (fun m _ => dvd_mul_of_dvd_right (dvd_pow m) _)

end OMAA192240Helpers

open Polynomial OMA.S_oeis_a192240 OMAA192240Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a192240.main := by
  intro n
  unfold a reduce
  rw [modByMonic_eq_of_dvd_sub hM (main_dvd n), (modByMonic_eq_self_iff hM).mpr]
  · rw [coeff_sub, coeff_C_zero, coeff_C_mul, coeff_X_zero, mul_zero, sub_zero]
  · have h2 : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by compute_degree!
    rw [h2, sub_eq_add_neg, ← neg_mul, ← map_neg, add_comm]
    exact degree_linear_lt
