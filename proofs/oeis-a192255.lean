import OMAStatements.S_oeis_a192255
import Mathlib

/-!
Modulo q = x^2 - x - 1 one has x^(k+1) = F(k+1) x + F(k) (induction: x^(k+2) - (F(k+2) x + F(k+1))
= x (x^(k+1) - (F(k+1) x + F(k))) + F(k+1) q). Summing, p(n) is congruent to s0(n) + s1(n) x,
with s1(n) = Sum_{j=0..n} (j+1)^2 F(j); since this has degree < 2 it is the remainder.
-/

namespace R192255
open OMA.S_oeis_a192255 Polynomial

theorem hq : (X ^ 2 - X - 1 : ℤ[X]).Monic := by monicity!

theorem xpow (k : ℕ) : (X ^ 2 - X - 1 : ℤ[X]) ∣
    X ^ (k + 1) - (C (Nat.fib (k + 1) : ℤ) * X + C (Nat.fib k : ℤ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : (X : ℤ[X]) ^ (k + 1 + 1) -
        (C (Nat.fib (k + 1 + 1) : ℤ) * X + C (Nat.fib (k + 1) : ℤ)) =
        X * (X ^ (k + 1) - (C (Nat.fib (k + 1) : ℤ) * X + C (Nat.fib k : ℤ))) +
          C (Nat.fib (k + 1) : ℤ) * (X ^ 2 - X - 1) := by
      rw [Nat.fib_add_two]
      push_cast
      simp only [map_add]
      ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_mul_left _ _)

def s0 : ℕ → ℤ
  | 0 => 1
  | n + 1 => s0 n + ((n : ℤ) + 2) ^ 2 * Nat.fib n

def s1 : ℕ → ℤ
  | 0 => 0
  | n + 1 => s1 n + ((n : ℤ) + 2) ^ 2 * Nat.fib (n + 1)

theorem pdvd (n : ℕ) : (X ^ 2 - X - 1 : ℤ[X]) ∣ p n - (C (s0 n) + C (s1 n) * X) := by
  induction n with
  | zero => simp [p, s0, s1]
  | succ n ih =>
    have e : p (n + 1) - (C (s0 (n + 1)) + C (s1 (n + 1)) * X) =
        (p n - (C (s0 n) + C (s1 n) * X)) +
        (X ^ (n + 1) - (C (Nat.fib (n + 1) : ℤ) * X + C (Nat.fib n : ℤ))) *
          C (((n : ℤ) + 2) ^ 2) := by
      simp only [p, s0, s1, map_add, map_mul]
      ring
    rw [e]
    exact dvd_add ih (dvd_mul_of_dvd_left (xpow n) _)

theorem rem (n : ℕ) : p n %ₘ (X ^ 2 - X - 1) = C (s0 n) + C (s1 n) * X := by
  rw [modByMonic_eq_of_dvd_sub hq (pdvd n), (modByMonic_eq_self_iff hq).mpr]
  apply degree_lt_degree
  have h2 : (X ^ 2 - X - 1 : ℤ[X]).natDegree = 2 := by compute_degree!
  have h1 : (C (s0 n) + C (s1 n) * X).natDegree ≤ 1 := by compute_degree
  omega

theorem sum_eq (n : ℕ) :
    s1 n = ∑ i ∈ Finset.Icc 1 (n + 1), (i : ℤ) ^ 2 * (Nat.fib (i - 1) : ℤ) := by
  induction n with
  | zero => simp [s1]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← ih]
    simp only [s1, Nat.add_sub_cancel]
    push_cast
    ring

theorem solve : ∀ n : ℕ,
    a (n + 1) = ∑ i ∈ Finset.Icc 1 (n + 1), (i : ℤ) ^ 2 * (Nat.fib (i - 1) : ℤ) := by
  intro n
  rw [← sum_eq n]
  simp only [a, Nat.add_sub_cancel, rem, coeff_add, coeff_C, coeff_C_mul_X]
  simp

end R192255

theorem OMA.solution : type_of% @OMA.S_oeis_a192255.main := R192255.solve
