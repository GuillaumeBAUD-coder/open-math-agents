import OMAStatements.S_oeis_a047946
import Mathlib

-- Problem: A047946: a(n) = 5*F(n)^2 + 3*(-1)^n where F(n) are the Fibonacci numbers A000045.
-- Upstream: formal-conjectures statements/oeis-a047946.lean:0 (declaration OMA.S_oeis_a047946.main)
-- Credit: @caa1982 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.A047946Helpers

lemma fibZ_add_two (m : ℕ) :
    ((m + 2).fib : ℤ) = ((m + 1).fib : ℤ) + (m.fib : ℤ) := by
  rw [Nat.fib_add_two]; push_cast; ring

lemma cassini (n : ℕ) :
    ((n + 1).fib : ℤ) ^ 2 - ((n + 1).fib : ℤ) * (n.fib : ℤ) - (n.fib : ℤ) ^ 2
      = (-1 : ℤ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [fibZ_add_two, pow_succ]
    linear_combination (-1 : ℤ) * ih

lemma shift (n m : ℕ) :
    ((m + n + n).fib : ℤ) =
      (2 * ((n + 1).fib : ℤ) - (n.fib : ℤ)) * ((m + n).fib : ℤ)
        - (-1 : ℤ) ^ n * (m.fib : ℤ) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ =>
      have h := Nat.fib_two_mul n
      have h2 : n.fib ≤ 2 * (n + 1).fib := by
        have := Nat.fib_le_fib_succ (n := n); omega
      simp only [Nat.zero_add, Nat.fib_zero, Nat.cast_zero, mul_zero, sub_zero]
      rw [← two_mul, h, Nat.cast_mul, Nat.cast_sub h2]
      push_cast; ring
    | 1, _ =>
      have h := Nat.fib_two_mul_add_one n
      have hc := cassini n
      rw [show 1 + n + n = 2 * n + 1 by ring, h, add_comm 1 n]
      push_cast
      linear_combination (-1 : ℤ) * hc
    | m + 2, ih =>
      have h0 := ih m (by omega)
      have h1 := ih (m + 1) (by omega)
      rw [show m + 2 + n + n = (m + n + n) + 2 by ring,
        show m + 2 + n = (m + n) + 2 by ring, fibZ_add_two, fibZ_add_two, fibZ_add_two,
        show m + n + n + 1 = m + 1 + n + n by ring, show m + n + 1 = m + 1 + n by ring,
        h0, h1]
      ring

end OMA.A047946Helpers

open OMA.A047946Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a047946.main := by
  intro n _ k
  unfold OMA.S_oeis_a047946.fibSquare OMA.S_oeis_a047946.coefficient
  set m := n * k with hm
  have e1 : n * (k + 1) = m + n := by rw [hm]; ring
  have e2 : n * (k + 2) = m + n + n := by rw [hm]; ring
  have e3 : n * (k + 3) = (m + n) + n + n := by rw [hm]; ring
  rw [e1, e2, e3, shift n (m + n), shift n m]
  have hL : (2 * ((n + 1).fib : ℤ) - (n.fib : ℤ)) ^ 2 = 5 * (n.fib : ℤ) ^ 2 + 4 * (-1 : ℤ) ^ n := by
    linear_combination 4 * cassini n
  set L := 2 * ((n + 1).fib : ℤ) - (n.fib : ℤ)
  set a := (m.fib : ℤ)
  set b := ((m + n).fib : ℤ)
  set F := (n.fib : ℤ)
  split_ifs with hn
  · have hq : (-1 : ℤ) ^ n = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr hn)
    rw [hq] at hL ⊢
    linear_combination ((L * b + a) ^ 2 + b ^ 2) * hL
  · have hq : (-1 : ℤ) ^ n = 1 := Even.neg_one_pow (Nat.even_iff.mpr (by omega))
    rw [hq] at hL ⊢
    linear_combination ((L * b - a) ^ 2 - b ^ 2) * hL
