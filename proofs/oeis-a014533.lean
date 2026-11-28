import OMAStatements.S_oeis_a014533
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: coefficient identities from (1+X+X^2)P' = m(1+2X)P and one-factor expansion, combined by linear_combination with multipliers found by computer algebra.

namespace OMA.S_oeis_a014533

open Polynomial in
lemma coeff_mul_tri (Q : Polynomial ℤ) (d : ℕ) :
    ((1 + X + X ^ 2 : Polynomial ℤ) * Q).coeff (d + 2) = Q.coeff (d + 2) + Q.coeff (d + 1) + Q.coeff d := by
  have h1 : (X * Q).coeff (d + 2) = Q.coeff (d + 1) := by
    rw [show d + 2 = (d + 1) + 1 by ring, coeff_X_mul]
  have h2 : (X ^ 2 * Q).coeff (d + 2) = Q.coeff d := by
    rw [mul_comm, coeff_mul_X_pow]
  simp only [add_mul, one_mul, coeff_add, h1, h2]

open Polynomial in
lemma pascal (m d : ℕ) :
    ((1 + X + X ^ 2 : Polynomial ℤ) ^ (m + 1)).coeff (d + 2) =
      ((1 + X + X ^ 2 : Polynomial ℤ) ^ m).coeff (d + 2) +
      ((1 + X + X ^ 2 : Polynomial ℤ) ^ m).coeff (d + 1) +
      ((1 + X + X ^ 2 : Polynomial ℤ) ^ m).coeff d := by
  rw [pow_succ', coeff_mul_tri]

open Polynomial in
lemma ode (m d : ℕ) :
    ((d : ℤ) + 3) * ((1 + X + X ^ 2 : Polynomial ℤ) ^ m).coeff (d + 3) +
      ((d : ℤ) + 2 - m) * ((1 + X + X ^ 2 : Polynomial ℤ) ^ m).coeff (d + 2) +
      ((d : ℤ) + 1 - 2 * m) * ((1 + X + X ^ 2 : Polynomial ℤ) ^ m).coeff (d + 1) = 0 := by
  set P := (1 + X + X ^ 2 : Polynomial ℤ) ^ m with hP
  have hder : derivative (1 + X + X ^ 2 : Polynomial ℤ) = C 1 + C 2 * X := by
    simp
  have key : (1 + X + X ^ 2 : Polynomial ℤ) * derivative P =
      (C (m : ℤ) * (C 1 + C 2 * X)) * P := by
    rw [hP, derivative_pow, hder]
    cases m with
    | zero => simp
    | succ k =>
      rw [pow_succ']
      simp only [Nat.add_sub_cancel]
      push_cast
      ring
  have e := congrArg (fun p => Polynomial.coeff p (d + 2)) key
  rw [coeff_mul_tri] at e
  simp only [coeff_derivative] at e
  have r : ((C (m : ℤ) * (C 1 + C 2 * X)) * P).coeff (d + 2) =
      (m : ℤ) * P.coeff (d + 2) + 2 * (m : ℤ) * P.coeff (d + 1) := by
    rw [show (C (m : ℤ) * (C 1 + C 2 * X)) * P = C (m : ℤ) * P + C (2 * (m : ℤ)) * (X * P) by
      simp only [C_mul, C_1]; ring]
    rw [coeff_add, coeff_C_mul, coeff_C_mul, show d + 2 = (d + 1) + 1 by ring, coeff_X_mul]
  rw [r] at e
  push_cast at e
  linear_combination e

theorem main_proof :
    ∀ n : ℕ, n ≥ 2 →
      -((n : ℤ) + 7) * ((n : ℤ) - 1) * aSeq n +
        ((n : ℤ) + 3) * (2 * (n : ℤ) + 5) * aSeq (n - 1) +
        3 * ((n : ℤ) + 3) * ((n : ℤ) + 2) * aSeq (n - 2) = 0 := by
  intro n hn
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 2 := ⟨n - 2, by omega⟩
  have e1 : t + 2 - 1 = t + 1 := by omega
  have e2 : t + 2 - 2 = t := by omega
  rw [e1, e2]
  unfold aSeq
  set c : ℕ → ℕ → ℤ := fun m k => ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ) ^ m).coeff k with hc
  show -(((t + 2 : ℕ) : ℤ) + 7) * (((t + 2 : ℕ) : ℤ) - 1) * c (t + 5) (t + 9) +
        (((t + 2 : ℕ) : ℤ) + 3) * (2 * ((t + 2 : ℕ) : ℤ) + 5) * c (t + 4) (t + 8) +
        3 * (((t + 2 : ℕ) : ℤ) + 3) * (((t + 2 : ℕ) : ℤ) + 2) * c (t + 3) (t + 7) = 0
  have p1 : c (t + 5) (t + 9) = c (t + 4) (t + 9) + c (t + 4) (t + 8) + c (t + 4) (t + 7) :=
    pascal (t + 4) (t + 7)
  have p2 : c (t + 4) (t + 9) = c (t + 3) (t + 9) + c (t + 3) (t + 8) + c (t + 3) (t + 7) :=
    pascal (t + 3) (t + 7)
  have p3 : c (t + 4) (t + 8) = c (t + 3) (t + 8) + c (t + 3) (t + 7) + c (t + 3) (t + 6) :=
    pascal (t + 3) (t + 6)
  have p4 : c (t + 4) (t + 7) = c (t + 3) (t + 7) + c (t + 3) (t + 6) + c (t + 3) (t + 5) :=
    pascal (t + 3) (t + 5)
  have h2 : (((t + 4 : ℕ) : ℤ) + 3) * c (t + 3) (t + 7) + (((t + 4 : ℕ) : ℤ) + 2 - ((t + 3 : ℕ) : ℤ)) * c (t + 3) (t + 6)
      + (((t + 4 : ℕ) : ℤ) + 1 - 2 * ((t + 3 : ℕ) : ℤ)) * c (t + 3) (t + 5) = 0 := ode (t + 3) (t + 4)
  have h3 : (((t + 5 : ℕ) : ℤ) + 3) * c (t + 3) (t + 8) + (((t + 5 : ℕ) : ℤ) + 2 - ((t + 3 : ℕ) : ℤ)) * c (t + 3) (t + 7)
      + (((t + 5 : ℕ) : ℤ) + 1 - 2 * ((t + 3 : ℕ) : ℤ)) * c (t + 3) (t + 6) = 0 := ode (t + 3) (t + 5)
  have h4 : (((t + 6 : ℕ) : ℤ) + 3) * c (t + 3) (t + 9) + (((t + 6 : ℕ) : ℤ) + 2 - ((t + 3 : ℕ) : ℤ)) * c (t + 3) (t + 8)
      + (((t + 6 : ℕ) : ℤ) + 1 - 2 * ((t + 3 : ℕ) : ℤ)) * c (t + 3) (t + 7) = 0 := ode (t + 3) (t + 6)
  push_cast at h2 h3 h4 ⊢
  rw [p1, p2, p3, p4]
  linear_combination ((t : ℤ) + 9) * h2 + 4 * h3 - ((t : ℤ) + 1) * h4


end OMA.S_oeis_a014533

theorem OMA.solution : type_of% @OMA.S_oeis_a014533.main := OMA.S_oeis_a014533.main_proof
