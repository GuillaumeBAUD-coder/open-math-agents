import OMAStatements.S_oeis_a131607
import Mathlib

open OMA.S_oeis_a131607 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a131607.main := by
  have f (j : ℕ) : P (j+2) = 2*P (j+1) + P j := rfl
  have o (j : ℕ) : P j % 2 = 1 ∧ P (j+1) % 2 = 1 := by
    induction j with
    | zero => decide
    | succ j ih =>
      have : P (j+1+1) = 2*P (j+1) + P j := rfl
      omega
  have s (N : ℕ) : a (N+6) + a N + 1 = 7*P (N+1) + 3*P N := by
    have : P (N+6) = 70*P (N+1) + 29*P N := by
      simp only [f]
      ring
    have := (o N).1
    unfold a
    omega
  have h (n : ℕ) : (a (n+9) : ℤ) = 3*a (n+8) - a (n+7) - a (n+6) - a (n+3) + 3*a (n+2) -
      a (n+1) - a n := by
    have s0 := s n
    have s1 := s (n+1)
    have s2 := s (n+2)
    have s3 := s (n+3)
    have f0 := f n
    have f1 := f (n+1)
    have f2 := f (n+2)
    simp only [add_assoc, Nat.reduceAdd] at s0 s1 s2 s3 f0 f1 f2
    omega
  constructor
  · rw [show ((1 - X) * (1 + X ^ 2) * (1 - 2 * X - X ^ 2) * (1 - X ^ 2 + X ^ 4) : ℤ⟦X⟧) =
      1 - 3*X + X^2 + X^3 + X^6 - 3*X^7 + X^8 + X^9 by ring]
    ext (_ | _ | _ | _ | _ | _ | _ | _ | _ | n) <;>
    simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_mul_C,
      ← map_ofNat (C : ℤ →+* _), -eq_intCast] <;>
    first | linarith [h n] | simp [a, P]
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact h (k+4)
