import OMAStatements.S_oeis_a370261
import Mathlib

namespace A370261Aux

open Polynomial

/-- Pell-type identity for Chebyshev polynomials. -/
lemma pell (n : ℕ) :
    Chebyshev.T ℤ ((n : ℤ) + 1) ^ 2 - (X ^ 2 - 1) * Chebyshev.U ℤ (n : ℤ) ^ 2 = 1 := by
  induction n with
  | zero => simp [Chebyshev.T_one, Chebyshev.U_zero]
  | succ n ih =>
    have h1 := Chebyshev.T_eq_X_mul_T_sub_pol_U ℤ (n : ℤ)
    have h2 := Chebyshev.U_eq_X_mul_U_add_T ℤ (n : ℤ)
    have e1 : (((n + 1 : ℕ) : ℤ) + 1) = (n : ℤ) + 2 := by push_cast; ring
    have e2 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [e1, e2]
    linear_combination
      (Chebyshev.T ℤ ((n : ℤ) + 2) + (X * Chebyshev.T ℤ ((n : ℤ) + 1)
        + (X ^ 2 - 1) * Chebyshev.U ℤ (n : ℤ))) * h1
      - (X ^ 2 - 1) * (Chebyshev.U ℤ ((n : ℤ) + 1) + (X * Chebyshev.U ℤ (n : ℤ)
        + Chebyshev.T ℤ ((n : ℤ) + 1))) * h2 + ih

lemma key (j : ℕ) : ∃ w : ℤ,
    (Chebyshev.T ℤ ((2 * (j + 1) : ℕ) : ℤ)).eval (((2 * (j + 1) : ℕ) : ℤ) + 1)
      = 1 + 8 * ((j : ℤ) + 1) ^ 3 * ((j : ℤ) + 2) * w ^ 2 := by
  have hx : (((2 * (j + 1) : ℕ) : ℤ) + 1) = 2 * ((j : ℤ) + 1) + 1 := by push_cast; ring
  have hidx : ((2 * (j + 1) : ℕ) : ℤ) = ((j : ℤ) + 1) + ((j : ℤ) + 1) := by push_cast; ring
  rw [hx, hidx]
  set x : ℤ := 2 * ((j : ℤ) + 1) + 1 with hxdef
  have hp := congrArg (Polynomial.eval x) (pell j)
  simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_one] at hp
  have hd := congrArg (Polynomial.eval x) (Chebyshev.T_mul_T ℤ ((j : ℤ) + 1) ((j : ℤ) + 1))
  rw [sub_self, Chebyshev.T_zero] at hd
  simp only [eval_add, eval_mul, eval_one] at hd
  have h2 : (Polynomial.eval x (2 : ℤ[X])) = 2 := by
    have : (2 : ℤ[X]) = Polynomial.C 2 := rfl
    rw [this, eval_C]
  rw [h2] at hd
  have hdv := Polynomial.sub_dvd_eval_sub x 1 (Chebyshev.U ℤ (j : ℤ))
  rw [Chebyshev.U_eval_one] at hdv
  obtain ⟨c, hc⟩ := hdv
  have hu : (Chebyshev.U ℤ (j : ℤ)).eval x = ((j : ℤ) + 1) * (1 + 2 * c) := by
    have : ((((j : ℤ) : ℤ) : ℤ) + 1) = (j : ℤ) + 1 := rfl
    simp only [Int.cast_id] at hc
    rw [hxdef] at hc
    linear_combination hc
  refine ⟨1 + 2 * c, ?_⟩
  rw [hu] at hp
  have hx2 : x ^ 2 - 1 = 4 * ((j : ℤ) + 1) * ((j : ℤ) + 2) := by rw [hxdef]; ring
  linear_combination -hd + 2 * hp + 2 * ((j : ℤ) + 1) ^ 2 * (1 + 2 * c) ^ 2 * hx2

end A370261Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a370261.main := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  obtain ⟨w, hw⟩ := A370261Aux.key j
  refine ⟨w.natAbs, ?_⟩
  have hA : OMA.S_oeis_a370261.A370259 (2 * (j + 1)) = ((j : ℚ) + 2) * (w : ℚ) ^ 2 := by
    unfold OMA.S_oeis_a370261.A370259
    rw [hw]
    push_cast
    have h1 : ((j : ℚ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  unfold OMA.S_oeis_a370261.a
  rw [hA]
  push_cast
  have h2 : ((j : ℝ) + 1 + 1) ≠ 0 := by positivity
  have h3 : ((j : ℝ) + 2) * (w : ℝ) ^ 2 / ((j : ℝ) + 1 + 1) = (w : ℝ) ^ 2 := by
    field_simp
    ring
  rw [h3, Real.sqrt_sq_eq_abs]
  simp [Nat.cast_natAbs]
