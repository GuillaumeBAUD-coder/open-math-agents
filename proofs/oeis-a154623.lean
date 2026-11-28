import OMAStatements.S_oeis_a154623
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a154623.main := by
  intro T G hT h0 hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have h := congrArg (derivative ℚ) hT
  simp only [← map_ofNat (C (R := ℚ))] at h hG
  simp [Derivation.leibniz, pow_succ] at h
  simp only [map_ofNat] at h
  have o : (2 - 28*X + 90*X^2) * derivative ℚ T + 4*T = 0 :=
    (mul_eq_zero.1 (by linear_combination (1-9*X)*h + 9*hT : T * _ = 0)).resolve_left
      (by rintro rfl; simp at h0)
  simp only [← map_ofNat (C (R := ℚ))] at o
  have g (k : ℕ) : coeff (k+1) T = -2 * coeff (k+1) G := by
    have := congrArg (coeff (k+1)) hG
    simp at this
    linarith
  have c := congrArg (coeff (m+1)) o
  rcases m with _ | m <;>
  simp [sub_mul, add_mul, mul_assoc, pow_succ, coeff_derivative, g] at c ⊢ <;>
  linear_combination (-1/4 : ℚ) * c
