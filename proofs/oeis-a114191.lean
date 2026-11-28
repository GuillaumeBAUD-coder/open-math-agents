import OMAStatements.S_oeis_a114191
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a114191.main := by
  intro S c G hS h0 hc hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have K : G * (3 + S) = 4 := by linear_combination 4*hG + G*hc
  have s : S = 3 - 2*((1-X)*G) :=
    mul_left_cancel₀ (fun q => by
      have := congrArg (coeff 0) q
      rw [map_add, h0, ← map_ofNat (C (R := ℚ)) 3] at this
      norm_num at this : 3 + S ≠ 0)
      (by linear_combination hS + 2*(1-X)*K)
  have h := congrArg (derivative ℚ) hS
  simp only [← map_ofNat (C (R := ℚ))] at h s
  simp [Derivation.leibniz, pow_succ] at h
  simp only [map_ofNat] at h
  have o : (2 + 16*X) * derivative ℚ S - 8*S = 0 :=
    (mul_eq_zero.1 (by linear_combination (1+8*X)*h - 8*hS : S * _ = 0)).resolve_left
      (by rintro rfl; simp at h0)
  simp only [← map_ofNat (C (R := ℚ))] at o
  have g (k : ℕ) : coeff (k+1) S = 2 * (coeff k G - coeff (k+1) G) := by
    have := congrArg (coeff (k+1)) s
    simp [sub_mul] at this
    linarith
  have c := congrArg (coeff (m+1)) o
  simp [add_mul, mul_assoc, coeff_derivative, g] at c ⊢
  linear_combination (-1/4 : ℚ) * c
