import OMAStatements.S_oeis_a097192
import Mathlib

namespace OMA.S_oeis_a097192
open PowerSeries
end OMA.S_oeis_a097192

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a097192.main := by
  intro G h0 hG n hn
  have hne : G ≠ 0 := by
    intro h; rw [h] at h0; simp at h0
  have hX : (1 - 27 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg (coeff 0) h
    simp at this
  have hd := congrArg (d⁄dX ℚ) hG
  have h27 : (d⁄dX ℚ) (27 : ℚ⟦X⟧) = 0 := by
    have := (d⁄dX ℚ).map_natCast 27
    simpa using this
  simp only [nsmul_eq_mul, Derivation.leibniz, Derivation.leibniz_pow, map_one, Derivation.map_one_eq_zero, map_sub, map_mul, Derivation.map_natCast, smul_eq_mul, Derivation.map_algebraMap, derivative_X, h27] at hd
  norm_num at hd
  have key : (1 - 27 * X : ℚ⟦X⟧) * d⁄dX ℚ G = 24 * G := by
    have h1 : G ^ 8 * (1 - 27 * X) ^ 7 * (9 * ((1 - 27 * X) * d⁄dX ℚ G - 24 * G)) = 0 := by
      linear_combination hd
    have h2 : G ^ 8 * (1 - 27 * X) ^ 7 ≠ 0 := mul_ne_zero (pow_ne_zero _ hne) (pow_ne_zero _ hX)
    have h3 := (mul_eq_zero.mp h1).resolve_left h2
    have h4 : (9 : ℚ⟦X⟧) ≠ 0 := by
      intro h
      have := congrArg (constantCoeff (R := ℚ)) h
      rw [map_ofNat, map_zero] at this
      norm_num at this
    have := (mul_eq_zero.mp h3).resolve_left h4
    linear_combination this
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e24 : (24 : ℚ⟦X⟧) = C (24 : ℚ) := (map_ofNat C 24).symm
  have e27 : (27 : ℚ⟦X⟧) = C (27 : ℚ) := (map_ofNat C 27).symm
  have key2 : d⁄dX ℚ G = C (24 : ℚ) * G + C (27 : ℚ) * (X * d⁄dX ℚ G) := by
    rw [← e24, ← e27]; linear_combination key
  have hc := congrArg (coeff m) key2
  rw [map_add, coeff_C_mul, coeff_C_mul, coeff_derivative] at hc
  simp only [Nat.add_sub_cancel]
  rcases m with _ | k
  · rw [coeff_zero_X_mul] at hc
    simp [h0] at hc ⊢
    linarith
  · rw [coeff_succ_X_mul, coeff_derivative] at hc
    push_cast at hc ⊢
    linarith
