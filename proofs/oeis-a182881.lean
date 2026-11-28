import OMAStatements.S_oeis_a182881
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a182881.main := by
  intro S G hS h0 hG n hn
  have hD2 : (PowerSeries.derivative ℚ) (2 : ℚ⟦X⟧) = 0 := by
    simpa using (PowerSeries.derivative ℚ).map_natCast 2
  have hD1 : (PowerSeries.derivative ℚ) (2 * X ^ 3 : ℚ⟦X⟧) = 6 * X ^ 2 := by
    simp [Derivation.leibniz, Derivation.leibniz_pow, hD2]; ring
  have h3 : S ^ 3 * G = 2 * X ^ 3 := by
    have : (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 : ℚ⟦X⟧) * S * G = 2 * X ^ 3 := by
      linear_combination hG
    rw [← this, ← hS]; ring
  have hDP : (PowerSeries.derivative ℚ) (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 : ℚ⟦X⟧)
      = -2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3 := by
    simp [Derivation.leibniz, Derivation.leibniz_pow, hD2]; ring
  have hDS : 2 * S * (PowerSeries.derivative ℚ) S
      = -2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3 := by
    rw [← hDP, ← hS]; simp [Derivation.leibniz_pow]; ring
  have hd3 : S ^ 3 * (PowerSeries.derivative ℚ) G
      + 3 * S ^ 2 * (PowerSeries.derivative ℚ) S * G = 6 * X ^ 2 := by
    have := congrArg (PowerSeries.derivative ℚ) h3
    rw [hD1] at this
    simp [Derivation.leibniz, Derivation.leibniz_pow] at this
    linear_combination this
  have hS0 : S ≠ 0 := by
    intro h; rw [h] at h0; simp at h0
  have hE0 : S * (X * S ^ 2 * (PowerSeries.derivative ℚ) G
      - G * (3 * S ^ 2 - 3 * X * S * (PowerSeries.derivative ℚ) S)) = 0 := by
    linear_combination X * hd3 - 3 * h3
  have hE1 := (mul_eq_zero.mp hE0).resolve_left hS0
  have hE2 : 2 * X * S ^ 2 * (PowerSeries.derivative ℚ) G
      = G * (6 * S ^ 2 - 3 * X * (2 * S * (PowerSeries.derivative ℚ) S)) := by
    linear_combination 2 * hE1
  rw [hDS, hS] at hE2
  have hN : ∀ (c : ℕ) (f : ℚ⟦X⟧) (k : ℕ), (PowerSeries.coeff k) ((c : ℚ⟦X⟧) * f) = c * (PowerSeries.coeff k) f := by
    intro c f k
    rw [← map_natCast (PowerSeries.C (R := ℚ)) c, PowerSeries.coeff_C_mul]
  have hN2 := fun f k => hN 2 f k
  have hN4 := fun f k => hN 4 f k
  have hN6 := fun f k => hN 6 f k
  simp only [Nat.cast_ofNat] at hN2 hN4 hN6
  have hE3 : 2 * (X ^ 1 * (PowerSeries.derivative ℚ) G) - 4 * (X ^ 2 * (PowerSeries.derivative ℚ) G)
      - 2 * (X ^ 3 * (PowerSeries.derivative ℚ) G) - 4 * (X ^ 4 * (PowerSeries.derivative ℚ) G)
      + 2 * (X ^ 5 * (PowerSeries.derivative ℚ) G)
      = 6 * G - 6 * (X ^ 1 * G) + 6 * (X ^ 3 * G) - 6 * (X ^ 4 * G) := by
    linear_combination hE2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have hc := congrArg (PowerSeries.coeff (m + 4)) hE3
  simp only [map_sub, map_add, hN2, hN4, hN6, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_derivative] at hc
  have e1 : m + 4 - 1 = m + 3 := by omega
  have e2 : m + 4 - 2 = m + 2 := by omega
  have e3 : m + 4 - 3 = m + 1 := by omega
  have e4 : m + 4 - 4 = m := by omega
  simp only [e1, e2, e3, e4, if_pos (show 1 ≤ m + 4 by omega), if_pos (show 2 ≤ m + 4 by omega),
    if_pos (show 3 ≤ m + 4 by omega), if_pos (show 4 ≤ m + 4 by omega)] at hc ⊢
  by_cases h5 : 5 ≤ m + 4
  · have hm1 : 1 ≤ m := by omega
    have e6 : m + 4 - 5 + 1 = m := by omega
    have e7 : ((m + 4 - 5 : ℕ) : ℚ) + 1 = m := by
      have : m + 4 - 5 + 1 = m := e6
      exact_mod_cast this
    rw [if_pos h5, e6, e7] at hc
    push_cast at hc ⊢
    linear_combination (-1 / 2 : ℚ) * hc
  · rw [if_neg h5] at hc
    have hm0 : m = 0 := by omega
    subst hm0
    push_cast at hc ⊢
    simp at hc ⊢
    linear_combination (-1 / 2 : ℚ) * hc
