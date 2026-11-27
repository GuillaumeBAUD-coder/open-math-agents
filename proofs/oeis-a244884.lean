import OMAStatements.S_oeis_a244884

-- Problem: A244884: Expansion of (-2 +x^2 +x -x*sqrt(1-2*x-3*x^2))/(-1 +x -sqrt(1-2*x-3*x^2)).
-- Upstream: formal-conjectures statements/oeis-a244884.lean:0 (declaration OMA.S_oeis_a244884.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Multiplying the defining relation by -1 + x + S gives
(1-x) S = 2x^3 + x^2 - 2x + 1 - 2x^2 G. The series H = (1-x) S satisfies
H^2 = (1-x)^2 (1-3x)(1+x); differentiating, multiplying by H and cancelling 2 (1-x) gives
(1-x)(1+x)(1-3x) H' = (6x^2 - 2) H. The coefficient of x^(n+1) in this equation, written through
the coefficients of G, is the recurrence. -/

namespace A244884Aux

open PowerSeries

theorem c_succ (f : ℚ⟦X⟧) (c : ℚ) (m : ℕ) :
    coeff (m + 1) (f * (1 - C c * X)) = coeff (m + 1) f - c * coeff m f := by
  rw [mul_sub, mul_one, map_sub, mul_comm (C c) X, ← mul_assoc, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_succ_mul_X]
  ring

theorem odeH (H : ℚ⟦X⟧) (hH : H * H = (1 - X) * (1 - X) * ((1 - 3 * X) * (1 + X))) :
    derivative ℚ H * (1 - C 1 * X) * (1 - C (-1) * X) * (1 - C 3 * X) =
      H * X * X * C 6 - H * C 2 := by
  have h1c : (C 1 : ℚ⟦X⟧) = 1 := map_one C
  have hm1 : (C (-1) : ℚ⟦X⟧) = -1 := by rw [map_neg, map_one]
  have h2 : (C 2 : ℚ⟦X⟧) = 2 := map_ofNat C 2
  have h3 : (C 3 : ℚ⟦X⟧) = 3 := map_ofNat C 3
  have h6 : (C 6 : ℚ⟦X⟧) = 6 := map_ofNat C 6
  have hH' : H * H = (1 - X) * (1 - X) * ((1 - C 3 * X) * (1 + X)) := by
    rw [h3]
    exact hH
  have hd := congrArg (derivative ℚ) hH'
  simp [Derivation.leibniz] at hd
  rw [h3] at hd
  have hmul : (1 - X) * (2 * (derivative ℚ H * (1 - X) * (1 + X) * (1 - 3 * X) -
      (H * X * X * 6 - H * 2))) = 0 := by
    linear_combination H * hd - 2 * derivative ℚ H * hH
  have h1 : (1 - X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2T := (mul_eq_zero.mp hmul).resolve_left h1
  have hC : C 2 * (derivative ℚ H * (1 - C 1 * X) * (1 - C (-1) * X) * (1 - C 3 * X) -
      (H * X * X * C 6 - H * C 2)) = 0 := by
    rw [h1c, hm1, h2, h3, h6]
    linear_combination h2T
  ext n
  have h := congrArg (coeff n) hC
  rw [coeff_C_mul, map_sub, map_zero] at h
  linarith

theorem hcoef (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (-1 + X - S) = -2 + X ^ 2 + X - X * S) (i : ℕ) :
    coeff (i + 1 + 1 + 1 + 1) ((1 - X) * S) = -2 * coeff (i + 1 + 1) G := by
  have h1c : (C 1 : ℚ⟦X⟧) = 1 := map_one C
  have hm2 : (C (-2) : ℚ⟦X⟧) = -2 := by rw [map_neg, map_ofNat]
  have h2 : (C 2 : ℚ⟦X⟧) = 2 := map_ofNat C 2
  have hC : C 2 * ((1 - X) * S -
      (((C 2 * X + C 1) * X + C (-2)) * X + C 1 + G * X * X * C (-2))) = 0 := by
    rw [h1c, hm2, h2]
    linear_combination (X - 1 + S) * hG + (G - X) * hS
  have h := congrArg (coeff (i + 1 + 1 + 1 + 1)) hC
  rw [coeff_C_mul, map_zero] at h
  simp only [map_sub, map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C,
    PowerSeries.coeff_mul_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  linear_combination (1 / 2 : ℚ) * h

theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (-1 + X - S) = -2 + X ^ 2 + X - X * S) (m : ℕ) :
    ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1) G -
      (3 * (m : ℚ) + 16) * coeff (m + 1 + 1 + 1 + 1) G -
      ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1) G + 3 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G = 0 := by
  have hH : (1 - X) * S * ((1 - X) * S) = (1 - X) * (1 - X) * ((1 - 3 * X) * (1 + X)) := by
    linear_combination (1 - X) ^ 2 * hS
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (odeH _ hH)
  simp only [c_succ, map_sub, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
    coeff_derivative] at h
  rw [hcoef S G hS hG (m + 1 + 1 + 1), hcoef S G hS hG (m + 1 + 1), hcoef S G hS hG (m + 1),
    hcoef S G hS hG m] at h
  push_cast at h
  linear_combination (-1 / 2 : ℚ) * h

end A244884Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a244884.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  rw [e1, e2, e3]
  have r := A244884Aux.rel S G hS hG m
  push_cast
  linear_combination r
