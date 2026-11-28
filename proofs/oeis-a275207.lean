import OMAStatements.S_oeis_a275207
import Mathlib

namespace OMA.Helpers

open PowerSeries

/-- Coefficient `k + 4` of a product with a polynomial of degree at most four. -/
theorem motzSq_coeff_poly (a0 a1 a2 a3 a4 : ℚ) (F : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 4) ((C a0 + C a1 * X + C a2 * X ^ 2 + C a3 * X ^ 3 + C a4 * X ^ 4) * F) =
      a0 * coeff (k + 4) F + a1 * coeff (k + 3) F + a2 * coeff (k + 2) F +
      a3 * coeff (k + 1) F + a4 * coeff k F := by
  have e : (C a0 + C a1 * X + C a2 * X ^ 2 + C a3 * X ^ 3 + C a4 * X ^ 4) * F =
      C a0 * F + C a1 * (X ^ 1 * F) + C a2 * (X ^ 2 * F) + C a3 * (X ^ 3 * F) +
      C a4 * (X ^ 4 * F) := by ring
  have h1 : coeff (k + 4) (X ^ 1 * F) = coeff (k + 3) F := coeff_X_pow_mul F 1 (k + 3)
  have h2 : coeff (k + 4) (X ^ 2 * F) = coeff (k + 2) F := coeff_X_pow_mul F 2 (k + 2)
  have h3 : coeff (k + 4) (X ^ 3 * F) = coeff (k + 1) F := coeff_X_pow_mul F 3 (k + 1)
  have h4 : coeff (k + 4) (X ^ 4 * F) = coeff k F := coeff_X_pow_mul F 4 k
  rw [e, map_add, map_add, map_add, map_add, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_C_mul,
    coeff_C_mul, h1, h2, h3, h4]

/-- The derivative of a polynomial of degree at most four. -/
theorem motzSq_deriv_poly (a0 a1 a2 a3 a4 : ℚ) :
    derivative ℚ (C a0 + C a1 * X + C a2 * X ^ 2 + C a3 * X ^ 3 + C a4 * X ^ 4) =
      C a1 + C (2 * a2) * X + C (3 * a3) * X ^ 2 + C (4 * a4) * X ^ 3 + C 0 * X ^ 4 := by
  simp [Derivation.leibniz, map_mul, map_ofNat]
  ring

/-- From `F ^ 2 = P`: `2 P F' = P' F`. -/
theorem motzSq_ode (F P : ℚ⟦X⟧) (h : F ^ 2 = P) :
    (C 2 * P) * derivative ℚ F = derivative ℚ P * F := by
  have h1 : derivative ℚ (F ^ 2) = 2 * F * derivative ℚ F := by
    rw [derivative_pow]
    norm_num
  rw [← h, h1, map_ofNat]
  ring

theorem motzSq_rec_T (T : ℚ⟦X⟧) (hT : T ^ 2 = 1 - 2 * X - 3 * X ^ 2) (k : ℕ) :
    ((k : ℚ) + 5) * coeff (k + 5) T =
      (2 * (k : ℚ) + 7) * coeff (k + 4) T + 3 * ((k : ℚ) + 2) * coeff (k + 3) T := by
  have hP : (1 - 2 * X - 3 * X ^ 2 : ℚ⟦X⟧) =
      C 1 + C (-2) * X + C (-3) * X ^ 2 + C 0 * X ^ 3 + C 0 * X ^ 4 := by
    simp only [map_one, map_neg, map_ofNat, map_zero]
    ring
  have h := motzSq_ode T _ (hT.trans hP)
  rw [motzSq_deriv_poly] at h
  have h2 : C 2 * (C 1 + C (-2) * X + C (-3) * X ^ 2 + C 0 * X ^ 3 + C 0 * X ^ 4 : ℚ⟦X⟧) =
      C 2 + C (-4) * X + C (-6) * X ^ 2 + C 0 * X ^ 3 + C 0 * X ^ 4 := by
    simp only [map_one, map_neg, map_ofNat, map_zero]
    ring
  rw [h2] at h
  have e := congrArg (coeff (k + 4)) h
  rw [motzSq_coeff_poly, motzSq_coeff_poly] at e
  simp only [coeff_derivative] at e
  simp only [Nat.add_assoc, Nat.reduceAdd] at e
  push_cast at e
  linear_combination e / 2

theorem motzSq_rec_W (W : ℚ⟦X⟧) (hW : W ^ 2 = 1 - 2 * X ^ 2 - 3 * X ^ 4) (k : ℕ) :
    ((k : ℚ) + 5) * coeff (k + 5) W =
      2 * ((k : ℚ) + 2) * coeff (k + 3) W + 3 * ((k : ℚ) - 1) * coeff (k + 1) W := by
  have hQ : (1 - 2 * X ^ 2 - 3 * X ^ 4 : ℚ⟦X⟧) =
      C 1 + C 0 * X + C (-2) * X ^ 2 + C 0 * X ^ 3 + C (-3) * X ^ 4 := by
    simp only [map_one, map_neg, map_ofNat, map_zero]
    ring
  have h := motzSq_ode W _ (hW.trans hQ)
  rw [motzSq_deriv_poly] at h
  have h2 : C 2 * (C 1 + C 0 * X + C (-2) * X ^ 2 + C 0 * X ^ 3 + C (-3) * X ^ 4 : ℚ⟦X⟧) =
      C 2 + C 0 * X + C (-4) * X ^ 2 + C 0 * X ^ 3 + C (-6) * X ^ 4 := by
    simp only [map_one, map_neg, map_ofNat, map_zero]
    ring
  rw [h2] at h
  have e := congrArg (coeff (k + 4)) h
  rw [motzSq_coeff_poly, motzSq_coeff_poly] at e
  simp only [coeff_derivative] at e
  simp only [Nat.add_assoc, Nat.reduceAdd] at e
  push_cast at e
  linear_combination e / 2

theorem motzSq_g (T W G : ℚ⟦X⟧) (hT : T ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : 8 * X ^ 4 * G = (1 - X - T) ^ 2 + 2 * (1 - X ^ 2 - W)) (k : ℕ) :
    coeff k G = -(coeff (k + 4) T - coeff (k + 3) T + coeff (k + 4) W) / 4 := by
  have hR : (1 - X - T) ^ 2 + 2 * (1 - X ^ 2 - W) =
      (C 4 + C (-4) * X + C (-4) * X ^ 2 + C 0 * X ^ 3 + C 0 * X ^ 4) * 1 +
      (C (-2) + C 2 * X + C 0 * X ^ 2 + C 0 * X ^ 3 + C 0 * X ^ 4) * T +
      (C (-2) + C 0 * X + C 0 * X ^ 2 + C 0 * X ^ 3 + C 0 * X ^ 4) * W := by
    simp only [map_neg, map_ofNat, map_zero]
    linear_combination hT
  have hL : (8 * X ^ 4 * G : ℚ⟦X⟧) = C 8 * (X ^ 4 * G) := by
    rw [map_ofNat]
    ring
  have e := congrArg (coeff (k + 4)) (hG.trans hR)
  rw [hL] at e
  rw [map_add, map_add, motzSq_coeff_poly, motzSq_coeff_poly, motzSq_coeff_poly, coeff_C_mul,
    show coeff (k + 4) (X ^ 4 * G) = coeff k G from coeff_X_pow_mul G 4 k] at e
  simp only [coeff_one] at e
  norm_num at e
  linear_combination e / 8

end OMA.Helpers

open OMA.Helpers PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a275207.main := by
  intro T W G hT hT0 hW hW0 hG hG0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
    show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega,
    show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega,
    show m + 8 - 7 = m + 1 by omega, show m + 8 - 8 = m by omega]
  simp only [motzSq_g T W G hT hG]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  have r2 := motzSq_rec_T T hT m
  have r3 := motzSq_rec_T T hT (m + 1)
  have r4 := motzSq_rec_T T hT (m + 2)
  have r5 := motzSq_rec_T T hT (m + 3)
  have r6 := motzSq_rec_T T hT (m + 4)
  have r7 := motzSq_rec_T T hT (m + 5)
  have r8 := motzSq_rec_T T hT (m + 6)
  have r9 := motzSq_rec_T T hT (m + 7)
  have s3 := motzSq_rec_W W hW (m + 3)
  have s4 := motzSq_rec_W W hW (m + 4)
  have s5 := motzSq_rec_W W hW (m + 5)
  have s6 := motzSq_rec_W W hW (m + 6)
  have s7 := motzSq_rec_W W hW (m + 7)
  simp only [Nat.add_assoc, Nat.reduceAdd] at r2 r3 r4 r5 r6 r7 r8 r9 s3 s4 s5 s6 s7
  push_cast at r2 r3 r4 r5 r6 r7 r8 r9 s3 s4 s5 s6 s7 ⊢
  linear_combination (-1 / 4 : ℚ) * (
      (285*(m:ℚ)^2 + 2733*(m:ℚ) + 5634) * r2 +
      (63*(m:ℚ)^2 + 2583*(m:ℚ) + 13014) * r3 +
      (-419*(m:ℚ)^2 - 7081*(m:ℚ) - 26052) * r4 +
      (303*(m:ℚ)^2 + 5913*(m:ℚ) + 24252) * r5 +
      (-501*(m:ℚ)^2 - 7569*(m:ℚ) - 27462) * r6 +
      (153*(m:ℚ)^2 + 2037*(m:ℚ) + 6630) * r7 +
      (203*(m:ℚ)^2 + 3437*(m:ℚ) + 13800) * r8 +
      (-87*(m:ℚ)^2 - 1557*(m:ℚ) - 6600) * r9 +
      (-285*(m:ℚ)^2 - 2733*(m:ℚ) - 5634) * s3 +
      (-538*(m:ℚ)^2 - 6948*(m:ℚ) - 21152) * s4 +
      (124*(m:ℚ)^2 + 1946*(m:ℚ) + 7470) * s5 +
      (290*(m:ℚ)^2 + 4820*(m:ℚ) + 19200) * s6 +
      (-87*(m:ℚ)^2 - 1557*(m:ℚ) - 6600) * s7)
