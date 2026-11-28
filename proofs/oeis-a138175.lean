import OMAStatements.S_oeis_a138175

-- Problem: A138175: Row sums of the Riordan array (1/(1+x),x(1+2x)/(1+x)^3)^(-1).
-- Upstream: formal-conjectures statements/oeis-a138175.lean:0 (declaration OMA.S_oeis_a138175.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The recurrence as stated fails at n = 3. The series T exists: it is the compositional inverse of
x - x^3 (Mathlib's `PowerSeries.substInv`), and G = (1 - 2T)^(-1). Writing T = x Q gives
Q = 1 + x^2 Q^3 and G = 1 + 2 x Q G, from which the coefficients of 1, x, x^2, x^3 in G are
1, 2, 4, 10; the left side of the recurrence at n = 3 is then -711504. -/

namespace A138175Aux

open PowerSeries

theorem exists_T : ∃ T : ℚ⟦X⟧, T - T ^ 3 = X ∧ constantCoeff T = 0 := by
  have hP0 : constantCoeff (X - X ^ 3 : ℚ⟦X⟧) = 0 := by simp
  have hP1 : coeff 1 (X - X ^ 3 : ℚ⟦X⟧) ≠ 0 := by
    simp [coeff_X, coeff_X_pow]
  have : Invertible (coeff 1 (X - X ^ 3 : ℚ⟦X⟧)) := invertibleOfNonzero hP1
  have hsub : HasSubst (substInv (X - X ^ 3 : ℚ⟦X⟧)) := PowerSeries.HasSubst.substInv _
  have h := subst_substInv_right (X - X ^ 3 : ℚ⟦X⟧) hP0
  rw [← coe_substAlgHom hsub, map_sub, map_pow, substAlgHom_X] at h
  exact ⟨_, h, constantCoeff_substInv _⟩

theorem prod0 (A B : ℚ⟦X⟧) : coeff 0 (A * B) = coeff 0 A * coeff 0 B := by
  simp [coeff_mul]

theorem prod1 (A B : ℚ⟦X⟧) :
    coeff 1 (A * B) = coeff 0 A * coeff 1 B + coeff 1 A * coeff 0 B := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem prod2 (A B : ℚ⟦X⟧) :
    coeff 2 (A * B) = coeff 0 A * coeff 2 B + coeff 1 A * coeff 1 B + coeff 2 A * coeff 0 B := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem step (Q G : ℚ⟦X⟧) (hGR : G = 1 + X * (2 * (Q * G))) (n : ℕ) :
    coeff (n + 1) G = 2 * coeff n (Q * G) := by
  conv_lhs => rw [hGR]
  rw [map_add, coeff_succ_X_mul, coeff_one, if_neg (Nat.succ_ne_zero n), zero_add, two_mul,
    map_add]
  ring

theorem coeffs (T G : ℚ⟦X⟧) (hT : T - T ^ 3 = X) (hT0 : constantCoeff T = 0)
    (hG : G * (1 - 2 * T) = 1) :
    coeff 0 G = 1 ∧ coeff 1 G = 2 ∧ coeff 2 G = 4 ∧ coeff 3 G = 10 := by
  obtain ⟨Q, rfl⟩ := X_dvd_iff.mpr hT0
  have hQX : X * Q = X * (1 + X ^ 2 * Q ^ 3) := by linear_combination hT
  have hQ : Q = 1 + X ^ 2 * Q ^ 3 := mul_left_cancel₀ X_ne_zero hQX
  have q0 : constantCoeff Q = 1 := by
    have h := congrArg constantCoeff hQ
    simpa using h
  have c0Q : coeff 0 Q = 1 := by
    rw [coeff_zero_eq_constantCoeff_apply]
    exact q0
  have q1 : coeff 1 Q = 0 := by
    have h := congrArg (coeff 1) hQ
    simpa [coeff_X_pow_mul', coeff_one] using h
  have q2 : coeff 2 Q = 1 := by
    have h := congrArg (coeff 2) hQ
    simpa [coeff_X_pow_mul', coeff_one, q0] using h
  have hGR : G = 1 + X * (2 * (Q * G)) := by linear_combination hG
  have g0 : coeff 0 G = 1 := by
    have h := congrArg (coeff 0) hGR
    simpa using h
  have g1 : coeff 1 G = 2 := by
    have h := step Q G hGR 0
    rw [prod0 Q G, c0Q, g0] at h
    simpa using h
  have g2 : coeff 2 G = 4 := by
    have h := step Q G hGR 1
    rw [prod1 Q G, c0Q, q1, g0, g1] at h
    norm_num at h
    exact h
  have g3 : coeff 3 G = 10 := by
    have h := step Q G hGR 2
    rw [prod2 Q G, c0Q, q1, q2, g0, g1, g2] at h
    norm_num at h
    exact h
  exact ⟨g0, g1, g2, g3⟩

end A138175Aux

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a138175.main) := by
  intro h
  obtain ⟨T, hT, hT0⟩ := A138175Aux.exists_T
  have hc : PowerSeries.constantCoeff (1 - 2 * T : PowerSeries ℚ) ≠ 0 := by
    simp [hT0]
  have hG : (1 - 2 * T)⁻¹ * (1 - 2 * T) = 1 := PowerSeries.inv_mul_cancel _ hc
  obtain ⟨g0, g1, g2, g3⟩ := A138175Aux.coeffs T _ hT hT0 hG
  have hT0' : PowerSeries.coeff 0 T = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hT0
  have h3 := h T _ hT hT0' hG 3 le_rfl
  norm_num [g0, g1, g2, g3] at h3
