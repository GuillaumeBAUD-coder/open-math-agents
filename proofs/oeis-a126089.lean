import OMAStatements.S_oeis_a126089

-- Problem: A126089: Expansion of e.g.f.: (1-2*x)*sqrt(1-4*x).
-- Upstream: formal-conjectures statements/oeis-a126089.lean:0 (declaration OMA.S_oeis_a126089.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Differentiating F^2 = (1-2x)^2 (1-4x), multiplying by F and cancelling 2 (1-2x) gives the
differential equation (1-2x)(1-4x) F' = (-4+12x) F. Its coefficients give a three-term relation
between consecutive coefficients of F, and the first-order recurrence follows from it by
induction. -/

namespace A126089Aux

open PowerSeries OMA.S_oeis_a126089

theorem c_succ (f : ℚ⟦X⟧) (c : ℚ) (m : ℕ) :
    coeff (m + 1) (f * (1 - C c * X)) = coeff (m + 1) f - c * coeff m f := by
  rw [mul_sub, mul_one, map_sub, mul_comm (C c) X, ← mul_assoc, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_succ_mul_X]
  ring

theorem c_zero (f : ℚ⟦X⟧) (c : ℚ) : coeff 0 (f * (1 - C c * X)) = coeff 0 f := by
  rw [mul_sub, mul_one, map_sub, mul_comm (C c) X, ← mul_assoc, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_zero_mul_X]
  ring

theorem ode (F : ℚ⟦X⟧) (hF : F ^ 2 = (1 - 2 * X) ^ 2 * (1 - 4 * X)) :
    derivative ℚ F * (1 - C 2 * X) * (1 - C 4 * X) = F * (1 - C 3 * X) * C (-4) := by
  have h2 : (C 2 : ℚ⟦X⟧) = 2 := map_ofNat C 2
  have h3 : (C 3 : ℚ⟦X⟧) = 3 := map_ofNat C 3
  have h4 : (C 4 : ℚ⟦X⟧) = 4 := map_ofNat C 4
  have hm4 : (C (-4) : ℚ⟦X⟧) = -4 := by rw [map_neg, map_ofNat]
  have hF' : F * F = (1 - C 2 * X) * (1 - C 2 * X) * (1 - C 4 * X) := by
    rw [h2, h4]
    linear_combination hF
  have hd := congrArg (derivative ℚ) hF'
  simp [Derivation.leibniz] at hd
  rw [h2, h4] at hd
  have hmul : (1 - 2 * X) * (2 * (derivative ℚ F * (1 - 2 * X) * (1 - 4 * X) -
      F * (1 - 3 * X) * (-4))) = 0 := by
    linear_combination F * hd - 2 * derivative ℚ F * hF
  have h1 : (1 - 2 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2T := (mul_eq_zero.mp hmul).resolve_left h1
  have hC : C 2 * (derivative ℚ F * (1 - C 2 * X) * (1 - C 4 * X) -
      F * (1 - C 3 * X) * C (-4)) = 0 := by
    rw [h2, h3, h4, hm4]
    exact h2T
  ext n
  have h := congrArg (coeff n) hC
  rw [coeff_C_mul, map_sub, map_zero] at h
  linarith

theorem rel0 (F : ℚ⟦X⟧) (hF : F ^ 2 = (1 - 2 * X) ^ 2 * (1 - 4 * X)) :
    coeff (0 + 1) F = -4 * coeff 0 F := by
  have h := congrArg (coeff 0) (ode F hF)
  simp only [c_zero, PowerSeries.coeff_mul_C, coeff_derivative] at h
  push_cast at h
  linear_combination h

theorem rel1 (F : ℚ⟦X⟧) (hF : F ^ 2 = (1 - 2 * X) ^ 2 * (1 - 4 * X)) :
    2 * coeff (0 + 1 + 1) F - 6 * coeff (0 + 1) F = -4 * coeff (0 + 1) F + 12 * coeff 0 F := by
  have h := congrArg (coeff (0 + 1)) (ode F hF)
  simp only [c_succ, c_zero, PowerSeries.coeff_mul_C, coeff_derivative] at h
  push_cast at h
  linear_combination h

theorem rel (F : ℚ⟦X⟧) (hF : F ^ 2 = (1 - 2 * X) ^ 2 * (1 - 4 * X)) (m : ℕ) :
    ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) F - 6 * ((m : ℚ) + 2) * coeff (m + 1 + 1) F +
      8 * ((m : ℚ) + 1) * coeff (m + 1) F =
      -4 * coeff (m + 1 + 1) F + 12 * coeff (m + 1) F := by
  have h := congrArg (coeff (m + 1 + 1)) (ode F hF)
  simp only [c_succ, PowerSeries.coeff_mul_C, coeff_derivative] at h
  push_cast at h
  linear_combination h

theorem first_order (F : ℚ⟦X⟧) (hF : F ^ 2 = (1 - 2 * X) ^ 2 * (1 - 4 * X)) (n : ℕ) :
    (3 - (n : ℚ)) * ((n : ℚ) + 1) * coeff (n + 1) F +
      2 * (2 * (n : ℚ) - 3) * ((n : ℚ) - 2) * coeff n F = 0 := by
  induction n with
  | zero =>
    have r0 := rel0 F hF
    push_cast
    linear_combination 3 * r0
  | succ n ih =>
    cases n with
    | zero =>
      have r0 := rel0 F hF
      have r1 := rel1 F hF
      push_cast
      linear_combination 2 * r1 + 6 * r0
    | succ m =>
      have r := rel F hF m
      push_cast at ih ⊢
      linear_combination (1 - (m : ℚ)) * r + 2 * ih

end A126089Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a126089.main := by
  intro F hF _ n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have q := A126089Aux.first_order F hF j
  rw [Nat.add_sub_cancel]
  unfold OMA.S_oeis_a126089.a
  rw [Nat.factorial_succ]
  push_cast
  linear_combination (j.factorial : ℚ) * q
