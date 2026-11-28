import OMAStatements.S_oeis_a372018

-- Problem: A372018: G.f. A(x) satisfies A(x) = ( 1 + 4*x*A(x)/(1 - x*A(x)) )^(1/2).
-- Upstream: formal-conjectures statements/oeis-a372018.lean:0 (declaration OMA.S_oeis_a372018.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Put U = x*A. Then U^3 - U^2 + 3*x^2*U + x^2 = 0, a cubic whose coefficients are even in x, so
V = U(-x) is a second root, different from U. By Vieta the third root is 1 - U - V. On the other hand
1 - 4*T(x^2) is a root with constant term 1, and there is only one such root. Hence U + V = 4*T(x^2),
and the coefficient of x^(2n+2) gives the claim. -/

theorem OMA.solution : type_of% @OMA.S_oeis_a372018.main := by
  intro A T hA0 hA hT0 hT n
  have hU : (PowerSeries.X * A) ^ 3 - (PowerSeries.X * A) ^ 2 + 3 * PowerSeries.X ^ 2 * (PowerSeries.X * A) +
      PowerSeries.X ^ 2 = 0 := by
    linear_combination (-(PowerSeries.X ^ 2)) * hA
  obtain ⟨V, hVd⟩ : ∃ V : PowerSeries ℚ, V = PowerSeries.rescale (-1 : ℚ) (PowerSeries.X * A) := ⟨_, rfl⟩
  have hV : V ^ 3 - V ^ 2 + 3 * PowerSeries.X ^ 2 * V + PowerSeries.X ^ 2 = 0 := by
    have h := congrArg (PowerSeries.rescale (-1 : ℚ)) hU
    simp only [map_add, map_sub, map_mul, map_pow, map_zero, map_ofNat, PowerSeries.rescale_neg_one_X] at h
    rw [hVd]
    simp only [map_mul, PowerSeries.rescale_neg_one_X]
    linear_combination h
  obtain ⟨W, hWd⟩ : ∃ W : PowerSeries ℚ, W = PowerSeries.expand 2 two_ne_zero T := ⟨_, rfl⟩
  have hW : W * (1 - 4 * W) ^ 2 = PowerSeries.X ^ 2 * (1 - 3 * W) := by
    have h := congrArg (PowerSeries.expand 2 two_ne_zero) hT
    simp only [map_mul, map_sub, map_pow, map_one, map_ofNat, PowerSeries.expand_X] at h
    rw [hWd]
    linear_combination h
  have hV0 : PowerSeries.constantCoeff V = 0 := by
    rw [hVd, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale]
    simp
  have hW0 : PowerSeries.constantCoeff W = 0 := by
    rw [hWd, PowerSeries.constantCoeff_expand, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hT0
  have h2ne : (2 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    rw [map_ofNat, map_zero] at h'
    norm_num at h'
  have hUV : PowerSeries.X * A - V ≠ 0 := by
    intro h
    have h1 := congrArg (PowerSeries.coeff 1) h
    have h2 : PowerSeries.coeff 1 (PowerSeries.X * A) = 1 := (PowerSeries.coeff_succ_X_mul 0 A).trans hA0
    rw [hVd, map_sub, PowerSeries.coeff_rescale, h2, map_zero] at h1
    norm_num at h1
  have key : (2 * (PowerSeries.X * A - V)) *
      ((1 - PowerSeries.X * A - V) ^ 3 - (1 - PowerSeries.X * A - V) ^ 2 +
        3 * PowerSeries.X ^ 2 * (1 - PowerSeries.X * A - V) + PowerSeries.X ^ 2) = 0 := by
    linear_combination ((PowerSeries.X * A - V) + (2 - 3 * (PowerSeries.X * A + V))) * hU +
      ((PowerSeries.X * A - V) - (2 - 3 * (PowerSeries.X * A + V))) * hV
  have h3 : (1 - PowerSeries.X * A - V) ^ 3 - (1 - PowerSeries.X * A - V) ^ 2 +
      3 * PowerSeries.X ^ 2 * (1 - PowerSeries.X * A - V) + PowerSeries.X ^ 2 = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' h2ne
      · exact absurd h' hUV
    · exact h
  have h4 : (1 - 4 * W) ^ 3 - (1 - 4 * W) ^ 2 + 3 * PowerSeries.X ^ 2 * (1 - 4 * W) + PowerSeries.X ^ 2 = 0 := by
    linear_combination (-4 : PowerSeries ℚ) * hW
  have h5 : ((1 - PowerSeries.X * A - V) - (1 - 4 * W)) *
      ((1 - PowerSeries.X * A - V) ^ 2 + (1 - PowerSeries.X * A - V) * (1 - 4 * W) + (1 - 4 * W) ^ 2 -
        ((1 - PowerSeries.X * A - V) + (1 - 4 * W)) + 3 * PowerSeries.X ^ 2) = 0 := by
    linear_combination h3 - h4
  have hne : (1 - PowerSeries.X * A - V) ^ 2 + (1 - PowerSeries.X * A - V) * (1 - 4 * W) + (1 - 4 * W) ^ 2 -
      ((1 - PowerSeries.X * A - V) + (1 - 4 * W)) + 3 * PowerSeries.X ^ 2 ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [hV0, hW0] at h' <;> norm_num at h'
  have h6 : (1 - PowerSeries.X * A - V) = (1 - 4 * W) := by
    rcases mul_eq_zero.mp h5 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hne
  have h7 : PowerSeries.X * A + V = W + W + W + W := by
    linear_combination (-1 : PowerSeries ℚ) * h6
  have h8 := congrArg (PowerSeries.coeff (2 * n + 1 + 1)) h7
  rw [hVd, hWd] at h8
  have e : PowerSeries.coeff (2 * n + 1 + 1) (PowerSeries.expand 2 two_ne_zero T) = PowerSeries.coeff (n + 1) T := by
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, PowerSeries.coeff_expand_mul]
  have hpow : (-1 : ℚ) ^ (2 * n + 1 + 1) = 1 := Even.neg_one_pow ⟨n + 1, by ring⟩
  have e2 : PowerSeries.coeff (2 * n + 1 + 1) (PowerSeries.rescale (-1 : ℚ) (PowerSeries.X * A)) =
      PowerSeries.coeff (2 * n + 1) A := by
    rw [PowerSeries.coeff_rescale, PowerSeries.coeff_succ_X_mul, hpow, one_mul]
  simp only [map_add, PowerSeries.coeff_succ_X_mul, e, e2] at h8
  linear_combination (1 / 2 : ℚ) * h8
