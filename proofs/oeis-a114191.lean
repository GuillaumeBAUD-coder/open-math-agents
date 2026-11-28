import OMAStatements.S_oeis_a114191

-- Problem: A114191: Mathar's recurrence (oeis-a114191)
-- Credit: @sntntHb
-- Method: G*(S+3) = 4 gives a first-order linear ODE for G; its coefficients give the recurrence.

namespace OMA114191

open PowerSeries

theorem dmul (f g : ℚ⟦X⟧) : derivative ℚ (f * g) = f * derivative ℚ g + g * derivative ℚ f := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

theorem dofNat (k : ℕ) [k.AtLeastTwo] : derivative ℚ (OfNat.ofNat k : ℚ⟦X⟧) = 0 := by
  rw [← map_ofNat (C (R := ℚ)) k, derivative_C]

theorem done : derivative ℚ (1 : ℚ⟦X⟧) = 0 := derivative_one

theorem c0ofNat (k : ℕ) [k.AtLeastTwo] : coeff 0 (OfNat.ofNat k : ℚ⟦X⟧) = OfNat.ofNat k := by
  rw [← map_ofNat (C (R := ℚ)) k, coeff_zero_C]

theorem ne_zero_of_coeff {f : ℚ⟦X⟧} (h : coeff 0 f ≠ 0) : f ≠ 0 := by
  rintro rfl; simp at h

theorem coeff_X_mul_D (f : ℚ⟦X⟧) (n : ℕ) :
    coeff n (X * derivative ℚ f) = (n : ℚ) * coeff n f := by
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring


end OMA114191

open PowerSeries OMA114191

theorem OMA.solution : type_of% @OMA.S_oeis_a114191.main := by
  intro S c G h1 h0 hc hG n hn
  have hA : S * derivative ℚ S = 4 := by
    have := congrArg (derivative ℚ) h1
    rw [pow_two, dmul, map_add, done, dmul, dofNat 8, derivative_X] at this
    have h2 : (2 : ℚ⟦X⟧) * (S * derivative ℚ S - 4) = 0 := by linear_combination this
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (ne_zero_of_coeff (by rw [c0ofNat]; norm_num))
    · linear_combination h
  have hB : G * (S + 3) = 4 := by linear_combination 4 * hG + G * hc
  have hD : derivative ℚ G * (S + 3) + G * derivative ℚ S = 0 := by
    have := congrArg (derivative ℚ) hB
    rw [dmul, map_add, dofNat 3, dofNat 4] at this
    linear_combination this
  have hS3 : S + 3 ≠ 0 := ne_zero_of_coeff (by rw [map_add, c0ofNat, h0]; norm_num)
  have hS : S ≠ 0 := ne_zero_of_coeff (by rw [h0]; norm_num)
  have hG2 : 2 * (1 - X) * G + S - 3 = 0 := by
    have : (S + 3) * (2 * (1 - X) * G + S - 3) = 0 := by
      linear_combination 2 * (1 - X) * hB + h1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hS3
    · exact h
  have hE : (1 + 7 * X - 8 * X ^ 2) * X * derivative ℚ G - (5 * X + 4 * X ^ 2) * G + 6 * X = 0 := by
    have : ((S + 3) * S) * ((1 + 7 * X - 8 * X ^ 2) * X * derivative ℚ G
        - (5 * X + 4 * X ^ 2) * G + 6 * X) = 0 := by
      linear_combination (1 + 7 * X - 8 * X ^ 2) * X * S * hD
        - (1 + 7 * X - 8 * X ^ 2) * X * G * hA - (5 * X + 4 * X ^ 2) * S * hB + 6 * X * h1
        - 2 * X * (1 + 8 * X) * hG2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (mul_ne_zero hS3 hS)
    · exact h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have c4 : (C (4 : ℚ) : ℚ⟦X⟧) = 4 := map_ofNat C 4
  have c5 : (C (5 : ℚ) : ℚ⟦X⟧) = 5 := map_ofNat C 5
  have c6 : (C (6 : ℚ) : ℚ⟦X⟧) = 6 := map_ofNat C 6
  have c7 : (C (7 : ℚ) : ℚ⟦X⟧) = 7 := map_ofNat C 7
  have c8 : (C (8 : ℚ) : ℚ⟦X⟧) = 8 := map_ofNat C 8
  have hE' : X * derivative ℚ G + C 7 * (X * (X * derivative ℚ G))
      - C 8 * (X * (X * (X * derivative ℚ G))) - C 5 * (X * G) - C 4 * (X * (X * G))
      + C 6 * X = 0 := by
    rw [c4, c5, c6, c7, c8]; linear_combination hE
  have key := congrArg (coeff (m + 2)) hE'
  have hT : ∀ k, coeff k (X * derivative ℚ G) = (k : ℚ) * coeff k G := coeff_X_mul_D G
  generalize X * derivative ℚ G = t at hT key
  simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, hT, coeff_X, map_zero] at key
  rw [if_neg (by omega)] at key
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  push_cast at key ⊢
  linear_combination key
