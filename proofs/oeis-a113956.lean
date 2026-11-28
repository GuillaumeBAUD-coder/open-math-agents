import OMAStatements.S_oeis_a113956

-- Problem: A113956: Expansion of (1/((1-4x)c(x)))/(1-x^2c(x)/sqrt(1-4x)), c(x) the g.f. of A000108.
-- Upstream: formal-conjectures statements/oeis-a113956.lean:0 (declaration OMA.S_oeis_a113956.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation for G with polynomial coefficients. The recurrence is the
coefficient of a power of x in this equation, beyond the degree of its right side. -/

namespace A113956Aux

open PowerSeries

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-2 + 14 * X - 20 * X ^ 2 - 16 * X ^ 3 + (2 - 6 * X - 8 * X ^ 2) * S) = 0 + (4 * X) * S) :
    (256 - 2560 * X + 6912 * X ^ 2 + 1280 * X ^ 3 - 14592 * X ^ 4 - 10752 * X ^ 5 - 2048 * X ^ 6) * derivative ℚ G + (-512 + 2048 * X + 3328 * X ^ 2 - 10240 * X ^ 3 - 11264 * X ^ 4 - 3072 * X ^ 5) * G = 256 - 1024 * X - 512 * X ^ 2 - 512 * X ^ 3 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d56 : derivative ℚ (56 : ℚ⟦X⟧) = 0 := dnum 56
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have d80 : derivative ℚ (80 : ℚ⟦X⟧) = 0 := dnum 80
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d176 : derivative ℚ (176 : ℚ⟦X⟧) = 0 := dnum 176
  have d256 : derivative ℚ (256 : ℚ⟦X⟧) = 0 := dnum 256
  have d272 : derivative ℚ (272 : ℚ⟦X⟧) = 0 := dnum 272
  have d576 : derivative ℚ (576 : ℚ⟦X⟧) = 0 := dnum 576
  have d896 : derivative ℚ (896 : ℚ⟦X⟧) = 0 := dnum 896
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-16 * X + 176 * X ^ 2 - 576 * X ^ 3 + 272 * X ^ 4 + 896 * X ^ 5 + 256 * X ^ 6) * G = (-8 * X + 56 * X ^ 2 - 64 * X ^ 3 - 128 * X ^ 4 : ℚ⟦X⟧) + (-8 * X + 56 * X ^ 2 - 80 * X ^ 3 - 64 * X ^ 4) * S := by
    linear_combination (-2 + 14 * X - 20 * X ^ 2 - 16 * X ^ 3 - (2 - 6 * X - 8 * X ^ 2) * S) * hG + (2 - 6 * X - 8 * X ^ 2) * ((2 - 6 * X - 8 * X ^ 2) * G - (4 * X)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-16 * X + 176 * (X * X) - 576 * (X * X * X) + 272 * (X * X * X * X) + 896 * (X * X * X * X * X) + 256 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-16 + 352 * X - 1728 * X ^ 2 + 1088 * X ^ 3 + 4480 * X ^ 4 + 1536 * X ^ 5) * G + (-16 * X + 176 * X ^ 2 - 576 * X ^ 3 + 272 * X ^ 4 + 896 * X ^ 5 + 256 * X ^ 6) * derivative ℚ G := by
    simp [Derivation.leibniz, d16, d176, d256, d272, d576, d896]
    ring
  have hR : derivative ℚ ((-8 * X + 56 * (X * X) - 64 * (X * X * X) - 128 * (X * X * X * X) : ℚ⟦X⟧) + (-8 * X + 56 * (X * X) - 80 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * S) =
      -8 + 112 * X - 192 * X ^ 2 - 512 * X ^ 3 + (-8 + 112 * X - 240 * X ^ 2 - 256 * X ^ 3) * S + (-8 * X + 56 * X ^ 2 - 80 * X ^ 3 - 64 * X ^ 4) * derivative ℚ S := by
    simp [Derivation.leibniz, d8, d56, d64, d80, d128]
    ring
  have hk2 : (-16 * X + 176 * (X * X) - 576 * (X * X * X) + 272 * (X * X * X * X) + 896 * (X * X * X * X * X) + 256 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G = (-8 * X + 56 * (X * X) - 64 * (X * X * X) - 128 * (X * X * X * X) : ℚ⟦X⟧) + (-8 * X + 56 * (X * X) - 80 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-16 + 352 * X - 1728 * X ^ 2 + 1088 * X ^ 3 + 4480 * X ^ 4 + 1536 * X ^ 5) * G + (-16 * X + 176 * X ^ 2 - 576 * X ^ 3 + 272 * X ^ 4 + 896 * X ^ 5 + 256 * X ^ 6) * derivative ℚ G =
      -8 + 112 * X - 192 * X ^ 2 - 512 * X ^ 3 + (-8 + 112 * X - 240 * X ^ 2 - 256 * X ^ 3) * S + (-8 * X + 56 * X ^ 2 - 80 * X ^ 3 - 64 * X ^ 4) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 2 * ((1 - 12 * X + 48 * X ^ 2 - 64 * X ^ 3) * ((256 - 2560 * X + 6912 * X ^ 2 + 1280 * X ^ 3 - 14592 * X ^ 4 - 10752 * X ^ 5 - 2048 * X ^ 6) * derivative ℚ G + (-512 + 2048 * X + 3328 * X ^ 2 - 10240 * X ^ 3 - 11264 * X ^ 4 - 3072 * X ^ 5) * G - (256 - 1024 * X - 512 * X ^ 2 - 512 * X ^ 3))) = 0 := by
    linear_combination (-8 * X + 56 * X ^ 2 - 80 * X ^ 3 - 64 * X ^ 4) ^ 2 * S * hdS - 2 * (-8 * X + 56 * X ^ 2 - 80 * X ^ 3 - 64 * X ^ 4) ^ 2 * derivative ℚ S * hS -
      (2 * (-8 + 112 * X - 240 * X ^ 2 - 256 * X ^ 3) * (1 - 4 * X) + (-8 * X + 56 * X ^ 2 - 80 * X ^ 3 - 64 * X ^ 4) * (-4)) * hk + 2 * (-8 * X + 56 * X ^ 2 - 80 * X ^ 3 - 64 * X ^ 4) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero 2 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 12 * X + 48 * X ^ 2 - 64 * X ^ 3 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-2 + 14 * X - 20 * X ^ 2 - 16 * X ^ 3 + (2 - 6 * X - 8 * X ^ 2) * S) = 0 + (4 * X) * S) :
    derivative ℚ G * C 256 + derivative ℚ G * X * C (-2560) +
      derivative ℚ G * X * X * C 6912 + derivative ℚ G * X * X * X * C 1280 +
      derivative ℚ G * X * X * X * X * C (-14592) + derivative ℚ G * X * X * X * X * X * C (-10752) +
      derivative ℚ G * X * X * X * X * X * X * C (-2048) + G * C (-512) +
      G * X * C 2048 + G * X * X * C 3328 +
      G * X * X * X * C (-10240) + G * X * X * X * X * C (-11264) +
      G * X * X * X * X * X * C (-3072) =
      C 256 + C (-1024) * X +
      C (-512) * X * X + C (-512) * X * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-2 + 14 * X - 20 * X ^ 2 - 16 * X ^ 3 + (2 - 6 * X - 8 * X ^ 2) * S) = 0 + (4 * X) * S) (m : ℕ) :
    256 * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-2560) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      6912 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 1280 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-14592) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-10752) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-2048) * ((m : ℚ) + 1) * coeff (m + 1) G + (-512) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      2048 * coeff (m + 1 + 1 + 1 + 1 + 1) G + 3328 * coeff (m + 1 + 1 + 1 + 1) G +
      (-10240) * coeff (m + 1 + 1 + 1) G + (-11264) * coeff (m + 1 + 1) G +
      (-3072) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-2 + 14 * X - 20 * X ^ 2 - 16 * X ^ 3 + (2 - 6 * X - 8 * X ^ 2) * S) = 0 + (4 * X) * S) :
    1536 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-12800) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      27648 * coeff (0 + 1 + 1 + 1 + 1) G + 3840 * coeff (0 + 1 + 1 + 1) G +
      (-29184) * coeff (0 + 1 + 1) G + (-10752) * coeff (0 + 1) G +
      (-512) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 2048 * coeff (0 + 1 + 1 + 1 + 1) G +
      3328 * coeff (0 + 1 + 1 + 1) G + (-10240) * coeff (0 + 1 + 1) G +
      (-11264) * coeff (0 + 1) G + (-3072) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A113956Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a113956.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 6, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m := rfl
  rw [e1, e2, e3, e4, e5, e6]
  cases m with
  | zero =>
    have r := A113956Aux.relE0 (S) G (by linear_combination hS)
      (by linear_combination 4 * PowerSeries.X * hG + G * (1 - 4 * PowerSeries.X) * (2 + PowerSeries.X) * hS -
        G * (1 - 4 * PowerSeries.X) * (2 * S - PowerSeries.X + PowerSeries.X * S - 2 * PowerSeries.X ^ 2 * c) * hc)
    push_cast
    linear_combination ((1 : ℚ) / 256) * r
  | succ m =>
    have r := A113956Aux.rel (S) G (by linear_combination hS)
      (by linear_combination 4 * PowerSeries.X * hG + G * (1 - 4 * PowerSeries.X) * (2 + PowerSeries.X) * hS -
        G * (1 - 4 * PowerSeries.X) * (2 * S - PowerSeries.X + PowerSeries.X * S - 2 * PowerSeries.X ^ 2 * c) * hc) m
    push_cast
    linear_combination ((1 : ℚ) / 256) * r
