import OMAStatements.S_oeis_a105696
import Mathlib

namespace OMA.P105696

open PowerSeries

lemma dOfNat (m : ℕ) [m.AtLeastTwo] : derivative ℚ (ofNat(m) : PowerSeries ℚ) = 0 := by
  rw [← Nat.cast_ofNat (R := PowerSeries ℚ)]
  exact Derivation.map_natCast _ _

/-- The first-order differential equation satisfied by F. -/
lemma ode (F : ℚ⟦X⟧) (hF : F ^ 2 * (1 - 3 * X) = (1 - X) ^ 2 * (1 + X)) (h0 : coeff 0 F = 1) :
    (1 - 3 * X - X ^ 2 + 3 * X ^ 3) * derivative ℚ F - (1 + 3 * X ^ 2) * F = 0 := by
  have hF' := congrArg (derivative ℚ) hF
  simp only [map_add, map_sub, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero] at hF'
  have hne : (2 * F : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h1 : coeff 0 ((2 : ℚ⟦X⟧) * F) = 2 := by
      rw [show (2 : ℚ⟦X⟧) = C (2 : ℚ) from (map_ofNat C 2).symm, coeff_C_mul, h0]
      norm_num
    rw [h, map_zero] at h1
    norm_num at h1
  have hm : (2 * F) * ((1 - 3 * X - X ^ 2 + 3 * X ^ 3) * derivative ℚ F - (1 + 3 * X ^ 2) * F) = 0 := by
    push_cast at hF'
    linear_combination (1 - X ^ 2) * hF' + (1 + 3 * X) * hF
  exact (mul_eq_zero.mp hm).resolve_left hne

lemma odeC (F : ℚ⟦X⟧) (hF : F ^ 2 * (1 - 3 * X) = (1 - X) ^ 2 * (1 + X)) (h0 : coeff 0 F = 1) :
    C (1 : ℚ) * derivative ℚ F + C (-3 : ℚ) * (X ^ 1 * derivative ℚ F)
      + C (-1 : ℚ) * (X ^ 2 * derivative ℚ F) + C (3 : ℚ) * (X ^ 3 * derivative ℚ F)
      - (C (1 : ℚ) * F + C (3 : ℚ) * (X ^ 2 * F)) = 0 := by
  have h := ode F hF h0
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

lemma hrec (F : ℚ⟦X⟧) (hF : F ^ 2 * (1 - 3 * X) = (1 - X) ^ 2 * (1 + X)) (h0 : coeff 0 F = 1)
    (N : ℕ) :
    ((N : ℚ) + 3) * coeff (N + 3) F + (-3 * ((N : ℚ) + 3) + 2) * coeff (N + 2) F
      + (-((N : ℚ) + 3) + 2) * coeff (N + 1) F + 3 * (((N : ℚ) + 3) - 4) * coeff N F = 0 := by
  have h := congrArg (coeff (N + 2)) (odeC F hF h0)
  have e0 : coeff (N + 2) (derivative ℚ F) = coeff (N + 3) F * ((N : ℚ) + 3) := by
    rw [coeff_derivative]
    push_cast
    ring
  have e1 : coeff (N + 2) (X ^ 1 * derivative ℚ F) = coeff (N + 2) F * ((N : ℚ) + 2) := by
    rw [show N + 2 = N + 1 + 1 from rfl, coeff_X_pow_mul, coeff_derivative]
    push_cast
    ring
  have e2 : coeff (N + 2) (X ^ 2 * derivative ℚ F) = coeff (N + 1) F * ((N : ℚ) + 1) := by
    rw [coeff_X_pow_mul, coeff_derivative]
  have e3 : coeff (N + 2) (X ^ 3 * derivative ℚ F) = coeff N F * (N : ℚ) := by
    rcases N with _ | M
    · rw [coeff_X_pow_mul', if_neg (by omega)]
      simp
    · rw [show M + 1 + 2 = M + 3 from by omega, coeff_X_pow_mul, coeff_derivative]
      push_cast
      ring
  have f2 : coeff (N + 2) (X ^ 2 * F) = coeff N F := by
    rw [coeff_X_pow_mul]
  simp only [map_add, map_sub, coeff_C_mul, e0, e1, e2, e3, f2, map_zero] at h
  linear_combination h

end OMA.P105696

theorem OMA.solution : type_of% @OMA.S_oeis_a105696.main := by
  intro F hF h0 n hn
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 3 := ⟨n - 3, by omega⟩
  have h := OMA.P105696.hrec F hF h0 N
  have t1 : N + 3 - 1 = N + 2 := by omega
  have t2 : N + 3 - 2 = N + 1 := by omega
  have t3 : N + 3 - 3 = N := by omega
  simp only [t1, t2, t3]
  push_cast
  linear_combination h
