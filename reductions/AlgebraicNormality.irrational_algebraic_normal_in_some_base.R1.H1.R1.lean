import OMAReductions.R_AlgebraicNormality_irrational_algebraic_normal_in_some_base_R1

-- Reduction AlgebraicNormality.irrational_algebraic_normal_in_some_base.R1.H1.R1 of step AlgebraicNormality.irrational_algebraic_normal_in_some_base.R1.H1
-- Credit: @arjunkshah12345-hash
-- Splits Wall affine preservation into add-rational, mul-integer, and mul-reciprocal.

open NormalNumber

namespace OMA.R_AlgebraicNormality_irrational_algebraic_normal_in_some_base_R1_H1_R1

def H1 : Prop :=
  ∀ (b : ℕ), 2 ≤ b → ∀ (x : ℝ) (s : ℚ),
    IsNormalInBase b x → IsNormalInBase b (x + (s : ℝ))

def H2 : Prop :=
  ∀ (b : ℕ), 2 ≤ b → ∀ (x : ℝ) (m : ℤ), m ≠ 0 →
    IsNormalInBase b x → IsNormalInBase b ((m : ℝ) * x)

def H3 : Prop :=
  ∀ (b : ℕ), 2 ≤ b → ∀ (x : ℝ) (m : ℕ), m ≠ 0 →
    IsNormalInBase b x → IsNormalInBase b ((m : ℝ)⁻¹ * x)

theorem main :
    H1 → H2 → H3 → OMA.R_AlgebraicNormality_irrational_algebraic_normal_in_some_base_R1.H1 := by
  intro hAdd hMul hInv b hb x r s hr hx
  have hnum : r.num ≠ 0 := Rat.num_ne_zero.mpr hr
  have hden : r.den ≠ 0 := r.den_ne_zero
  have hmul := hMul b hb x r.num hnum hx
  have hscaled := hInv b hb ((r.num : ℝ) * x) r.den hden hmul
  have heq : (r.den : ℝ)⁻¹ * ((r.num : ℝ) * x) = (r : ℝ) * x := by
    calc (r.den : ℝ)⁻¹ * ((r.num : ℝ) * x)
        = ((r.num : ℝ) * (r.den : ℝ)⁻¹) * x := by ring
      _ = ((r.num : ℝ) / (r.den : ℝ)) * x := by rw [div_eq_mul_inv]
      _ = (r : ℝ) * x := by rw [← Rat.cast_def]
  have hrx : IsNormalInBase b ((r : ℝ) * x) := heq ▸ hscaled
  exact hAdd b hb ((r : ℝ) * x) s hrx

end OMA.R_AlgebraicNormality_irrational_algebraic_normal_in_some_base_R1_H1_R1
