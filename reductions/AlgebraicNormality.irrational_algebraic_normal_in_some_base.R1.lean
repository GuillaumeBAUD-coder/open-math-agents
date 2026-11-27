import FormalConjectures.Wikipedia.AlgebraicNormality

-- Reduction AlgebraicNormality.irrational_algebraic_normal_in_some_base.R1 of Normality of Irrational Algebraic Numbers — irrational algebraic normal in some base
-- Credit: @GuillaumeBAUD-coder
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Reduction of normality in some integer base

H1 is Wall's theorem on rational affine changes in a fixed base.
See Theorem 1.3 in Airey, Jackson, and Mance, Descriptive Complexity in Cantor Series:
https://doi.org/10.1017/jsl.2021.77

H2 isolates the square roots of squarefree integers greater than one.
H3 asks for normality in some base for irrational algebraic integers of degree at least three.
Clearing denominators gives an algebraic integer, and completing the square handles degree two.
-/

open AlgebraicNormality NormalNumber Polynomial

namespace OMA.R_AlgebraicNormality_irrational_algebraic_normal_in_some_base_R1

private theorem quadratic_as_affine_radical {x : ℝ}
    (hx : IsIntegral ℤ x) (hirr : Irrational x)
    (hdeg : (minpoly ℚ x).natDegree = 2) :
    ∃ (d : ℕ) (r s : ℚ), 2 ≤ d ∧ Squarefree d ∧ r ≠ 0 ∧
      x = (r : ℝ) * Real.sqrt (d : ℝ) + (s : ℝ) := by
  let p := minpoly ℤ x
  have hmonic : p.Monic := minpoly.monic hx
  have hdegZ : p.natDegree = 2 := by
    rw [← hmonic.natDegree_map (algebraMap ℤ ℚ),
      ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx, hdeg]
  have hcoeff : p.coeff 2 = 1 := by
    simpa only [hdegZ] using hmonic.coeff_natDegree
  let a := p.coeff 1
  let c := p.coeff 0
  have hp : p = C c + C a * X + X ^ 2 := by
    conv_lhs => rw [p.as_sum_range_C_mul_X_pow, hdegZ]
    simp [Finset.sum_range_succ, hcoeff, a, c]
  have hp_eval : aeval x p = 0 := minpoly.aeval ℤ x
  rw [hp] at hp_eval
  have hroot : x ^ 2 + (a : ℝ) * x + (c : ℝ) = 0 := by
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C] at hp_eval
    change (c : ℝ) + (a : ℝ) * x + x ^ 2 = 0 at hp_eval
    linarith only [hp_eval]

  let z : ℝ := 2 * x + (a : ℝ)
  let D : ℤ := a ^ 2 - 4 * c
  have hz : Irrational z :=
    (hirr.natCast_mul (by decide : (2 : ℕ) ≠ 0)).add_intCast a
  have hdisc : z ^ 2 = (D : ℝ) := by
    dsimp only [z, D]
    push_cast
    nlinarith only [hroot]
  have hDreal : (0 : ℝ) < (D : ℝ) := hdisc ▸ sq_pos_of_ne_zero hz.ne_zero
  have hD : 0 < D := by exact_mod_cast hDreal
  have hDnat : 0 < D.toNat := by omega
  obtain ⟨d, m, hd, hm, hfactor, hfree⟩ := Nat.sq_mul_squarefree_of_pos hDnat
  have hfactorReal : (D : ℝ) = (m : ℝ) ^ 2 * (d : ℝ) := by
    calc
      (D : ℝ) = (D.toNat : ℝ) := by exact_mod_cast (Int.toNat_of_nonneg hD.le).symm
      _ = (m : ℝ) ^ 2 * (d : ℝ) := by exact_mod_cast hfactor.symm
  have hsquare : ((m : ℝ) * Real.sqrt (d : ℝ)) ^ 2 = (D : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by positivity), hfactorReal]
  obtain ⟨q, hq, hzq⟩ :
      ∃ q : ℚ, q ≠ 0 ∧ z = (q : ℝ) * Real.sqrt (d : ℝ) := by
    have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hdisc.trans hsquare.symm) with h | h
    · exact ⟨m, hmQ, by simpa using h⟩
    · exact ⟨-(m : ℚ), neg_ne_zero.mpr hmQ, by simpa using h⟩
  have hrad : Irrational (Real.sqrt (d : ℝ)) :=
    (hzq ▸ hz).of_ratCast_mul q
  have hd2 : 2 ≤ d := by
    by_contra! hlt
    have hd1 : d = 1 := by omega
    exact hrad.ne_one (by simp [hd1])
  refine ⟨d, q / 2, -(a : ℚ) / 2, hd2, hfree, div_ne_zero hq (by norm_num), ?_⟩
  dsimp only [z] at hzq
  push_cast
  linarith only [hzq]

def H1 : Prop :=
  ∀ (b : ℕ), 2 ≤ b → ∀ (x : ℝ) (r s : ℚ), r ≠ 0 →
    IsNormalInBase b x → IsNormalInBase b ((r : ℝ) * x + (s : ℝ))

def H2 : Prop :=
  ∀ d : ℕ, 2 ≤ d → Squarefree d →
    ∃ b : ℕ, 2 ≤ b ∧ IsNormalInBase b (Real.sqrt (d : ℝ))

def H3 : Prop :=
  ∀ x : ℝ, IsIntegral ℤ x → Irrational x → 3 ≤ (minpoly ℚ x).natDegree →
    ∃ b : ℕ, 2 ≤ b ∧ IsNormalInBase b x

theorem main : H1 → H2 → H3 → type_of% @AlgebraicNormality.irrational_algebraic_normal_in_some_base := by
  intro hAffine hRadical hHigher x hx
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors ℤ) (Rₘ := ℚ) x hx.1.isIntegral
  have hm0 : (m : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp m.property
  let y : ℝ := ((m : ℤ) : ℝ) * x
  have hyInt : IsIntegral ℤ y := by
    simpa only [y, Submonoid.smul_def, zsmul_eq_mul] using hm
  have hyIrr : Irrational y := hx.2.intCast_mul hm0
  have hyDeg : 2 ≤ (minpoly ℚ y).natDegree :=
    (minpoly.two_le_natDegree_iff (hyInt.tower_top (A := ℚ))).2 hyIrr
  have hyNormal : ∃ b : ℕ, 2 ≤ b ∧ IsNormalInBase b y := by
    by_cases hDegree : (minpoly ℚ y).natDegree = 2
    · obtain ⟨d, r, s, hd, hfree, hr, hyr⟩ :=
        quadratic_as_affine_radical hyInt hyIrr hDegree
      obtain ⟨b, hb, hnormal⟩ := hRadical d hd hfree
      exact ⟨b, hb, hyr.symm ▸ hAffine b hb _ r s hr hnormal⟩
    · exact hHigher y hyInt hyIrr (by omega)
  obtain ⟨b, hb, hnormal⟩ := hyNormal
  have hmQ : ((m : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hm0
  have hmR : ((m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hm0
  have hback := hAffine b hb y (((m : ℤ) : ℚ)⁻¹) 0 (inv_ne_zero hmQ) hnormal
  exact ⟨b, hb, by simpa [y, ← mul_assoc, inv_mul_cancel₀ hmR] using hback⟩

end OMA.R_AlgebraicNormality_irrational_algebraic_normal_in_some_base_R1
