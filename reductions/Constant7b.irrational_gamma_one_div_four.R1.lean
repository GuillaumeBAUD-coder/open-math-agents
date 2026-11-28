import FormalConjectures.OptimizationConstants.«7b»
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.Tactic

/-!
# Reduction of `Constant7b.irrational_gamma_one_div_four`

Following G. V. Chudnovsky (*Algebraic independence of constants connected with the exponential
and the elliptic functions*, Dokl. Akad. Nauk Ukrain. SSR Ser. A 1976, no. 8, 698–701), we reduce
the irrationality of `Γ(1/4)` to two independent classical theorems on Weierstrass elliptic
lattices (`PeriodPair` in Mathlib):
1. `H1`: **Lemniscatic period invariant** — for the square period lattice `L = ℤ Ω + ℤ (i Ω)` with
   Gauss's lemniscate constant `Ω = 2 ∫₀¹ (1 - t⁴)^(-1/2) dt`, the Weierstrass invariant satisfies
   `L.g₂ = 4`.
2. `H2`: **Chudnovsky's algebraic-independence theorem for square CM lattices** — for every square
   Weierstrass lattice `L = ℤ ω + ℤ (i ω)` (`ω > 0`) with rational invariants `L.g₂, L.g₃ ∈ ℚ`,
   the real period `ω` and the Legendre quasi-period `π / ω` are algebraically independent over `ℚ`.

Inside `main`, we prove from scratch:
- The Euler Beta substitution `u = t⁴` (`MeasureTheory.integral_Icc_deriv_smul_of_deriv_nonneg`),
  identifying `Complex.betaIntegral (1 / 4) (1 / 2) = 2 * Ω`.
- The Gamma-Beta-reflection identity `Γ(1/4)⁴ = 8 * π * Ω²` (via
  `Complex.Gamma_mul_Gamma_eq_betaIntegral`, `Real.Gamma_mul_Gamma_one_sub`, and
  `Real.Gamma_one_half_eq`), together with `0 < Ω`.
- Construction of the square `PeriodPair` `L` (`ω₁ = Ω`, `ω₂ = i Ω`) and proof that `L.g₃ = 0` by
  four-fold rotational symmetry (`i · L = L`).
- Deduction of `Irrational (Real.Gamma (1 / 4))` from `AlgebraicIndependent ℚ ![Ω, π / Ω]` using
  the explicit nonzero polynomial `X₀³ X₁ - q⁴ / 8 ∈ ℚ[X₀, X₁]`.

Thanks to @MechaNuggan for the lemniscate Beta-integral and square-lattice period analysis.
Credit: @tkaiman
-/

namespace OMA.R_Constant7b_irrational_gamma_one_div_four_R1

open MeasureTheory Set

private noncomputable def lemOmega : ℝ :=
  2 * ∫ t in Set.Ioo (0 : ℝ) 1, (1 - t ^ 4) ^ (-(1 / 2 : ℝ))

private lemma betaIntegral_quarter_half_eq :
    Complex.betaIntegral (1 / 4) (1 / 2) = ((2 * lemOmega : ℝ) : ℂ) := by
  have h1 : Complex.betaIntegral (1 / 4) (1 / 2) =
      ∫ x in Set.Ioo (0 : ℝ) 1,
        (((x ^ (-(3 / 4 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    have hx0 : (0 : ℝ) ≤ x := hx.1.le
    have hx1 : (0 : ℝ) ≤ 1 - x := sub_nonneg.mpr hx.2.le
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx0, Complex.ofReal_cpow hx1]
    congr 1
    · congr 1; push_cast; ring
    · rw [Complex.ofReal_sub, Complex.ofReal_one]
      congr 1; push_cast; ring
  rw [h1, integral_complex_ofReal]
  congr 1
  have hsub := MeasureTheory.integral_Icc_deriv_smul_of_deriv_nonneg
    (a := (0 : ℝ)) (b := (1 : ℝ))
    (f := fun t : ℝ => t ^ 4)
    (f' := fun t : ℝ => 4 * t ^ 3)
    (g := fun x : ℝ => x ^ (-(3 / 4 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ)))
    (continuous_pow 4).continuousOn
    (fun t _ => by simpa using (hasDerivAt_pow 4 t))
    (fun t ht => by positivity [ht.1.le])
    (by norm_num)
  have h04 : (0 : ℝ) ^ 4 = 0 := by norm_num
  have h14 : (1 : ℝ) ^ 4 = 1 := by norm_num
  rw [h04, h14] at hsub
  rw [← MeasureTheory.integral_Icc_eq_integral_Ioo, ← hsub,
    MeasureTheory.integral_Icc_eq_integral_Ioo]
  have hcongr : ∫ t in Set.Ioo (0 : ℝ) 1,
      (4 * t ^ 3) • ((t ^ 4) ^ (-(3 / 4 : ℝ)) * (1 - t ^ 4) ^ (-(1 / 2 : ℝ))) =
      ∫ t in Set.Ioo (0 : ℝ) 1, 4 * (1 - t ^ 4) ^ (-(1 / 2 : ℝ)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    simp only [smul_eq_mul]
    have ht0 : 0 < t := ht.1
    have hpow : (t ^ 4) ^ (-(3 / 4 : ℝ)) = (t ^ 3)⁻¹ := by
      rw [← Real.rpow_natCast t 4, ← Real.rpow_mul ht0.le]
      have hexp : ((4 : ℕ) : ℝ) * -(3 / 4 : ℝ) = -((3 : ℕ) : ℝ) := by norm_num
      rw [hexp, Real.rpow_neg ht0.le, Real.rpow_natCast]
    rw [hpow]
    have ht3 : t ^ 3 ≠ 0 := pow_ne_zero 3 ht0.ne'
    field_simp [ht3]
  rw [hcongr, MeasureTheory.integral_const_mul, lemOmega]
  ring

private lemma gamma_quarter_pow_four :
    Real.Gamma (1 / 4) ^ 4 = 8 * Real.pi * lemOmega ^ 2 := by
  have hbetaC := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := (1 / 4 : ℂ)) (t := (1 / 2 : ℂ)) (by norm_num) (by norm_num)
  have hsum : (1 / 4 : ℂ) + 1 / 2 = ((3 / 4 : ℝ) : ℂ) := by push_cast; ring
  have h14 : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by push_cast; rfl
  have h12 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hsum, betaIntegral_quarter_half_eq, h14, h12,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul] at hbetaC
  have hbeta : Real.Gamma (1 / 4) * Real.Gamma (1 / 2) = Real.Gamma (3 / 4) * (2 * lemOmega) :=
    Complex.ofReal_inj.mp hbetaC
  have hrefl : Real.Gamma (1 / 4) * Real.Gamma (3 / 4) = Real.pi * Real.sqrt 2 := by
    have h := Real.Gamma_mul_Gamma_one_sub (1 / 4 : ℝ)
    have hsub : (1 : ℝ) - 1 / 4 = 3 / 4 := by norm_num
    have hsin : Real.sin (Real.pi * (1 / 4)) = Real.sqrt 2 / 2 := by
      rw [show Real.pi * (1 / 4 : ℝ) = Real.pi / 4 by ring, Real.sin_pi_div_four]
    rw [hsub, hsin] at h
    have hsq2 : Real.sqrt 2 ≠ 0 := by positivity
    rw [h, div_div_eq_mul_div]
    field_simp [hsq2]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hmul : Real.Gamma (1 / 4) ^ 2 * Real.sqrt Real.pi =
      Real.pi * Real.sqrt 2 * (2 * lemOmega) := by
    calc Real.Gamma (1 / 4) ^ 2 * Real.sqrt Real.pi
        = Real.Gamma (1 / 4) * (Real.Gamma (1 / 4) * Real.Gamma (1 / 2)) := by
            rw [Real.Gamma_one_half_eq]; ring
      _ = Real.Gamma (1 / 4) * (Real.Gamma (3 / 4) * (2 * lemOmega)) := by rw [hbeta]
      _ = (Real.Gamma (1 / 4) * Real.Gamma (3 / 4)) * (2 * lemOmega) := by ring
      _ = Real.pi * Real.sqrt 2 * (2 * lemOmega) := by rw [hrefl]
  have hsq : (Real.Gamma (1 / 4) ^ 2 * Real.sqrt Real.pi) ^ 2 =
      (Real.pi * Real.sqrt 2 * (2 * lemOmega)) ^ 2 := congrArg (· ^ 2) hmul
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsq_pi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt hpi_pos.le
  have hsq_2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h4 : Real.Gamma (1 / 4) ^ 4 * Real.pi = 8 * Real.pi ^ 2 * lemOmega ^ 2 := by
    calc Real.Gamma (1 / 4) ^ 4 * Real.pi
        = (Real.Gamma (1 / 4) ^ 2) ^ 2 * Real.sqrt Real.pi ^ 2 := by rw [hsq_pi]; ring
      _ = (Real.Gamma (1 / 4) ^ 2 * Real.sqrt Real.pi) ^ 2 := by ring
      _ = (Real.pi * Real.sqrt 2 * (2 * lemOmega)) ^ 2 := hsq
      _ = Real.pi ^ 2 * Real.sqrt 2 ^ 2 * (4 * lemOmega ^ 2) := by ring
      _ = 8 * Real.pi ^ 2 * lemOmega ^ 2 := by rw [hsq_2]; ring
  nlinarith

private lemma lemOmega_pos : 0 < lemOmega := by
  have hge : 0 ≤ lemOmega := by
    unfold lemOmega
    refine mul_nonneg (by norm_num) ?_
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioo fun t ht => ?_
    have h1 : (0 : ℝ) ≤ 1 - t ^ 4 := by
      have ht1 : t ^ 4 ≤ 1 := pow_le_one₀ ht.1.le ht.2.le
      linarith
    exact Real.rpow_nonneg h1 _
  have hne : lemOmega ≠ 0 := by
    intro h0
    have hgam : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
    have h4 := gamma_quarter_pow_four
    rw [h0] at h4
    nlinarith [pow_pos hgam 4]
  exact lt_of_le_of_ne hge hne.symm

private lemma square_linearIndependent (ω : ℝ) (hω : 0 < ω) :
    LinearIndependent ℝ (![(ω : ℂ), (ω : ℂ) * Complex.I] : Fin 2 → ℂ) := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hre := congrArg Complex.re hab
  have him := congrArg Complex.im hab
  simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re,
    Complex.zero_im, mul_zero, mul_one, sub_zero, add_zero, zero_add, zero_mul] at hre him
  exact ⟨mul_eq_zero.mp hre |>.resolve_right hω.ne', mul_eq_zero.mp him |>.resolve_right hω.ne'⟩

private lemma square_g3_eq_zero (L : PeriodPair) (ω : ℝ)
    (h1 : L.ω₁ = (ω : ℂ)) (h2 : L.ω₂ = (ω : ℂ) * Complex.I) :
    L.g₃ = 0 := by
  have hmulI : ∀ z ∈ L.lattice, Complex.I * z ∈ L.lattice := by
    intro z hz
    rw [PeriodPair.mem_lattice] at hz ⊢
    obtain ⟨m, n, rfl⟩ := hz
    refine ⟨-n, m, ?_⟩
    rw [h1, h2]
    push_cast
    have hmul : Complex.I * ((m : ℂ) * (ω : ℂ) + (n : ℂ) * ((ω : ℂ) * Complex.I)) =
        (m : ℂ) * ((ω : ℂ) * Complex.I) + (n : ℂ) * (ω : ℂ) * (Complex.I ^ 2) := by ring
    rw [hmul, Complex.I_sq]
    ring
  let e : L.lattice ≃ L.lattice :=
    { toFun := fun l => ⟨Complex.I * l.1, hmulI l.1 l.2⟩
      invFun := fun l => ⟨-Complex.I * l.1, by
        have h := hmulI _ (hmulI _ (hmulI _ l.2))
        have heq : Complex.I * (Complex.I * (Complex.I * l.1)) = -Complex.I * l.1 := by
          calc Complex.I * (Complex.I * (Complex.I * l.1))
              = (Complex.I ^ 2) * (Complex.I * l.1) := by ring
            _ = (-1) * (Complex.I * l.1) := by rw [Complex.I_sq]
            _ = -Complex.I * l.1 := by ring
        rwa [heq] at h⟩
      left_inv := fun l => by
        ext
        calc -Complex.I * (Complex.I * l.1) = -(Complex.I ^ 2) * l.1 := by ring
          _ = l.1 := by rw [Complex.I_sq]; ring
      right_inv := fun l => by
        ext
        calc Complex.I * (-Complex.I * l.1) = -(Complex.I ^ 2) * l.1 := by ring
          _ = l.1 := by rw [Complex.I_sq]; ring
    }
  have hG6 : L.G 6 = -L.G 6 := by
    calc L.G 6 = ∑' l : L.lattice, ((l : ℂ) ^ 6)⁻¹ := rfl
      _ = ∑' l : L.lattice, (((e l : L.lattice) : ℂ) ^ 6)⁻¹ := (e.tsum_eq _).symm
      _ = ∑' l : L.lattice, -(((l : ℂ) ^ 6)⁻¹) := by
            congr 1 with l
            have hI6 : Complex.I ^ 6 = (-1 : ℂ) := by
              calc Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 := by ring
                _ = (-1 : ℂ) ^ 3 := by rw [Complex.I_sq]
                _ = -1 := by norm_num
            change ((Complex.I * (l : ℂ)) ^ 6)⁻¹ = -(((l : ℂ) ^ 6)⁻¹)
            rw [mul_pow, hI6, neg_one_mul, inv_neg]
      _ = -L.G 6 := tsum_neg
  have hG60 : L.G 6 = 0 := CharZero.eq_neg_self_iff.mp hG6
  simp [PeriodPair.g₃, hG60]

/-- **Lemniscatic period invariant `g₂ = 4`**:
for the square Weierstrass lattice `L = ℤ Ω + ℤ (i Ω)` generated by Gauss's lemniscate constant
`Ω = 2 ∫₀¹ (1 - t⁴)^(-1/2) dt`, the Weierstrass elliptic invariant satisfies `L.g₂ = 4`. -/
def H1 : Prop :=
  ∀ L : PeriodPair,
    L.ω₁ = ((2 * ∫ t in Set.Ioo (0 : ℝ) 1, (1 - t ^ 4) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) →
    L.ω₂ = ((2 * ∫ t in Set.Ioo (0 : ℝ) 1, (1 - t ^ 4) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.I →
    L.g₂ = 4

/-- **Chudnovsky's algebraic-independence theorem (1976) for square CM lattices**:
for every square Weierstrass period lattice `L = ℤ ω + ℤ (i ω)` (`ω > 0`) with rational invariants
`L.g₂, L.g₃ ∈ ℚ`, the real period `ω` and the Legendre quasi-period `π / ω` are algebraically
independent over `ℚ`. -/
def H2 : Prop :=
  ∀ (L : PeriodPair) (ω : ℝ), 0 < ω →
    L.ω₁ = (ω : ℂ) → L.ω₂ = (ω : ℂ) * Complex.I →
    (∃ q₂ : ℚ, L.g₂ = (q₂ : ℂ)) → (∃ q₃ : ℚ, L.g₃ = (q₃ : ℂ)) →
    AlgebraicIndependent ℚ (![ω, Real.pi / ω] : Fin 2 → ℝ)

theorem main : H1 → H2 → type_of% @Constant7b.irrational_gamma_one_div_four := by
  intro h1 h2
  have hωpos : 0 < lemOmega := lemOmega_pos
  let L : PeriodPair :=
    { ω₁ := (lemOmega : ℂ)
      ω₂ := (lemOmega : ℂ) * Complex.I
      indep := square_linearIndependent lemOmega hωpos }
  have hg2 : L.g₂ = 4 := h1 L rfl rfl
  have hg3 : L.g₃ = 0 := square_g3_eq_zero L lemOmega rfl rfl
  have hind : AlgebraicIndependent ℚ (![lemOmega, Real.pi / lemOmega] : Fin 2 → ℝ) :=
    h2 L lemOmega hωpos rfl rfl ⟨4, by simpa using hg2⟩ ⟨0, by simpa using hg3⟩
  rw [irrational_iff_ne_rational]
  intro a b _ hq
  let q : ℚ := (a : ℚ) / (b : ℚ)
  have hq_eq : (q : ℝ) = Real.Gamma (1 / 4) := by
    push_cast [q]
    exact hq.symm
  let P : MvPolynomial (Fin 2) ℚ :=
    MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 - MvPolynomial.C (q ^ 4 / 8)
  have heval : MvPolynomial.aeval (![lemOmega, Real.pi / lemOmega] : Fin 2 → ℝ) P = 0 := by
    simp only [P, map_sub, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Matrix.cons_val_zero, Matrix.cons_val_one, eq_ratCast,
      Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, hq_eq]
    have h4 := gamma_quarter_pow_four
    have hne : lemOmega ≠ 0 := hωpos.ne'
    field_simp [hne]
    linarith
  have hP0 : P = 0 := algebraicIndependent_iff.mp hind P heval
  have hcoeff := congrArg (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 3 + Finsupp.single 1 1)) hP0
  have hne0 : (Finsupp.single (0 : Fin 2) 3 + Finsupp.single 1 1) ≠ 0 := by
    intro h0
    have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h0
    simp at this
  have hX : MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 3 + Finsupp.single 1 1)
      (MvPolynomial.X (0 : Fin 2) ^ 3 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ) = 1 := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X, MvPolynomial.monomial_mul,
      MvPolynomial.coeff_monomial]
    simp
  have hC : MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 3 + Finsupp.single 1 1)
      (MvPolynomial.C (q ^ 4 / 8) : MvPolynomial (Fin 2) ℚ) = 0 := by
    rw [MvPolynomial.coeff_C, if_neg hne0.symm]
  simp only [P, MvPolynomial.coeff_sub, hX, hC, sub_zero, MvPolynomial.coeff_zero] at hcoeff
  norm_num at hcoeff

end OMA.R_Constant7b_irrational_gamma_one_div_four_R1
