import OMAStatements.S_mo_465929
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Sharp Dimension-Free Comparison of `W_2` and `W_1` for Centered Gaussian Measures (`mo-465929`)

We prove that for every dimension `d` and all centered Gaussian measures `μ, ν` on
`EuclideanSpace ℝ (Fin d)` (including singular covariance matrices),
`Real.sqrt (transportCost 2 μ ν) ≤ Real.sqrt (Real.pi / 2) * transportCost 1 μ ν`.
-/

namespace OMA_mo_465929

open MeasureTheory ProbabilityTheory Matrix Filter Set WithLp
open scoped ENNReal NNReal Real Topology RealInnerProductSpace

abbrev Ed (d : ℕ) := OMA.S_mo_465929.E d
abbrev RawMat (d : ℕ) := Fin d → Fin d → ℝ

private def toRaw {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : RawMat d := fun i j => M i j
private def ofRaw {d : ℕ} (R : RawMat d) : Matrix (Fin d) (Fin d) ℝ := Matrix.of R

private lemma ofRaw_toRaw {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : ofRaw (toRaw M) = M := by
  ext i j; rfl

private lemma toRaw_ofRaw {d : ℕ} (R : RawMat d) : toRaw (ofRaw R) = R := rfl

/-! ## Section 1: First Absolute Moment of `gaussianReal 0 v` -/

private lemma integral_Ioi_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ in Ioi 0, x * Real.exp (-b * x ^ 2) = (2 * b)⁻¹ := by
  have hb0 : b ≠ 0 := hb.ne'
  have hderiv : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => -(2 * b)⁻¹ * Real.exp (-b * t ^ 2))
        (x * Real.exp (-b * x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => -b * t ^ 2) (-b * (2 * x ^ (2 - 1))) x :=
      (hasDerivAt_pow 2 x).const_mul (-b)
    have h2 : HasDerivAt (fun t : ℝ => -(2 * b)⁻¹ * Real.exp (-b * t ^ 2))
        (-(2 * b)⁻¹ * (Real.exp (-b * x ^ 2) * (-b * (2 * x ^ (2 - 1))))) x :=
      h1.exp.const_mul (-(2 * b)⁻¹)
    refine h2.congr_deriv ?_
    field_simp [hb0]
    ring
  have htend : Tendsto (fun t : ℝ => -(2 * b)⁻¹ * Real.exp (-b * t ^ 2))
      atTop (𝓝 (-(2 * b)⁻¹ * 0)) := by
    refine Tendsto.const_mul _ ?_
    exact Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop_of_neg (neg_lt_zero.mpr hb))
  have hint : IntegrableOn (fun x : ℝ => x * Real.exp (-b * x ^ 2)) (Ioi 0) :=
    (integrable_mul_exp_neg_mul_sq hb).integrableOn
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  simp only [mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), Real.exp_zero, mul_one,
    sub_neg_eq_add, zero_add] at hval
  exact hval

private lemma integral_abs_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, |x| * Real.exp (-b * x ^ 2) = b⁻¹ := by
  have hint_pos : Integrable (fun x : ℝ => |x| * Real.exp (-b * x ^ 2)) := by
    have h := (integrable_mul_exp_neg_mul_sq hb).norm
    refine h.congr (ae_of_all _ fun x => ?_)
    dsimp only
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hint_pos, compl_Ioi]
  have hpos : ∫ x : ℝ in Ioi 0, |x| * Real.exp (-b * x ^ 2) = (2 * b)⁻¹ := by
    rw [← integral_Ioi_mul_exp_neg_mul_sq hb]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [abs_of_pos hx]
  have hneg : ∫ x : ℝ in Iic 0, |x| * Real.exp (-b * x ^ 2) = (2 * b)⁻¹ := by
    have hcomp := integral_comp_neg_Ioi (0 : ℝ) (fun x : ℝ => |x| * Real.exp (-b * x ^ 2))
    simp only [neg_zero, abs_neg, neg_sq] at hcomp
    rw [← hcomp, hpos]
  rw [hpos, hneg]
  have hb0 : b ≠ 0 := hb.ne'
  field_simp [hb0]
  ring

private lemma integral_abs_gaussianReal_zero (v : ℝ≥0) :
    ∫ x : ℝ, |x| ∂(gaussianReal 0 v) = Real.sqrt (2 / Real.pi) * Real.sqrt (v : ℝ) := by
  by_cases hv : v = 0
  · subst hv
    simp [gaussianReal_zero_var]
  · have hv_pos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
    rw [integral_gaussianReal_eq_integral_smul hv]
    simp only [smul_eq_mul, gaussianPDFReal_def, sub_zero]
    have hrew : (fun x : ℝ => (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-x ^ 2 / (2 * v)) * |x|) =
        fun x : ℝ => (Real.sqrt (2 * Real.pi * v))⁻¹ * (|x| * Real.exp (-(2 * (v : ℝ))⁻¹ * x ^ 2)) := by
      funext x
      have : -x ^ 2 / (2 * (v : ℝ)) = -(2 * (v : ℝ))⁻¹ * x ^ 2 := by field_simp [hv_pos.ne']
      rw [this]
      ring
    rw [hrew, integral_const_mul, integral_abs_mul_exp_neg_mul_sq (by positivity), inv_inv]
    have hpi : 0 < Real.pi := Real.pi_pos
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hsqv : Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ) = (v : ℝ) := Real.mul_self_sqrt hv_pos.le
    have hsp : Real.sqrt (Real.pi) ≠ 0 := (Real.sqrt_pos.mpr hpi).ne'
    have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hsv : Real.sqrt (v : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hv_pos).ne'
    field_simp [hsp, hs2, hsv]
    nlinarith [hsq2, hsqv]

/-! ## Section 2: Spectral Square Root & Brenier Eigenbasis Identity -/

private def IsSymmPSD {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  S.IsHermitian ∧ ∀ x : Fin d → ℝ, 0 ≤ x ⬝ᵥ (S *ᵥ x)

private lemma IsSymmPSD.transpose_eq {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : IsSymmPSD S) :
    Sᵀ = S := by
  simpa using hS.1.eq

private lemma IsSymmPSD.eigenvalues_nonneg {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : IsSymmPSD S) (i : Fin d) : 0 ≤ hS.1.eigenvalues i := by
  rw [hS.1.eigenvalues_eq i]
  simpa using hS.2 (⇑(hS.1.eigenvectorBasis i))

private lemma vecMul_eq_transpose_mulVec {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    x ᵥ* M = Mᵀ *ᵥ x := by
  ext i; simp [vecMul, mulVec, dotProduct, mul_comm]

private lemma star_matrix_real {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : star M = Mᵀ := by
  ext i j; simp

private noncomputable def eigU {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.IsHermitian) :
    Matrix (Fin d) (Fin d) ℝ :=
  (hS.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)

private lemma eigU_mul_transpose {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.IsHermitian) :
    eigU hS * (eigU hS)ᵀ = 1 := by
  have h := Unitary.coe_mul_star_self hS.eigenvectorUnitary
  rwa [Unitary.coe_star, star_matrix_real] at h

private lemma eigU_transpose_mul {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.IsHermitian) :
    (eigU hS)ᵀ * eigU hS = 1 := by
  have h := Unitary.coe_star_mul_self hS.eigenvectorUnitary
  rwa [star_matrix_real] at h

private lemma spectral_decomp_real {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.IsHermitian) :
    S = eigU hS * Matrix.diagonal hS.eigenvalues * (eigU hS)ᵀ := by
  have h := hS.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  simpa [eigU, Unitary.coe_star, star_matrix_real] using h

private noncomputable def sqrtM {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : IsSymmPSD S) :
    Matrix (Fin d) (Fin d) ℝ :=
  eigU hS.1 * Matrix.diagonal (fun i => Real.sqrt (hS.1.eigenvalues i)) * (eigU hS.1)ᵀ

private noncomputable def sqrtEps {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : IsSymmPSD S)
    (ε : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  eigU hS.1 * Matrix.diagonal (fun i => Real.sqrt (hS.1.eigenvalues i + ε)) * (eigU hS.1)ᵀ

private noncomputable def invSqrtEps {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : IsSymmPSD S)
    (ε : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  eigU hS.1 * Matrix.diagonal (fun i => (Real.sqrt (hS.1.eigenvalues i + ε))⁻¹) * (eigU hS.1)ᵀ

private lemma symm_conj_diag {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    (Q * Matrix.diagonal v * Qᵀ)ᵀ = Q * Matrix.diagonal v * Qᵀ := by
  rw [transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]

private lemma psd_conj_diag {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ)
    (hv : ∀ i, 0 ≤ v i) : IsSymmPSD (Q * Matrix.diagonal v * Qᵀ) := by
  refine ⟨?_, fun x => ?_⟩
  · change (Q * Matrix.diagonal v * Qᵀ)ᵀ = _
    exact symm_conj_diag Q v
  · have hrew : x ⬝ᵥ ((Q * Matrix.diagonal v * Qᵀ) *ᵥ x) =
        ∑ i : Fin d, v i * (Qᵀ *ᵥ x) i ^ 2 := by
      rw [Matrix.mul_assoc, ← mulVec_mulVec, dotProduct_mulVec, vecMul_eq_transpose_mulVec,
        ← mulVec_mulVec]
      simp only [dotProduct, mulVec_diagonal]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hrew]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hv i) (sq_nonneg _)

private lemma sqrtM_symm {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : IsSymmPSD S) :
    (sqrtM hS)ᵀ = sqrtM hS :=
  symm_conj_diag _ _

private lemma sqrtM_psd {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : IsSymmPSD S) :
    IsSymmPSD (sqrtM hS) :=
  psd_conj_diag _ _ fun _ => Real.sqrt_nonneg _

private lemma conj_diag_mul {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.IsHermitian)
    (u v : Fin d → ℝ) :
    (eigU hS * Matrix.diagonal u * (eigU hS)ᵀ) * (eigU hS * Matrix.diagonal v * (eigU hS)ᵀ) =
      eigU hS * Matrix.diagonal (fun i => u i * v i) * (eigU hS)ᵀ := by
  calc (eigU hS * Matrix.diagonal u * (eigU hS)ᵀ) * (eigU hS * Matrix.diagonal v * (eigU hS)ᵀ)
      = eigU hS * Matrix.diagonal u * ((eigU hS)ᵀ * eigU hS) * Matrix.diagonal v * (eigU hS)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = eigU hS * (Matrix.diagonal u * Matrix.diagonal v) * (eigU hS)ᵀ := by
        rw [eigU_transpose_mul, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = eigU hS * Matrix.diagonal (fun i => u i * v i) * (eigU hS)ᵀ := by
        rw [diagonal_mul_diagonal]

private lemma sqrtM_mul_self {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : IsSymmPSD S) :
    sqrtM hS * sqrtM hS = S := by
  dsimp only [sqrtM]
  rw [conj_diag_mul]
  have hd : (fun i => Real.sqrt (hS.1.eigenvalues i) * Real.sqrt (hS.1.eigenvalues i)) =
      hS.1.eigenvalues := funext fun i => Real.mul_self_sqrt (hS.eigenvalues_nonneg i)
  rw [hd, ← spectral_decomp_real hS.1]

private lemma sqrtEps_symm {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : IsSymmPSD S) (ε : ℝ) :
    (sqrtEps hS ε)ᵀ = sqrtEps hS ε :=
  symm_conj_diag _ _

private lemma invSqrtEps_symm {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : IsSymmPSD S) (ε : ℝ) :
    (invSqrtEps hS ε)ᵀ = invSqrtEps hS ε :=
  symm_conj_diag _ _

private lemma sqrtEps_mul_self {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : IsSymmPSD S)
    {ε : ℝ} (hε : 0 < ε) :
    sqrtEps hS ε * sqrtEps hS ε = S + ε • 1 := by
  dsimp only [sqrtEps]
  rw [conj_diag_mul]
  have hd : (fun i => Real.sqrt (hS.1.eigenvalues i + ε) * Real.sqrt (hS.1.eigenvalues i + ε)) =
      fun i => hS.1.eigenvalues i + ε :=
    funext fun i => Real.mul_self_sqrt (by linarith [hS.eigenvalues_nonneg i])
  rw [hd]
  have hdiag : Matrix.diagonal (fun i => hS.1.eigenvalues i + ε) =
      Matrix.diagonal hS.1.eigenvalues + ε • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  rw [hdiag, Matrix.mul_add, Matrix.add_mul, ← spectral_decomp_real hS.1]
  simp [eigU_mul_transpose]

private lemma sqrtEps_mul_inv {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : IsSymmPSD S)
    {ε : ℝ} (hε : 0 < ε) :
    sqrtEps hS ε * invSqrtEps hS ε = 1 := by
  dsimp only [sqrtEps, invSqrtEps]
  rw [conj_diag_mul]
  have hd : (fun i => Real.sqrt (hS.1.eigenvalues i + ε) *
      (Real.sqrt (hS.1.eigenvalues i + ε))⁻¹) = fun _ => 1 := by
    funext i
    have hpos : 0 < hS.1.eigenvalues i + ε := by linarith [hS.eigenvalues_nonneg i]
    exact mul_inv_cancel₀ (Real.sqrt_pos.mpr hpos).ne'
  rw [hd, diagonal_one, Matrix.mul_one, eigU_mul_transpose]

private lemma inv_mul_sqrtEps {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : IsSymmPSD S)
    {ε : ℝ} (hε : 0 < ε) :
    invSqrtEps hS ε * sqrtEps hS ε = 1 := by
  have h := congr_arg Matrix.transpose (sqrtEps_mul_inv hS hε)
  rwa [transpose_mul, sqrtEps_symm, invSqrtEps_symm, transpose_one] at h

private lemma tendsto_sqrtEps {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : IsSymmPSD S) :
    Tendsto (fun n : ℕ => toRaw (sqrtEps hS (1 / ((n : ℝ) + 1))))
      atTop (𝓝 (toRaw (sqrtM hS))) := by
  have hcont : Continuous (fun t : ℝ => toRaw
      (eigU hS.1 * Matrix.diagonal (fun i => Real.sqrt (hS.1.eigenvalues i + t)) * (eigU hS.1)ᵀ)) := by
    rw [continuous_pi_iff]; intro i; rw [continuous_pi_iff]; intro j
    simp only [toRaw, Matrix.mul_apply, diagonal_apply, transpose_apply]
    refine continuous_finsetSum _ fun k _ => (continuous_finsetSum _ fun l _ => ?_).mul continuous_const
    by_cases hlk : l = k
    · subst hlk; simp only [↓reduceIte]; fun_prop
    · simp only [hlk, ↓reduceIte, mul_zero]; exact continuous_const
  have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim := (hcont.tendsto 0).comp h0
  simpa only [Function.comp_def, sqrtEps, sqrtM, add_zero] using hlim

private lemma trace_orth_quad_sum {d : ℕ} (E X : Matrix (Fin d) (Fin d) ℝ)
    (hE : E * Eᵀ = 1) :
    (∑ i : Fin d, (Eᵀ i) ⬝ᵥ (X *ᵥ (Eᵀ i))) = X.trace := by
  have hlhs : (∑ i : Fin d, (Eᵀ i) ⬝ᵥ (X *ᵥ (Eᵀ i))) = (Eᵀ * (X * E)).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, dotProduct, mulVec, transpose_apply]
  rw [hlhs, Matrix.trace_mul_comm, Matrix.mul_assoc, hE, Matrix.mul_one]

private lemma frobenius_sq_eq_trace {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    (∑ i : Fin d, ∑ j : Fin d, (M i j) ^ 2) = (M * Mᵀ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, transpose_apply, sq]

private lemma polar_orth_algebra {d : ℕ}
    (M Minv Ph Phi : Matrix (Fin d) (Fin d) ℝ)
    (hPh_symm : Phᵀ = Ph) (hPhi_symm : Phiᵀ = Phi)
    (hPh_sq : Ph * Ph = M * Mᵀ)
    (hPh_Phi : Ph * Phi = 1)
    (hM_inv : M * Minv = 1) (hMinv_M : Minv * M = 1)
    (hMinv_tr : Mᵀ * Minvᵀ = 1) :
    (Minv * Ph)ᵀ * (Minv * Ph) = 1 ∧ (Minv * Ph) * (Minv * Ph)ᵀ = 1 ∧ M * (Minv * Ph) = Ph := by
  have hPhi_Ph : Phi * Ph = 1 := by
    have ht := congr_arg Matrix.transpose hPh_Phi
    rwa [transpose_mul, hPh_symm, hPhi_symm, transpose_one] at ht
  have hMU : M * (Minv * Ph) = Ph := by
    rw [← Matrix.mul_assoc, hM_inv, Matrix.one_mul]
  have h1 : (Minv * Ph)ᵀ * Mᵀ = Ph := by
    rw [transpose_mul, hPh_symm, Matrix.mul_assoc]
    have htr2 : Minvᵀ * Mᵀ = 1 := by
      have ht := congr_arg Matrix.transpose hM_inv
      rwa [transpose_mul, transpose_one] at ht
    rw [htr2, Matrix.mul_one]
  have h2 : (Phi * M) * Mᵀ = Ph := by
    rw [Matrix.mul_assoc, ← hPh_sq, ← Matrix.mul_assoc, hPhi_Ph, Matrix.one_mul]
  have htr_eq : (Minv * Ph)ᵀ = Phi * M := by
    calc (Minv * Ph)ᵀ = (Minv * Ph)ᵀ * (Mᵀ * Minvᵀ) := by rw [hMinv_tr, Matrix.mul_one]
      _ = ((Minv * Ph)ᵀ * Mᵀ) * Minvᵀ := by rw [Matrix.mul_assoc]
      _ = ((Phi * M) * Mᵀ) * Minvᵀ := by rw [h1, h2]
      _ = (Phi * M) * (Mᵀ * Minvᵀ) := by rw [Matrix.mul_assoc]
      _ = Phi * M := by rw [hMinv_tr, Matrix.mul_one]
  have hUU_tr : (Minv * Ph) * (Minv * Ph)ᵀ = 1 := by
    rw [htr_eq]
    calc (Minv * Ph) * (Phi * M) = Minv * (Ph * Phi) * M := by simp only [Matrix.mul_assoc]
      _ = Minv * M := by rw [hPh_Phi, Matrix.mul_one]
      _ = 1 := hMinv_M
  have hU_tr_U : (Minv * Ph)ᵀ * (Minv * Ph) = 1 := by
    rw [htr_eq]
    calc (Phi * M) * (Minv * Ph) = Phi * (M * Minv) * Ph := by simp only [Matrix.mul_assoc]
      _ = Phi * Ph := by rw [hM_inv, Matrix.mul_one]
      _ = 1 := hPhi_Ph
  exact ⟨hU_tr_U, hUU_tr, hMU⟩

private lemma brenier_TAT_algebra {d : ℕ}
    (Ae Be Ah Ahi Bh Ph : Matrix (Fin d) (Fin d) ℝ)
    (hAh_symm : Ahᵀ = Ah) (hAhi_symm : Ahiᵀ = Ahi) (hBh_symm : Bhᵀ = Bh)
    (hAh_sq : Ah * Ah = Ae) (hBh_sq : Bh * Bh = Be)
    (hAh_inv : Ah * Ahi = 1) (hAhi_inv : Ahi * Ah = 1)
    (hPh_symm : Phᵀ = Ph) (hPh_psd : IsSymmPSD Ph)
    (hPh_sq : Ph * Ph = (Ah * Bh) * (Ah * Bh)ᵀ) :
    IsSymmPSD (Ahi * Ph * Ahi) ∧ (Ahi * Ph * Ahi) * Ae * (Ahi * Ph * Ahi) = Be := by
  refine ⟨⟨?_, fun x => ?_⟩, ?_⟩
  · change (Ahi * Ph * Ahi)ᵀ = Ahi * Ph * Ahi
    rw [transpose_mul, transpose_mul, hAhi_symm, hPh_symm, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, ← mulVec_mulVec, dotProduct_mulVec, vecMul_eq_transpose_mulVec,
      hAhi_symm, ← mulVec_mulVec]
    exact hPh_psd.2 (Ahi *ᵥ x)
  · rw [← hAh_sq, ← hBh_sq]
    calc (Ahi * Ph * Ahi) * (Ah * Ah) * (Ahi * Ph * Ahi)
        = Ahi * Ph * (Ahi * Ah) * (Ah * Ahi) * Ph * Ahi := by simp only [Matrix.mul_assoc]
      _ = Ahi * (Ph * Ph) * Ahi := by
          rw [hAhi_inv, hAh_inv, Matrix.mul_one, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = Ahi * (Ah * Bh * (Bh * Ah)) * Ahi := by
          rw [hPh_sq, transpose_mul, hAh_symm, hBh_symm]
      _ = (Ahi * Ah) * Bh * Bh * (Ah * Ahi) := by simp only [Matrix.mul_assoc]
      _ = Bh * Bh := by rw [hAhi_inv, hAh_inv, Matrix.one_mul, Matrix.mul_one]

private lemma brenier_quad_identity {d : ℕ}
    (Ae Be Ah Ahi Bh U Ph T : Matrix (Fin d) (Fin d) ℝ)
    (hT : IsSymmPSD T)
    (hAh_symm : Ahᵀ = Ah) (hBh_symm : Bhᵀ = Bh)
    (hAh_sq : Ah * Ah = Ae) (hBh_sq : Bh * Bh = Be)
    (hAh_inv : Ah * Ahi = 1) (hAhi_inv : Ahi * Ah = 1)
    (hU_mul_tr : U * Uᵀ = 1)
    (hMU : (Ah * Bh) * U = Ph)
    (hT_def : T = Ahi * Ph * Ahi)
    (hTAT : T * Ae * T = Be) :
    (∑ i : Fin d, (Real.sqrt (((eigU hT.1)ᵀ i) ⬝ᵥ (Ae *ᵥ ((eigU hT.1)ᵀ i))) -
        Real.sqrt (((eigU hT.1)ᵀ i) ⬝ᵥ (Be *ᵥ ((eigU hT.1)ᵀ i)))) ^ 2) =
      ∑ k : Fin d, ∑ j : Fin d, ((Ah - Bh * U) k j) ^ 2 := by
  let E := eigU hT.1
  have hE_mul_tr : E * Eᵀ = 1 := eigU_mul_transpose hT.1
  have hterm : ∀ i : Fin d,
      (Real.sqrt ((Eᵀ i) ⬝ᵥ (Ae *ᵥ (Eᵀ i))) -
        Real.sqrt ((Eᵀ i) ⬝ᵥ (Be *ᵥ (Eᵀ i)))) ^ 2 =
      (Eᵀ i) ⬝ᵥ (Ae *ᵥ (Eᵀ i)) + (Eᵀ i) ⬝ᵥ (Be *ᵥ (Eᵀ i)) -
        2 * ((Eᵀ i) ⬝ᵥ ((Ae * T) *ᵥ (Eᵀ i))) := by
    intro i
    have heig : T *ᵥ (Eᵀ i) = (hT.1.eigenvalues i) • (Eᵀ i) := by
      simpa [E, eigU] using hT.1.mulVec_eigenvectorBasis i
    have hτ_nn : 0 ≤ hT.1.eigenvalues i := hT.eigenvalues_nonneg i
    have ha_nn : 0 ≤ (Eᵀ i) ⬝ᵥ (Ae *ᵥ (Eᵀ i)) := by
      rw [← hAh_sq, ← mulVec_mulVec, dotProduct_mulVec, vecMul_eq_transpose_mulVec, hAh_symm]
      simp only [dotProduct]
      exact Finset.sum_nonneg fun k _ => mul_self_nonneg _
    have hb_eq : (Eᵀ i) ⬝ᵥ (Be *ᵥ (Eᵀ i)) =
        (hT.1.eigenvalues i) ^ 2 * ((Eᵀ i) ⬝ᵥ (Ae *ᵥ (Eᵀ i))) := by
      have hstep : Be *ᵥ (Eᵀ i) = T *ᵥ (Ae *ᵥ (T *ᵥ (Eᵀ i))) := by
        rw [← hTAT, mulVec_mulVec, mulVec_mulVec]
      rw [hstep, dotProduct_mulVec, vecMul_eq_transpose_mulVec, hT.transpose_eq, heig,
        mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
      ring
    have hAT_eq : (Eᵀ i) ⬝ᵥ ((Ae * T) *ᵥ (Eᵀ i)) =
        (hT.1.eigenvalues i) * ((Eᵀ i) ⬝ᵥ (Ae *ᵥ (Eᵀ i))) := by
      rw [← mulVec_mulVec, heig, mulVec_smul, dotProduct_smul, smul_eq_mul]
    rw [hb_eq, hAT_eq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hτ_nn]
    have hs2 : (Real.sqrt ((Eᵀ i) ⬝ᵥ (Ae *ᵥ (Eᵀ i)))) ^ 2 = (Eᵀ i) ⬝ᵥ (Ae *ᵥ (Eᵀ i)) :=
      Real.sq_sqrt ha_nn
    nlinarith [hs2]
  change (∑ i : Fin d, (Real.sqrt ((Eᵀ i) ⬝ᵥ (Ae *ᵥ (Eᵀ i))) -
      Real.sqrt ((Eᵀ i) ⬝ᵥ (Be *ᵥ (Eᵀ i)))) ^ 2) = _
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    trace_orth_quad_sum E _ hE_mul_tr, trace_orth_quad_sum E _ hE_mul_tr,
    trace_orth_quad_sum E _ hE_mul_tr, frobenius_sq_eq_trace]
  have hAT_trace : (Ae * T).trace = Ph.trace := by
    rw [← hAh_sq, hT_def]
    calc ((Ah * Ah) * (Ahi * Ph * Ahi)).trace
        = (Ah * (Ah * Ahi) * Ph * Ahi).trace := by simp only [Matrix.mul_assoc]
      _ = ((Ah * Ph) * Ahi).trace := by rw [hAh_inv, Matrix.mul_one]
      _ = (Ahi * (Ah * Ph)).trace := Matrix.trace_mul_comm _ _
      _ = ((Ahi * Ah) * Ph).trace := by rw [Matrix.mul_assoc]
      _ = Ph.trace := by rw [hAhi_inv, Matrix.one_mul]
  have hfrob : ((Ah - Bh * U) * (Ah - Bh * U)ᵀ).trace =
      Ae.trace + Be.trace - 2 * Ph.trace := by
    rw [transpose_sub, transpose_mul, hAh_symm, hBh_symm, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub]
    have hBUU : Bh * U * (Uᵀ * Bh) = Be := by
      calc Bh * U * (Uᵀ * Bh) = Bh * (U * Uᵀ) * Bh := by simp only [Matrix.mul_assoc]
        _ = Bh * Bh := by rw [hU_mul_tr, Matrix.mul_one]
        _ = Be := hBh_sq
    have htr1 : (Bh * U * Ah).trace = Ph.trace := by
      rw [Matrix.trace_mul_comm (Bh * U) Ah, ← Matrix.mul_assoc]
      exact congr_arg Matrix.trace hMU
    have htr2 : (Ah * (Uᵀ * Bh)).trace = Ph.trace := by
      have ht : (Ah * (Uᵀ * Bh))ᵀ = Bh * U * Ah := by
        rw [transpose_mul, transpose_mul, transpose_transpose, hAh_symm, hBh_symm, Matrix.mul_assoc]
      rw [← Matrix.trace_transpose (Ah * (Uᵀ * Bh)), ht, htr1]
    rw [hAh_sq, hBUU, htr1, htr2]
    ring
  rw [hAT_trace, hfrob]

set_option maxHeartbeats 800000 in
private lemma brenier_step_eps {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℝ}
    (hA : IsSymmPSD A) (hB : IsSymmPSD B) {ε : ℝ} (hε : 0 < ε) :
    ∃ E U : Matrix (Fin d) (Fin d) ℝ,
      (Eᵀ * E = 1 ∧ E * Eᵀ = 1) ∧ (Uᵀ * U = 1 ∧ U * Uᵀ = 1) ∧
      (∑ i : Fin d, (Real.sqrt ((Eᵀ i) ⬝ᵥ ((A + ε • 1) *ᵥ (Eᵀ i))) -
          Real.sqrt ((Eᵀ i) ⬝ᵥ ((B + ε • 1) *ᵥ (Eᵀ i)))) ^ 2) =
        ∑ k : Fin d, ∑ j : Fin d, ((sqrtEps hA ε - sqrtEps hB ε * U) k j) ^ 2 := by
  let Ah := sqrtEps hA ε
  let Ahi := invSqrtEps hA ε
  let Bh := sqrtEps hB ε
  let Bhi := invSqrtEps hB ε
  have hAh_symm : Ahᵀ = Ah := sqrtEps_symm hA ε
  have hAhi_symm : Ahiᵀ = Ahi := invSqrtEps_symm hA ε
  have hBh_symm : Bhᵀ = Bh := sqrtEps_symm hB ε
  have hBhi_symm : Bhiᵀ = Bhi := invSqrtEps_symm hB ε
  have hAh_inv : Ah * Ahi = 1 := sqrtEps_mul_inv hA hε
  have hAhi_inv : Ahi * Ah = 1 := inv_mul_sqrtEps hA hε
  have hBh_inv : Bh * Bhi = 1 := sqrtEps_mul_inv hB hε
  have hBhi_inv : Bhi * Bh = 1 := inv_mul_sqrtEps hB hε
  have hAh_sq : Ah * Ah = A + ε • 1 := sqrtEps_mul_self hA hε
  have hBh_sq : Bh * Bh = B + ε • 1 := sqrtEps_mul_self hB hε
  let M := Ah * Bh
  let Minv := Bhi * Ahi
  have hM_inv : M * Minv = 1 := by
    calc (Ah * Bh) * (Bhi * Ahi) = Ah * (Bh * Bhi) * Ahi := by simp only [Matrix.mul_assoc]
      _ = Ah * Ahi := by rw [hBh_inv, Matrix.mul_one]
      _ = 1 := hAh_inv
  have hMinv_M : Minv * M = 1 := by
    calc (Bhi * Ahi) * (Ah * Bh) = Bhi * (Ahi * Ah) * Bh := by simp only [Matrix.mul_assoc]
      _ = Bhi * Bh := by rw [hAhi_inv, Matrix.mul_one]
      _ = 1 := hBhi_inv
  have hMinv_tr : Mᵀ * Minvᵀ = 1 := by
    have ht := congr_arg Matrix.transpose hMinv_M
    rwa [transpose_mul, transpose_one] at ht
  let P2 := M * Mᵀ
  have hP2 : IsSymmPSD P2 := by
    refine ⟨?_, fun x => ?_⟩
    · change (M * Mᵀ)ᵀ = M * Mᵀ
      rw [transpose_mul, transpose_transpose]
    · rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_eq_transpose_mulVec]
      simp only [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hP2_pos : ∀ i : Fin d, 0 < hP2.1.eigenvalues i := by
    intro i
    rw [hP2.1.eigenvalues_eq i]
    let v : Fin d → ℝ := ⇑(hP2.1.eigenvectorBasis i)
    have hv_norm : v ⬝ᵥ v = 1 := by
      have hn1 : ‖hP2.1.eigenvectorBasis i‖ = 1 := hP2.1.eigenvectorBasis.orthonormal.1 i
      have hsq : ‖hP2.1.eigenvectorBasis i‖ ^ 2 = 1 := by rw [hn1, one_pow]
      rw [EuclideanSpace.norm_sq_eq] at hsq
      simpa [v, dotProduct, Real.norm_eq_abs, sq_abs, sq] using hsq
    have hw_ne : Mᵀ *ᵥ v ≠ 0 := by
      intro hw
      have hrec : Minvᵀ *ᵥ (Mᵀ *ᵥ v) = v := by
        rw [mulVec_mulVec]
        have htr : Minvᵀ * Mᵀ = 1 := by
          have ht := congr_arg Matrix.transpose hM_inv
          rwa [transpose_mul, transpose_one] at ht
        rw [htr, one_mulVec]
      rw [hw, mulVec_zero] at hrec
      rw [← hrec, zero_dotProduct] at hv_norm
      exact zero_ne_one hv_norm
    have hdot : RCLike.re (star v ⬝ᵥ (P2 *ᵥ v)) = (Mᵀ *ᵥ v) ⬝ᵥ (Mᵀ *ᵥ v) := by
      change RCLike.re (star v ⬝ᵥ ((M * Mᵀ) *ᵥ v)) = _
      rw [← mulVec_mulVec, dotProduct_mulVec]
      simp [vecMul_eq_transpose_mulVec]
    rw [hdot]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hw_ne
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
      ⟨k, Finset.mem_univ k, mul_self_pos.mpr hk⟩
  let Ph := sqrtM hP2
  let Phi := eigU hP2.1 * Matrix.diagonal (fun i => (Real.sqrt (hP2.1.eigenvalues i))⁻¹) * (eigU hP2.1)ᵀ
  have hPh_Phi : Ph * Phi = 1 := by
    dsimp only [Ph, sqrtM, Phi]
    rw [conj_diag_mul]
    have hd : (fun i => Real.sqrt (hP2.1.eigenvalues i) *
        (Real.sqrt (hP2.1.eigenvalues i))⁻¹) = fun _ => 1 :=
      funext fun i => mul_inv_cancel₀ (Real.sqrt_pos.mpr (hP2_pos i)).ne'
    rw [hd, diagonal_one, Matrix.mul_one, eigU_mul_transpose]
  obtain ⟨hU_tr_mul, hU_mul_tr, hMU⟩ := polar_orth_algebra M Minv Ph Phi
    (sqrtM_symm hP2) (symm_conj_diag _ _) (sqrtM_mul_self hP2) hPh_Phi hM_inv hMinv_M hMinv_tr
  obtain ⟨hT, hTAT⟩ := brenier_TAT_algebra (A + ε • 1) (B + ε • 1) Ah Ahi Bh Ph
    hAh_symm hAhi_symm hBh_symm hAh_sq hBh_sq hAh_inv hAhi_inv
    (sqrtM_symm hP2) (sqrtM_psd hP2) (sqrtM_mul_self hP2)
  refine ⟨eigU hT.1, Minv * Ph, ⟨eigU_transpose_mul hT.1, eigU_mul_transpose hT.1⟩,
    ⟨hU_tr_mul, hU_mul_tr⟩, ?_⟩
  exact brenier_quad_identity (A + ε • 1) (B + ε • 1) Ah Ahi Bh (Minv * Ph) Ph (Ahi * Ph * Ahi) hT
    hAh_symm hBh_symm hAh_sq hBh_sq hAh_inv hAhi_inv hU_mul_tr hMU rfl hTAT

private def OrthSet (d : ℕ) : Set (RawMat d) :=
  {U : RawMat d | (ofRaw U)ᵀ * ofRaw U = 1 ∧ ofRaw U * (ofRaw U)ᵀ = 1}

private lemma mem_OrthSet_toRaw {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}
    (h : Mᵀ * M = 1 ∧ M * Mᵀ = 1) : toRaw M ∈ OrthSet d := by
  change (ofRaw (toRaw M))ᵀ * ofRaw (toRaw M) = 1 ∧ ofRaw (toRaw M) * (ofRaw (toRaw M))ᵀ = 1
  rw [ofRaw_toRaw]
  exact h

private lemma isCompact_orthRaw (d : ℕ) : IsCompact (OrthSet d) := by
  let box : Set (RawMat d) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (-1 : ℝ) 1
  have hbox : IsCompact box :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hc1 : Continuous (fun U : RawMat d => toRaw ((ofRaw U)ᵀ * ofRaw U)) := by
    rw [continuous_pi_iff]; intro i; rw [continuous_pi_iff]; intro j
    simp only [toRaw, ofRaw, Matrix.mul_apply, transpose_apply, of_apply]
    fun_prop
  have hc2 : Continuous (fun U : RawMat d => toRaw (ofRaw U * (ofRaw U)ᵀ)) := by
    rw [continuous_pi_iff]; intro i; rw [continuous_pi_iff]; intro j
    simp only [toRaw, ofRaw, Matrix.mul_apply, transpose_apply, of_apply]
    fun_prop
  have hset_eq : OrthSet d =
      {U : RawMat d | toRaw ((ofRaw U)ᵀ * ofRaw U) = toRaw 1 ∧
        toRaw (ofRaw U * (ofRaw U)ᵀ) = toRaw 1} := by
    ext U
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨congr_arg toRaw h1, congr_arg toRaw h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · ext i j; exact congr_fun (congr_fun h1 i) j
      · ext i j; exact congr_fun (congr_fun h2 i) j
  rw [hset_eq]
  have hclosed : IsClosed {U : RawMat d | toRaw ((ofRaw U)ᵀ * ofRaw U) = toRaw 1 ∧
      toRaw (ofRaw U * (ofRaw U)ᵀ) = toRaw 1} :=
    (isClosed_eq hc1 continuous_const).inter (isClosed_eq hc2 continuous_const)
  refine IsCompact.of_isClosed_subset hbox hclosed ?_
  intro U hU i _ j _
  have hdiag : toRaw ((ofRaw U)ᵀ * ofRaw U) j j = toRaw (1 : Matrix (Fin d) (Fin d) ℝ) j j :=
    congr_fun (congr_fun hU.1 j) j
  simp only [toRaw, ofRaw, Matrix.mul_apply, transpose_apply, of_apply, Matrix.one_apply_eq] at hdiag
  have hle : (U i j) ^ 2 ≤ 1 := by
    rw [← hdiag, sq]
    exact Finset.single_le_sum (fun k _ => mul_self_nonneg (U k j)) (Finset.mem_univ i)
  have habs : |U i j| ≤ 1 := by nlinarith [hle, sq_abs (U i j), abs_nonneg (U i j)]
  exact abs_le.mp habs

private noncomputable def lhsRaw {d : ℕ} (E A B : RawMat d) : ℝ :=
  ∑ i : Fin d, (Real.sqrt (∑ r : Fin d, E r i * ∑ s : Fin d, A r s * E s i) -
    Real.sqrt (∑ r : Fin d, E r i * ∑ s : Fin d, B r s * E s i)) ^ 2

private noncomputable def rhsRaw {d : ℕ} (Ah Bh U : RawMat d) : ℝ :=
  ∑ m : Fin d, ∑ j : Fin d, (Ah m j - ∑ l : Fin d, Bh m l * U l j) ^ 2

private lemma lhsRaw_toRaw {d : ℕ} (E A B : Matrix (Fin d) (Fin d) ℝ) :
    lhsRaw (toRaw E) (toRaw A) (toRaw B) =
      ∑ i : Fin d, (Real.sqrt ((Eᵀ i) ⬝ᵥ (A *ᵥ (Eᵀ i))) -
        Real.sqrt ((Eᵀ i) ⬝ᵥ (B *ᵥ (Eᵀ i)))) ^ 2 := by
  simp only [lhsRaw, toRaw, dotProduct, mulVec, transpose_apply]

private lemma rhsRaw_toRaw {d : ℕ} (Ah Bh U : Matrix (Fin d) (Fin d) ℝ) :
    rhsRaw (toRaw Ah) (toRaw Bh) (toRaw U) =
      ∑ k : Fin d, ∑ j : Fin d, ((Ah - Bh * U) k j) ^ 2 := by
  simp only [rhsRaw, toRaw, Matrix.sub_apply, Matrix.mul_apply]

private lemma tendsto_add_smul_one_entry {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (i j : Fin d) :
    Tendsto (fun k => toRaw (M + δ k • (1 : Matrix (Fin d) (Fin d) ℝ)) i j)
      atTop (𝓝 (toRaw M i j)) := by
  simp only [toRaw, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have h : Tendsto (fun k => M i j + δ k * (1 : Matrix (Fin d) (Fin d) ℝ) i j)
      atTop (𝓝 (M i j + 0 * (1 : Matrix (Fin d) (Fin d) ℝ) i j)) :=
    (tendsto_const_nhds (x := M i j)).add (hδ.mul_const ((1 : Matrix (Fin d) (Fin d) ℝ) i j))
  rwa [zero_mul, add_zero] at h

private lemma tendsto_lhsRaw {d : ℕ} {e a b : ℕ → RawMat d} {er ar br : RawMat d}
    (he : ∀ i j, Tendsto (fun k => e k i j) atTop (𝓝 (er i j)))
    (ha : ∀ i j, Tendsto (fun k => a k i j) atTop (𝓝 (ar i j)))
    (hb : ∀ i j, Tendsto (fun k => b k i j) atTop (𝓝 (br i j))) :
    Tendsto (fun k => lhsRaw (e k) (a k) (b k)) atTop (𝓝 (lhsRaw er ar br)) := by
  unfold lhsRaw
  refine tendsto_finsetSum _ fun i _ => ?_
  refine (Tendsto.sub ?_ ?_).pow 2
  · refine (Real.continuous_sqrt.tendsto _).comp (tendsto_finsetSum _ fun r _ => ?_)
    exact (he r i).mul (tendsto_finsetSum _ fun s _ => (ha r s).mul (he s i))
  · refine (Real.continuous_sqrt.tendsto _).comp (tendsto_finsetSum _ fun r _ => ?_)
    exact (he r i).mul (tendsto_finsetSum _ fun s _ => (hb r s).mul (he s i))

private lemma tendsto_rhsRaw {d : ℕ} {ah bh u : ℕ → RawMat d} {ahr bhr ur : RawMat d}
    (hah : ∀ i j, Tendsto (fun k => ah k i j) atTop (𝓝 (ahr i j)))
    (hbh : ∀ i j, Tendsto (fun k => bh k i j) atTop (𝓝 (bhr i j)))
    (hu : ∀ i j, Tendsto (fun k => u k i j) atTop (𝓝 (ur i j))) :
    Tendsto (fun k => rhsRaw (ah k) (bh k) (u k)) atTop (𝓝 (rhsRaw ahr bhr ur)) := by
  unfold rhsRaw
  refine tendsto_finsetSum _ fun m _ => tendsto_finsetSum _ fun j _ => ?_
  refine ((hah m j).sub (tendsto_finsetSum _ fun l _ => (hbh m l).mul (hu l j))).pow 2

private lemma subseq_orthRaw_pair {d : ℕ} {e u : ℕ → RawMat d}
    (he : ∀ n, e n ∈ OrthSet d) (hu : ∀ n, u n ∈ OrthSet d) :
    ∃ er ur : RawMat d, er ∈ OrthSet d ∧ ur ∈ OrthSet d ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ i j, Tendsto (fun k => e (φ k) i j) atTop (𝓝 (er i j))) ∧
        (∀ i j, Tendsto (fun k => u (φ k) i j) atTop (𝓝 (ur i j))) := by
  have hmem : ∀ n : ℕ, (e n, u n) ∈ OrthSet d ×ˢ OrthSet d := fun n => ⟨he n, hu n⟩
  obtain ⟨⟨er, ur⟩, ⟨her, hur⟩, φ, hφ, ht⟩ :=
    ((isCompact_orthRaw d).prod (isCompact_orthRaw d)).tendsto_subseq hmem
  rw [Prod.tendsto_iff] at ht
  have ht1 : Tendsto (fun k => e (φ k)) atTop (𝓝 er) := ht.1
  have ht2 : Tendsto (fun k => u (φ k)) atTop (𝓝 ur) := ht.2
  refine ⟨er, ur, her, hur, φ, hφ, ?_, ?_⟩
  · intro i j; exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp ht1 i) j
  · intro i j; exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp ht2 i) j

private lemma tendsto_sqrtEps_entry {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : IsSymmPSD S)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (i j : Fin d) :
    Tendsto (fun k => toRaw (sqrtEps hS (1 / ((φ k : ℝ) + 1))) i j)
      atTop (𝓝 (toRaw (sqrtM hS) i j)) := by
  have h : Tendsto (fun k => toRaw (sqrtEps hS (1 / ((φ k : ℝ) + 1))))
      atTop (𝓝 (toRaw (sqrtM hS))) :=
    (tendsto_sqrtEps hS).comp hφ.tendsto_atTop
  exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h i) j

private lemma brenier_limit {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℝ}
    (hA : IsSymmPSD A) (hB : IsSymmPSD B) :
    ∃ E U : Matrix (Fin d) (Fin d) ℝ,
      (Eᵀ * E = 1 ∧ E * Eᵀ = 1) ∧ (Uᵀ * U = 1 ∧ U * Uᵀ = 1) ∧
      (∑ i : Fin d, (Real.sqrt ((Eᵀ i) ⬝ᵥ (A *ᵥ (Eᵀ i))) -
          Real.sqrt ((Eᵀ i) ⬝ᵥ (B *ᵥ (Eᵀ i)))) ^ 2) =
        ∑ k : Fin d, ∑ j : Fin d, ((sqrtM hA - sqrtM hB * U) k j) ^ 2 := by
  have hε : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) :=
    fun n => one_div_pos.mpr (Nat.cast_add_one_pos n)
  choose Eseq Useq hEseq hUseq heq using fun n => brenier_step_eps hA hB (hε n)
  obtain ⟨Er, Ur, hE, hU, φ, hφ_mono, hEtend, hUtend⟩ :=
    subseq_orthRaw_pair (fun n => mem_OrthSet_toRaw (hEseq n))
      (fun n => mem_OrthSet_toRaw (hUseq n))
  refine ⟨ofRaw Er, ofRaw Ur, hE, hU, ?_⟩
  have hε0 : Tendsto (fun k => (1 : ℝ) / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ_mono.tendsto_atTop
  have hlhs_lim := tendsto_lhsRaw hEtend
    (tendsto_add_smul_one_entry A hε0) (tendsto_add_smul_one_entry B hε0)
  have hrhs_lim := tendsto_rhsRaw
    (tendsto_sqrtEps_entry hA hφ_mono) (tendsto_sqrtEps_entry hB hφ_mono) hUtend
  have hlhs_eq_rhs : (fun k => lhsRaw (toRaw (Eseq (φ k)))
      (toRaw (A + (1 / ((φ k : ℝ) + 1)) • (1 : Matrix (Fin d) (Fin d) ℝ)))
      (toRaw (B + (1 / ((φ k : ℝ) + 1)) • (1 : Matrix (Fin d) (Fin d) ℝ)))) =
      (fun k => rhsRaw (toRaw (sqrtEps hA (1 / ((φ k : ℝ) + 1))))
        (toRaw (sqrtEps hB (1 / ((φ k : ℝ) + 1)))) (toRaw (Useq (φ k)))) := by
    funext k
    rw [lhsRaw_toRaw, rhsRaw_toRaw]
    exact heq (φ k)
  rw [hlhs_eq_rhs] at hlhs_lim
  rw [← lhsRaw_toRaw, ← rhsRaw_toRaw, toRaw_ofRaw, toRaw_ofRaw]
  exact tendsto_nhds_unique hlhs_lim hrhs_lim

/-! ## Section 3: Covariance Matrix & Pushforward Representation of Centered Gaussians -/

private noncomputable def covMat {d : ℕ} (μ : Measure (Ed d)) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => covarianceBilin μ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

private lemma euclidean_eq_sum_single {d : ℕ} (x : Ed d) :
    x = ∑ i : Fin d, (x.ofLp i) • EuclideanSpace.single i (1 : ℝ) := by
  ext k
  simp [PiLp.ofLp_single, Pi.single_apply]

private lemma covarianceBilin_eq_covMat {d : ℕ} (μ : Measure (Ed d)) (x y : Ed d) :
    covarianceBilin μ x y = x.ofLp ⬝ᵥ (covMat μ *ᵥ y.ofLp) := by
  conv_lhs => rw [euclidean_eq_sum_single x, euclidean_eq_sum_single y]
  simp only [map_sum, map_smul, FunLike.coe_sum, FunLike.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct, mulVec, covMat, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma covMat_psd {d : ℕ} (μ : Measure (Ed d)) : IsSymmPSD (covMat μ) := by
  refine ⟨?_, fun v => ?_⟩
  · ext i j
    simp [covMat, covarianceBilin_comm]
  · have h := covarianceBilin_self_nonneg (μ := μ) (toLp 2 v)
    rwa [covarianceBilin_eq_covMat] at h

private lemma centered_gaussian_eq_map_stdGaussian {d : ℕ} (μ : Measure (Ed d)) [IsGaussian μ]
    (hμ0 : ∫ x, x ∂μ = 0) (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : M * Mᵀ = covMat μ) :
    μ = (stdGaussian (Ed d)).map (toEuclideanCLM (𝕜 := ℝ) M) := by
  let L : Ed d →L[ℝ] Ed d := toEuclideanCLM (𝕜 := ℝ) M
  apply IsGaussian.ext
  · change ∫ x, x ∂μ = ∫ x, x ∂((stdGaussian (Ed d)).map L)
    rw [hμ0, L.integral_id_map IsGaussian.integrable_id, integral_id_stdGaussian, map_zero]
  · ext x y
    rw [covarianceBilin_map IsGaussian.memLp_two_id L x y, covarianceBilin_stdGaussian,
      innerSL_apply_apply]
    have hadj_apply : ∀ u : Ed d, L.adjoint u = toEuclideanCLM (𝕜 := ℝ) Mᵀ u := by
      intro u
      apply ext_inner_left ℝ
      intro w
      rw [ContinuousLinearMap.adjoint_inner_right]
      simp only [L, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, ofLp_toEuclideanCLM]
      rw [dotProduct_mulVec, vecMul_eq_transpose_mulVec, dotProduct_comm]
    rw [hadj_apply x, hadj_apply y]
    have hinner : ⟪toEuclideanCLM (𝕜 := ℝ) Mᵀ x, toEuclideanCLM (𝕜 := ℝ) Mᵀ y⟫ =
        x.ofLp ⬝ᵥ ((M * Mᵀ) *ᵥ y.ofLp) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [star_trivial, ofLp_toEuclideanCLM]
      rw [dotProduct_mulVec, vecMul_eq_transpose_mulVec, transpose_transpose, mulVec_mulVec,
        dotProduct_comm]
    rw [hinner, hM, ← covarianceBilin_eq_covMat]

private lemma integral_norm_sq_map_stdGaussian {d : ℕ} (D : Matrix (Fin d) (Fin d) ℝ) :
    ∫ z : Ed d, ‖toEuclideanCLM (𝕜 := ℝ) D z‖ ^ 2 ∂(stdGaussian (Ed d)) =
      ∑ k : Fin d, ∑ j : Fin d, (D k j) ^ 2 := by
  rw [← map_pi_eq_stdGaussian (ι := Fin d),
    integral_map (Measurable.aemeasurable (by fun_prop))
      (Continuous.aestronglyMeasurable (by fun_prop))]
  have hnorm : ∀ x : Fin d → ℝ,
      ‖toEuclideanCLM (𝕜 := ℝ) D (toLp 2 x)‖ ^ 2 = ∑ k : Fin d, (∑ j : Fin d, D k j * x j) ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Real.norm_eq_abs, sq_abs, mulVec, dotProduct]
  simp_rw [hnorm]
  let γ := Measure.pi (fun _ : Fin d => gaussianReal 0 1)
  have hint_x2 : ∀ j : Fin d, Integrable (fun x : Fin d → ℝ => (x j) ^ 2) γ := by
    intro j
    have h1 : Integrable (fun t : ℝ => t ^ 2) (gaussianReal 0 1) :=
      (memLp_id_gaussianReal 2).integrable_sq
    exact (MeasureTheory.measurePreserving_eval
      (fun _ : Fin d => gaussianReal 0 1) j).integrable_comp_of_integrable h1
  have hint_prod : ∀ j l : Fin d, Integrable (fun x : Fin d → ℝ => x j * x l) γ := by
    intro j l
    refine Integrable.mono' ((hint_x2 j).add (hint_x2 l))
      (Measurable.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs]
    nlinarith [sq_nonneg (|x j| - |x l|), sq_abs (x j), sq_abs (x l), abs_mul (x j) (x l)]
  have hint_row : ∀ k : Fin d, Integrable (fun x : Fin d → ℝ => (∑ j : Fin d, D k j * x j) ^ 2) γ := by
    intro k
    have hexp : (fun x : Fin d → ℝ => (∑ j : Fin d, D k j * x j) ^ 2) =
        fun x => ∑ j : Fin d, ∑ l : Fin d, (D k j * D k l) * (x j * x l) := by
      funext x
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => by ring
    rw [hexp]
    exact integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun l _ => (hint_prod j l).const_mul _
  rw [integral_finsetSum _ fun k _ => hint_row k]
  refine Finset.sum_congr rfl fun k _ => ?_
  let fk : (Fin d → ℝ) → ℝ := fun x => ∑ j : Fin d, D k j * x j
  have hmean0 : ∫ x, fk x ∂γ = 0 := by
    dsimp only [fk]
    rw [integral_finsetSum _ fun j _ =>
      (integrable_eval (μ := fun _ : Fin d => gaussianReal 0 1) IsGaussian.integrable_id (i := j)).const_mul _]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul, integral_eval]
    simp
  have hvar_eq : Var[fk; γ] = ∫ x, (fk x) ^ 2 ∂γ := by
    rw [variance_eq_integral (Measurable.aemeasurable (by fun_prop)), hmean0]
    simp
  rw [← hvar_eq]
  have hfk_sum : fk = ∑ j : Fin d, fun x : Fin d → ℝ => D k j * x j := by
    funext x; simp [fk]
  rw [hfk_sum, variance_sum_pi]
  · refine Finset.sum_congr rfl fun j _ => ?_
    change Var[fun t : ℝ => D k j * id t; gaussianReal 0 1] = (D k j) ^ 2
    rw [variance_const_mul, variance_id_gaussianReal]
    simp
  · intro j
    exact (memLp_id_gaussianReal 2).const_mul _

/-! ## Section 4 & 5: Main Comparison Inequality -/

private lemma parseval_orth_rows {d : ℕ} (E : Matrix (Fin d) (Fin d) ℝ) (hE : E * Eᵀ = 1)
    (v : Ed d) :
    (∑ i : Fin d, ⟪toLp 2 (Eᵀ i), v⟫ ^ 2) = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  have hinner : ∀ i : Fin d, ⟪toLp 2 (Eᵀ i), v⟫ = (Eᵀ *ᵥ v.ofLp) i := by
    intro i
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [mulVec, dotProduct, mul_comm]
  simp_rw [hinner, Real.norm_eq_abs, sq_abs, sq]
  change (Eᵀ *ᵥ v.ofLp) ⬝ᵥ (Eᵀ *ᵥ v.ofLp) = v.ofLp ⬝ᵥ v.ofLp
  rw [dotProduct_mulVec, vecMul_eq_transpose_mulVec, transpose_transpose, mulVec_mulVec, hE,
    one_mulVec]

private lemma integral_abs_inner_gaussian {d : ℕ} (μ : Measure (Ed d)) [IsGaussian μ]
    (hμ0 : ∫ x, x ∂μ = 0) (u : Ed d) :
    ∫ x : Ed d, |⟪u, x⟫| ∂μ =
      Real.sqrt (2 / Real.pi) * Real.sqrt (u.ofLp ⬝ᵥ (covMat μ *ᵥ u.ofLp)) := by
  let L : StrongDual ℝ (Ed d) := InnerProductSpace.toDual ℝ (Ed d) u
  have hmap : μ.map L = gaussianReal (μ[L]) (Var[L; μ]).toNNReal :=
    IsGaussian.map_eq_gaussianReal L
  have hL0 : μ[L] = 0 := by
    rw [IsGaussian.integral_dual L, hμ0, map_zero]
  have hvar : Var[L; μ] = u.ofLp ⬝ᵥ (covMat μ *ᵥ u.ofLp) := by
    have hcov := covarianceBilin_self (μ := μ) IsGaussian.memLp_two_id u
    change Var[fun x => ⟪u, x⟫; μ] = _
    rw [← hcov, covarianceBilin_eq_covMat]
  have hvar_nn : 0 ≤ u.ofLp ⬝ᵥ (covMat μ *ᵥ u.ofLp) := (covMat_psd μ).2 u.ofLp
  have hint_eq : ∫ x : Ed d, |⟪u, x⟫| ∂μ = ∫ t : ℝ, |t| ∂(μ.map L) := by
    rw [integral_map L.continuous.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
    rfl
  rw [hint_eq, hmap, hL0, integral_abs_gaussianReal_zero, hvar, Real.coe_toNNReal _ hvar_nn]

theorem main_proof : type_of% @OMA.S_mo_465929.main := by
  refine ⟨Real.sqrt (Real.pi / 2), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro d μ ν hμ hν hμ0 hν0
  have : IsGaussian μ := hμ
  have : IsGaussian ν := hν
  set A := covMat μ
  set B := covMat ν
  have hA : IsSymmPSD A := covMat_psd μ
  have hB : IsSymmPSD B := covMat_psd ν
  obtain ⟨E, U, ⟨_, hEEt⟩, ⟨_, hUUt⟩, hbrenier⟩ := brenier_limit hA hB
  set D := sqrtM hA - sqrtM hB * U
  set S2 := ∑ k : Fin d, ∑ j : Fin d, (D k j) ^ 2
  have hS2_nn : 0 ≤ S2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hprod_coupl : OMA.S_mo_465929.IsCoupling (μ.prod ν) μ ν := by
    refine ⟨?_, ?_⟩ <;> simp
  -- Step 1: Upper bound on transportCost 2 μ ν via pushforward coupling of stdGaussian
  have hcost2_le : OMA.S_mo_465929.transportCost 2 μ ν ≤ S2 := by
    let LA : Ed d →L[ℝ] Ed d := toEuclideanCLM (𝕜 := ℝ) (sqrtM hA)
    let LB : Ed d →L[ℝ] Ed d := toEuclideanCLM (𝕜 := ℝ) (sqrtM hB * U)
    have hμ_eq : μ = (stdGaussian (Ed d)).map LA := by
      refine centered_gaussian_eq_map_stdGaussian μ hμ0 (sqrtM hA) ?_
      rw [sqrtM_symm, sqrtM_mul_self]
    have hν_eq : ν = (stdGaussian (Ed d)).map LB := by
      refine centered_gaussian_eq_map_stdGaussian ν hν0 (sqrtM hB * U) ?_
      calc (sqrtM hB * U) * (sqrtM hB * U)ᵀ
          = sqrtM hB * (U * Uᵀ) * (sqrtM hB)ᵀ := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
        _ = sqrtM hB * sqrtM hB := by rw [hUUt, Matrix.mul_one, sqrtM_symm]
        _ = B := sqrtM_mul_self hB
    let Φ : Ed d → Ed d × Ed d := fun z => (LA z, LB z)
    have hΦ_meas : Measurable Φ := LA.continuous.measurable.prodMk LB.continuous.measurable
    let γ₀ : Measure (Ed d × Ed d) := (stdGaussian (Ed d)).map Φ
    have hcoupl : OMA.S_mo_465929.IsCoupling γ₀ μ ν := by
      refine ⟨?_, ?_⟩
      · rw [Measure.map_map measurable_fst hΦ_meas]
        exact hμ_eq.symm
      · rw [Measure.map_map measurable_snd hΦ_meas]
        exact hν_eq.symm
    have hint_γ₀ : ∫ z, dist z.1 z.2 ^ 2 ∂γ₀ = S2 := by
      rw [integral_map hΦ_meas.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
      have hdist : (fun z : Ed d => dist (LA z) (LB z) ^ 2) =
          fun z => ‖toEuclideanCLM (𝕜 := ℝ) D z‖ ^ 2 := by
        funext z
        rw [dist_eq_norm, map_sub]
        rfl
      rw [hdist, integral_norm_sq_map_stdGaussian D]
    have hbdd2 : BddBelow {r : ℝ | ∃ γ : Measure (Ed d × Ed d),
        OMA.S_mo_465929.IsCoupling γ μ ν ∧ r = ∫ z, dist z.1 z.2 ^ 2 ∂γ} := by
      refine ⟨0, ?_⟩
      rintro r ⟨γ, _, rfl⟩
      exact integral_nonneg fun _ => sq_nonneg _
    exact (csInf_le hbdd2 ⟨γ₀, hcoupl, rfl⟩).trans_eq hint_γ₀
  -- Step 2: Lower bound on transportCost 1 μ ν
  by_cases hS2_zero : S2 = 0
  · have hcost1_nn : 0 ≤ OMA.S_mo_465929.transportCost 1 μ ν := by
      have hne1 : {r : ℝ | ∃ γ : Measure (Ed d × Ed d),
          OMA.S_mo_465929.IsCoupling γ μ ν ∧ r = ∫ z, dist z.1 z.2 ^ 1 ∂γ}.Nonempty :=
        ⟨∫ z, dist z.1 z.2 ^ 1 ∂(μ.prod ν), μ.prod ν, hprod_coupl, rfl⟩
      refine le_csInf hne1 ?_
      rintro r ⟨γ, _, rfl⟩
      exact integral_nonneg fun _ => by positivity
    have hcost2_le0 : OMA.S_mo_465929.transportCost 2 μ ν ≤ 0 := hS2_zero ▸ hcost2_le
    rw [Real.sqrt_eq_zero_of_nonpos hcost2_le0]
    exact mul_nonneg (by positivity) hcost1_nn
  · have hS2_pos : 0 < S2 := lt_of_le_of_ne hS2_nn (Ne.symm hS2_zero)
    set Δ := Real.sqrt S2
    have hΔ_pos : 0 < Δ := Real.sqrt_pos.mpr hS2_pos
    let δ : Fin d → ℝ := fun i =>
      Real.sqrt ((Eᵀ i) ⬝ᵥ (A *ᵥ (Eᵀ i))) - Real.sqrt ((Eᵀ i) ⬝ᵥ (B *ᵥ (Eᵀ i)))
    have hδ_sq : ∑ i : Fin d, (δ i) ^ 2 = S2 := hbrenier
    let w : Fin d → ℝ := fun i => δ i / Δ
    have hw_sq : ∑ i : Fin d, (w i) ^ 2 = 1 := by
      simp only [w, div_pow, ← Finset.sum_div, hδ_sq]
      rw [Real.sq_sqrt hS2_pos.le, div_self hS2_pos.ne']
    let u : Fin d → Ed d := fun i => toLp 2 (Eᵀ i)
    let f : Ed d → ℝ := fun x => ∑ i : Fin d, w i * |⟪u i, x⟫|
    have hf_cont : Continuous f := by
      dsimp only [f]; fun_prop
    have hf_lip : ∀ x y : Ed d, f x - f y ≤ dist x y := by
      intro x y
      rw [dist_eq_norm, ← Finset.sum_sub_distrib]
      have hterm_le : ∑ i : Fin d, (w i * |⟪u i, x⟫| - w i * |⟪u i, y⟫|) ≤
          ∑ i : Fin d, |w i| * |⟪u i, x - y⟫| := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 : w i * |⟪u i, x⟫| - w i * |⟪u i, y⟫| ≤ |w i * (|⟪u i, x⟫| - |⟪u i, y⟫|)| := by
          rw [← mul_sub]; exact le_abs_self _
        rw [abs_mul] at h1
        have h2 : |(|⟪u i, x⟫| - |⟪u i, y⟫|)| ≤ |⟪u i, x - y⟫| := by
          rw [inner_sub_right]; exact abs_abs_sub_abs_le_abs_sub _ _
        exact h1.trans (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
      have hcs : (∑ i : Fin d, |w i| * |⟪u i, x - y⟫|) ^ 2 ≤ ‖x - y‖ ^ 2 := by
        calc (∑ i : Fin d, |w i| * |⟪u i, x - y⟫|) ^ 2
            ≤ (∑ i : Fin d, |w i| ^ 2) * (∑ i : Fin d, |⟪u i, x - y⟫| ^ 2) :=
              Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |w i|) (fun i => |⟪u i, x - y⟫|)
          _ = 1 * ‖x - y‖ ^ 2 := by
              simp_rw [sq_abs]
              rw [hw_sq, parseval_orth_rows E hEEt (x - y)]
          _ = ‖x - y‖ ^ 2 := one_mul _
      have hnn : 0 ≤ ‖x - y‖ := norm_nonneg _
      have habs := le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hnn hcs
      exact hterm_le.trans habs
    have hf_bound : ∀ x : Ed d, |f x| ≤ ‖x‖ := by
      intro x
      have hf0 : f 0 = 0 := by simp [f]
      have h1 : f x ≤ ‖x‖ := by simpa [hf0, dist_zero_right] using hf_lip x 0
      have h2 : -f x ≤ ‖x‖ := by simpa [hf0, dist_zero_left] using hf_lip 0 x
      exact abs_le.mpr ⟨by linarith, h1⟩
    have hf_diff : ∫ x, f x ∂μ - ∫ y, f y ∂ν = Real.sqrt (2 / Real.pi) * Δ := by
      have hint_term_μ : ∀ i : Fin d, Integrable (fun x : Ed d => w i * |⟪u i, x⟫|) μ := by
        intro i
        exact ((InnerProductSpace.toDual ℝ (Ed d) (u i)).integrable_comp
          IsGaussian.integrable_id).norm.const_mul _
      have hint_term_ν : ∀ i : Fin d, Integrable (fun y : Ed d => w i * |⟪u i, y⟫|) ν := by
        intro i
        exact ((InnerProductSpace.toDual ℝ (Ed d) (u i)).integrable_comp
          IsGaussian.integrable_id).norm.const_mul _
      dsimp only [f]
      rw [integral_finsetSum _ fun i _ => hint_term_μ i,
        integral_finsetSum _ fun i _ => hint_term_ν i, ← Finset.sum_sub_distrib]
      have hterm : ∀ i : Fin d,
          (∫ x, w i * |⟪u i, x⟫| ∂μ) - (∫ y, w i * |⟪u i, y⟫| ∂ν) =
            Real.sqrt (2 / Real.pi) * (w i * δ i) := by
        intro i
        rw [integral_const_mul, integral_const_mul,
          integral_abs_inner_gaussian μ hμ0 (u i),
          integral_abs_inner_gaussian ν hν0 (u i)]
        dsimp only [u, δ, A, B]
        ring
      simp_rw [hterm, ← Finset.mul_sum]
      congr 1
      have hΔ2 : Δ ^ 2 = S2 := Real.sq_sqrt hS2_pos.le
      simp only [w, div_mul_eq_mul_div, ← sq, ← Finset.sum_div, hδ_sq, ← hΔ2]
      have hne : Δ ≠ 0 := hΔ_pos.ne'
      field_simp [hne]
    have hne1 : {r : ℝ | ∃ γ : Measure (Ed d × Ed d),
        OMA.S_mo_465929.IsCoupling γ μ ν ∧ r = ∫ z, dist z.1 z.2 ^ 1 ∂γ}.Nonempty :=
      ⟨∫ z, dist z.1 z.2 ^ 1 ∂(μ.prod ν), μ.prod ν, hprod_coupl, rfl⟩
    have hcost1_ge : Real.sqrt (2 / Real.pi) * Δ ≤ OMA.S_mo_465929.transportCost 1 μ ν := by
      refine le_csInf hne1 ?_
      rintro r ⟨γ, ⟨hγ1, hγ2⟩, rfl⟩
      simp only [pow_one]
      have hint_n1 : Integrable (fun z : Ed d × Ed d => ‖z.1‖) γ := by
        have h : Integrable (norm ∘ Prod.fst) γ :=
          (integrable_map_measure aestronglyMeasurable_id.norm measurable_fst.aemeasurable).mp
            (hγ1.symm ▸ IsGaussian.integrable_id.norm)
        exact h
      have hint_n2 : Integrable (fun z : Ed d × Ed d => ‖z.2‖) γ := by
        have h : Integrable (norm ∘ Prod.snd) γ :=
          (integrable_map_measure aestronglyMeasurable_id.norm measurable_snd.aemeasurable).mp
            (hγ2.symm ▸ IsGaussian.integrable_id.norm)
        exact h
      have hint_f1 : Integrable (fun z : Ed d × Ed d => f z.1) γ := by
        refine Integrable.mono' hint_n1 (hf_cont.comp continuous_fst).aestronglyMeasurable
          (ae_of_all _ fun z => ?_)
        rw [Real.norm_eq_abs]
        exact hf_bound z.1
      have hint_f2 : Integrable (fun z : Ed d × Ed d => f z.2) γ := by
        refine Integrable.mono' hint_n2 (hf_cont.comp continuous_snd).aestronglyMeasurable
          (ae_of_all _ fun z => ?_)
        rw [Real.norm_eq_abs]
        exact hf_bound z.2
      have hint_dist : Integrable (fun z : Ed d × Ed d => dist z.1 z.2) γ := by
        refine Integrable.mono' (hint_n1.add hint_n2)
          (continuous_fst.dist continuous_snd).aestronglyMeasurable (ae_of_all _ fun z => ?_)
        simp only [Pi.add_apply, Real.norm_of_nonneg dist_nonneg]
        exact dist_le_norm_add_norm z.1 z.2
      have hf1_eq : ∫ z : Ed d × Ed d, f z.1 ∂γ = ∫ x, f x ∂μ := by
        rw [← hγ1, integral_map measurable_fst.aemeasurable hf_cont.aestronglyMeasurable]
      have hf2_eq : ∫ z : Ed d × Ed d, f z.2 ∂γ = ∫ y, f y ∂ν := by
        rw [← hγ2, integral_map measurable_snd.aemeasurable hf_cont.aestronglyMeasurable]
      calc Real.sqrt (2 / Real.pi) * Δ
          = ∫ x, f x ∂μ - ∫ y, f y ∂ν := hf_diff.symm
        _ = ∫ z, (f z.1 - f z.2) ∂γ := by
            rw [← hf1_eq, ← hf2_eq, ← integral_sub hint_f1 hint_f2]
        _ ≤ ∫ z, dist z.1 z.2 ∂γ :=
            integral_mono_ae (hint_f1.sub hint_f2) hint_dist
              (ae_of_all _ fun z => hf_lip z.1 z.2)
    have hprod_id : Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi) = 1 := by
      rw [← Real.sqrt_mul (by positivity)]
      have hpi0 : Real.pi ≠ 0 := Real.pi_pos.ne'
      have : (Real.pi / 2) * (2 / Real.pi) = 1 := by field_simp [hpi0]
      rw [this, Real.sqrt_one]
    calc Real.sqrt (OMA.S_mo_465929.transportCost 2 μ ν)
        ≤ Real.sqrt S2 := Real.sqrt_le_sqrt hcost2_le
      _ = 1 * Δ := (one_mul Δ).symm
      _ = (Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi)) * Δ := by rw [hprod_id]
      _ = Real.sqrt (Real.pi / 2) * (Real.sqrt (2 / Real.pi) * Δ) := by ring
      _ ≤ Real.sqrt (Real.pi / 2) * OMA.S_mo_465929.transportCost 1 μ ν :=
          mul_le_mul_of_nonneg_left hcost1_ge (Real.sqrt_nonneg _)

end OMA_mo_465929

theorem OMA.solution : type_of% @OMA.S_mo_465929.main :=
  OMA_mo_465929.main_proof
