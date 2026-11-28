import OMAStatements.S_arxiv_2608_00482
import Mathlib

namespace OMA.P_arxiv_2608_00482

open OMA.S_arxiv_2608_00482
open scoped BigOperators Matrix

/-! ### Part 1: EuclideanSpace and symmetric/positive-definite matrix helpers -/

private lemma dotProduct_eq_inner {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    dotProduct u.ofLp v.ofLp = inner ℝ u v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

private lemma dotProduct_self_eq_norm_sq {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) :
    dotProduct u.ofLp u.ofLp = ‖u‖ ^ 2 := by
  rw [dotProduct_eq_inner, real_inner_self_eq_norm_sq]

private lemma herm_transpose_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) : Aᵀ = A := by
  ext i j
  have h := congrFun (congrFun hA.eq i) j
  simpa [Matrix.conjTranspose_apply] using h

private lemma posDef_of_quad_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hH : A.IsHermitian)
    (hpos : ∀ u : Fin n → ℝ, u ≠ 0 → 0 < dotProduct u (A.mulVec u)) :
    A.PosDef :=
  Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hH, fun u hu => by simpa [star_trivial] using hpos u hu⟩

private lemma dotProduct_vecMulVec_mulVec {n : ℕ} (g u : Fin n → ℝ) :
    dotProduct u ((Matrix.vecMulVec g g).mulVec u) = (dotProduct g u) ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, sq, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

private lemma herm_dotProduct_mulVec_comm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (u v : Fin n → ℝ) :
    dotProduct u (A.mulVec v) = dotProduct (A.mulVec u) v := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, herm_transpose_eq hA]

private lemma posDef_isUnit_det {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) : IsUnit A.det :=
  isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)

private lemma posDef_mul_inv_self {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) : A * A⁻¹ = 1 :=
  Matrix.mul_nonsing_inv A (posDef_isUnit_det hA)

private lemma posDef_inv_mul_self {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) : A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul A (posDef_isUnit_det hA)

private lemma posDef_mulVec_ne_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {u : Fin n → ℝ} (hu : u ≠ 0) : A.mulVec u ≠ 0 := by
  intro h0
  have h1 : A⁻¹.mulVec (A.mulVec u) = 0 := by rw [h0, Matrix.mulVec_zero]
  rw [Matrix.mulVec_mulVec, posDef_inv_mul_self hA, Matrix.one_mulVec] at h1
  exact hu h1

private lemma posDef_mul_self {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) : (A * A).PosDef := by
  refine posDef_of_quad_pos ?_ ?_
  · change (A * A)ᴴ = A * A
    rw [Matrix.conjTranspose_mul, hA.1]
  · intro u hu
    rw [← Matrix.mulVec_mulVec, herm_dotProduct_mulVec_comm hA.1]
    have hne : A.mulVec u ≠ 0 := posDef_mulVec_ne_zero hA hu
    have hpos : 0 < ‖WithLp.toLp 2 (A.mulVec u)‖ ^ 2 := by
      have : WithLp.toLp 2 (A.mulVec u) ≠ 0 := by
        intro h
        exact hne (congrArg WithLp.ofLp h)
      exact sq_pos_of_pos (norm_pos_iff.mpr this)
    rw [← dotProduct_self_eq_norm_sq] at hpos
    exact hpos

private lemma posDef_inv {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) : A⁻¹.PosDef :=
  Matrix.posDef_inv_iff.mpr hA

private lemma herm_mulVec_expand {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (x : EuclideanSpace ℝ (Fin n)) :
    WithLp.toLp 2 (A.mulVec x.ofLp) =
      ∑ i : Fin n, (hA.eigenvalues i * inner ℝ (hA.eigenvectorBasis i) x) • hA.eigenvectorBasis i := by
  have hx : x = ∑ i : Fin n, inner ℝ (hA.eigenvectorBasis i) x • hA.eigenvectorBasis i :=
    (hA.eigenvectorBasis.sum_repr' x).symm
  have hx' : x.ofLp = ∑ i : Fin n, inner ℝ (hA.eigenvectorBasis i) x • (hA.eigenvectorBasis i).ofLp := by
    have := congrArg WithLp.ofLp hx
    simpa using this
  apply WithLp.ofLp_injective
  rw [WithLp.ofLp_toLp, hx', Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, hA.mulVec_eigenvectorBasis, smul_smul, mul_comm,
    WithLp.ofLp_sum, WithLp.ofLp_smul]

private lemma herm_quad_expand {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (x : EuclideanSpace ℝ (Fin n)) :
    dotProduct x.ofLp (A.mulVec x.ofLp) =
      ∑ i : Fin n, hA.eigenvalues i * (inner ℝ (hA.eigenvectorBasis i) x) ^ 2 := by
  rw [show dotProduct x.ofLp (A.mulVec x.ofLp) = inner ℝ x (WithLp.toLp 2 (A.mulVec x.ofLp)) from by
    rw [← dotProduct_eq_inner, WithLp.ofLp_toLp]]
  rw [herm_mulVec_expand hA x, inner_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inner_smul_right, real_inner_comm, sq]
  ring

private lemma herm_norm_sq_expand {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = ∑ i : Fin n, (inner ℝ (hA.eigenvectorBasis i) x) ^ 2 := by
  have h := hA.eigenvectorBasis.sum_sq_norm_inner_right x
  simpa [Real.norm_eq_abs, sq_abs] using h.symm

private lemma herm_eig_ge_of_quad_ge {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) {c : ℝ}
    (hc : ∀ x : EuclideanSpace ℝ (Fin n), c * ‖x‖ ^ 2 ≤ dotProduct x.ofLp (A.mulVec x.ofLp))
    (i : Fin n) : c ≤ hA.eigenvalues i := by
  have hv := hc (hA.eigenvectorBasis i)
  have hnorm : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have hmul : A.mulVec (hA.eigenvectorBasis i).ofLp = hA.eigenvalues i • (hA.eigenvectorBasis i).ofLp :=
    hA.mulVec_eigenvectorBasis i
  rw [hnorm, one_pow, mul_one, hmul, dotProduct_smul, smul_eq_mul,
    dotProduct_self_eq_norm_sq, hnorm, one_pow, mul_one] at hv
  exact hv

private lemma herm_eig_le_of_quad_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) {C : ℝ}
    (hC : ∀ x : EuclideanSpace ℝ (Fin n), dotProduct x.ofLp (A.mulVec x.ofLp) ≤ C * ‖x‖ ^ 2)
    (i : Fin n) : hA.eigenvalues i ≤ C := by
  have hv := hC (hA.eigenvectorBasis i)
  have hnorm : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have hmul : A.mulVec (hA.eigenvectorBasis i).ofLp = hA.eigenvalues i • (hA.eigenvectorBasis i).ofLp :=
    hA.mulVec_eigenvectorBasis i
  rw [hnorm, one_pow, mul_one, hmul, dotProduct_smul, smul_eq_mul,
    dotProduct_self_eq_norm_sq, hnorm, one_pow, mul_one] at hv
  exact hv

private lemma herm_quad_ge_of_eigs_ge {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) {c : ℝ} (hc : ∀ i, c ≤ hA.eigenvalues i)
    (x : EuclideanSpace ℝ (Fin n)) :
    c * ‖x‖ ^ 2 ≤ dotProduct x.ofLp (A.mulVec x.ofLp) := by
  rw [herm_quad_expand hA x, herm_norm_sq_expand hA x, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hc i) (sq_nonneg _))

private lemma herm_quad_le_of_eigs_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) {C : ℝ} (hC : ∀ i, hA.eigenvalues i ≤ C)
    (x : EuclideanSpace ℝ (Fin n)) :
    dotProduct x.ofLp (A.mulVec x.ofLp) ≤ C * ‖x‖ ^ 2 := by
  rw [herm_quad_expand hA x, herm_norm_sq_expand hA x, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hC i) (sq_nonneg _))

private lemma herm_abs_quad_le_of_eigs_abs_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) {B : ℝ} (hB : ∀ i, |hA.eigenvalues i| ≤ B)
    (x : EuclideanSpace ℝ (Fin n)) :
    |dotProduct x.ofLp (A.mulVec x.ofLp)| ≤ B * ‖x‖ ^ 2 := by
  rw [herm_quad_expand hA x, herm_norm_sq_expand hA x, Finset.mul_sum]
  calc
    |∑ i : Fin n, hA.eigenvalues i * (inner ℝ (hA.eigenvectorBasis i) x) ^ 2|
        ≤ ∑ i : Fin n, |hA.eigenvalues i * (inner ℝ (hA.eigenvectorBasis i) x) ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |hA.eigenvalues i| * (inner ℝ (hA.eigenvectorBasis i) x) ^ 2 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [abs_mul, abs_of_nonneg (sq_nonneg (inner ℝ (hA.eigenvectorBasis i) x))]
    _ ≤ ∑ i : Fin n, B * (inner ℝ (hA.eigenvectorBasis i) x) ^ 2 :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hB i) (sq_nonneg _))

/-- If `W` is positive definite and `m ‖x‖^2 ≤ ⟨x, W^2 x⟩`, then `√m ‖x‖^2 ≤ ⟨x, W x⟩`. -/
private lemma posDef_sqrt_lower {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.PosDef) {m : ℝ}
    (hbound : ∀ x : EuclideanSpace ℝ (Fin n), m * ‖x‖ ^ 2 ≤ dotProduct x.ofLp ((W * W).mulVec x.ofLp)) :
    ∀ x : EuclideanSpace ℝ (Fin n), Real.sqrt m * ‖x‖ ^ 2 ≤ dotProduct x.ofLp (W.mulVec x.ofLp) := by
  refine herm_quad_ge_of_eigs_ge hW.1 (fun i => ?_)
  have hpos : 0 < hW.1.eigenvalues i := hW.eigenvalues_pos i
  have hv := hbound (hW.1.eigenvectorBasis i)
  have hnorm : ‖hW.1.eigenvectorBasis i‖ = 1 := hW.1.eigenvectorBasis.orthonormal.1 i
  have hmul : (W * W).mulVec (hW.1.eigenvectorBasis i).ofLp =
      (hW.1.eigenvalues i) ^ 2 • (hW.1.eigenvectorBasis i).ofLp := by
    rw [← Matrix.mulVec_mulVec, hW.1.mulVec_eigenvectorBasis, Matrix.mulVec_smul,
      hW.1.mulVec_eigenvectorBasis, smul_smul, sq]
  rw [hnorm, one_pow, mul_one, hmul, dotProduct_smul, smul_eq_mul,
    dotProduct_self_eq_norm_sq, hnorm, one_pow, mul_one] at hv
  have hsq : Real.sqrt m ≤ Real.sqrt ((hW.1.eigenvalues i) ^ 2) := Real.sqrt_le_sqrt hv
  rwa [Real.sqrt_sq (le_of_lt hpos)] at hsq

/-- If `W` is positive definite and `⟨x, W^2 x⟩ ≤ M ‖x‖^2`, then `⟨x, W x⟩ ≤ √M ‖x‖^2`. -/
private lemma posDef_sqrt_upper {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.PosDef) {M : ℝ}
    (hbound : ∀ x : EuclideanSpace ℝ (Fin n), dotProduct x.ofLp ((W * W).mulVec x.ofLp) ≤ M * ‖x‖ ^ 2) :
    ∀ x : EuclideanSpace ℝ (Fin n), dotProduct x.ofLp (W.mulVec x.ofLp) ≤ Real.sqrt M * ‖x‖ ^ 2 := by
  refine herm_quad_le_of_eigs_le hW.1 (fun i => ?_)
  have hpos : 0 < hW.1.eigenvalues i := hW.eigenvalues_pos i
  have hv := hbound (hW.1.eigenvectorBasis i)
  have hnorm : ‖hW.1.eigenvectorBasis i‖ = 1 := hW.1.eigenvectorBasis.orthonormal.1 i
  have hmul : (W * W).mulVec (hW.1.eigenvectorBasis i).ofLp =
      (hW.1.eigenvalues i) ^ 2 • (hW.1.eigenvectorBasis i).ofLp := by
    rw [← Matrix.mulVec_mulVec, hW.1.mulVec_eigenvectorBasis, Matrix.mulVec_smul,
      hW.1.mulVec_eigenvectorBasis, smul_smul, sq]
  rw [hnorm, one_pow, mul_one, hmul, dotProduct_smul, smul_eq_mul,
    dotProduct_self_eq_norm_sq, hnorm, one_pow, mul_one] at hv
  have hsq : Real.sqrt ((hW.1.eigenvalues i) ^ 2) ≤ Real.sqrt M := Real.sqrt_le_sqrt hv
  rwa [Real.sqrt_sq (le_of_lt hpos)] at hsq

/-- If `W` is positive definite and `c ‖x‖^2 ≤ ⟨x, W x⟩` (`c > 0`), then `⟨x, W⁻¹ x⟩ ≤ (1/c) ‖x‖^2`. -/
private lemma posDef_inv_upper {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.PosDef) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x : EuclideanSpace ℝ (Fin n), c * ‖x‖ ^ 2 ≤ dotProduct x.ofLp (W.mulVec x.ofLp)) :
    ∀ x : EuclideanSpace ℝ (Fin n), dotProduct x.ofLp (W⁻¹.mulVec x.ofLp) ≤ (1 / c) * ‖x‖ ^ 2 := by
  intro x
  have hW' : ∀ i, c ≤ hW.1.eigenvalues i := herm_eig_ge_of_quad_ge hW.1 hbound
  let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (W⁻¹.mulVec x.ofLp)
  have hWy : W.mulVec y.ofLp = x.ofLp := by
    change W.mulVec (W⁻¹.mulVec x.ofLp) = x.ofLp
    rw [Matrix.mulVec_mulVec, posDef_mul_inv_self hW, Matrix.one_mulVec]
  have hcoeff : ∀ i, inner ℝ (hW.1.eigenvectorBasis i) x =
      hW.1.eigenvalues i * inner ℝ (hW.1.eigenvectorBasis i) y := by
    intro i
    rw [← dotProduct_eq_inner, ← hWy, herm_dotProduct_mulVec_comm hW.1,
      hW.1.mulVec_eigenvectorBasis, smul_dotProduct, smul_eq_mul, dotProduct_eq_inner]
  have hquad : dotProduct x.ofLp (W⁻¹.mulVec x.ofLp) = dotProduct y.ofLp (W.mulVec y.ofLp) := by
    change dotProduct x.ofLp y.ofLp = dotProduct y.ofLp (W.mulVec y.ofLp)
    rw [hWy, dotProduct_comm]
  rw [hquad, herm_quad_expand hW.1 y, herm_norm_sq_expand hW.1 x, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [hcoeff i, mul_pow]
  have hlam : c ≤ hW.1.eigenvalues i := hW' i
  have hlam_pos : 0 < hW.1.eigenvalues i := lt_of_lt_of_le hc hlam
  have h1 : hW.1.eigenvalues i ≤ (1 / c) * (hW.1.eigenvalues i) ^ 2 := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hc]
    nlinarith
  calc
    hW.1.eigenvalues i * (inner ℝ (hW.1.eigenvectorBasis i) y) ^ 2
        ≤ ((1 / c) * (hW.1.eigenvalues i) ^ 2) * (inner ℝ (hW.1.eigenvectorBasis i) y) ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = (1 / c) * ((hW.1.eigenvalues i) ^ 2 * (inner ℝ (hW.1.eigenvectorBasis i) y) ^ 2) := by ring

/-- If `W` is positive definite and `⟨x, W x⟩ ≤ C ‖x‖^2` (`C > 0`), then `(1/C) ‖x‖^2 ≤ ⟨x, W⁻¹ x⟩`. -/
private lemma posDef_inv_lower {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.PosDef) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x : EuclideanSpace ℝ (Fin n), dotProduct x.ofLp (W.mulVec x.ofLp) ≤ C * ‖x‖ ^ 2) :
    ∀ x : EuclideanSpace ℝ (Fin n), (1 / C) * ‖x‖ ^ 2 ≤ dotProduct x.ofLp (W⁻¹.mulVec x.ofLp) := by
  intro x
  have hW' : ∀ i, hW.1.eigenvalues i ≤ C := herm_eig_le_of_quad_le hW.1 hbound
  let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (W⁻¹.mulVec x.ofLp)
  have hWy : W.mulVec y.ofLp = x.ofLp := by
    change W.mulVec (W⁻¹.mulVec x.ofLp) = x.ofLp
    rw [Matrix.mulVec_mulVec, posDef_mul_inv_self hW, Matrix.one_mulVec]
  have hcoeff : ∀ i, inner ℝ (hW.1.eigenvectorBasis i) x =
      hW.1.eigenvalues i * inner ℝ (hW.1.eigenvectorBasis i) y := by
    intro i
    rw [← dotProduct_eq_inner, ← hWy, herm_dotProduct_mulVec_comm hW.1,
      hW.1.mulVec_eigenvectorBasis, smul_dotProduct, smul_eq_mul, dotProduct_eq_inner]
  have hquad : dotProduct x.ofLp (W⁻¹.mulVec x.ofLp) = dotProduct y.ofLp (W.mulVec y.ofLp) := by
    change dotProduct x.ofLp y.ofLp = dotProduct y.ofLp (W.mulVec y.ofLp)
    rw [hWy, dotProduct_comm]
  rw [hquad, herm_quad_expand hW.1 y, herm_norm_sq_expand hW.1 x, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [hcoeff i, mul_pow]
  have hlam_pos : 0 < hW.1.eigenvalues i := hW.eigenvalues_pos i
  have h1 : (1 / C) * (hW.1.eigenvalues i) ^ 2 ≤ hW.1.eigenvalues i := by
    rw [one_div, inv_mul_eq_div, div_le_iff₀ hC]
    nlinarith [hW' i]
  calc
    (1 / C) * ((hW.1.eigenvalues i) ^ 2 * (inner ℝ (hW.1.eigenvectorBasis i) y) ^ 2)
        = ((1 / C) * (hW.1.eigenvalues i) ^ 2) * (inner ℝ (hW.1.eigenvectorBasis i) y) ^ 2 := by ring
    _ ≤ hW.1.eigenvalues i * (inner ℝ (hW.1.eigenvectorBasis i) y) ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (sq_nonneg _)

/-- Sylvester operator Lipschitzness of the symmetric positive-definite square root:
if `W₁, W₂ ⪰ c I` (`c > 0`) and `|⟨u, (W₁^2 - W₂^2) u⟩| ≤ B ‖u‖^2`, then
`|⟨u, (W₁ - W₂) u⟩| ≤ (B / (2c)) ‖u‖^2` for all `u`. -/
private lemma sqrt_diff_quad_bound {n : ℕ} {W₁ W₂ : Matrix (Fin n) (Fin n) ℝ}
    (hW₁ : W₁.PosDef) (hW₂ : W₂.PosDef) {c B : ℝ} (hc : 0 < c)
    (hc₁ : ∀ u : EuclideanSpace ℝ (Fin n), c * ‖u‖ ^ 2 ≤ dotProduct u.ofLp (W₁.mulVec u.ofLp))
    (hc₂ : ∀ u : EuclideanSpace ℝ (Fin n), c * ‖u‖ ^ 2 ≤ dotProduct u.ofLp (W₂.mulVec u.ofLp))
    (hB : ∀ u : EuclideanSpace ℝ (Fin n),
      |dotProduct u.ofLp ((W₁ * W₁ - W₂ * W₂).mulVec u.ofLp)| ≤ B * ‖u‖ ^ 2) :
    ∀ u : EuclideanSpace ℝ (Fin n),
      |dotProduct u.ofLp ((W₁ - W₂).mulVec u.ofLp)| ≤ (B / (2 * c)) * ‖u‖ ^ 2 := by
  have hX : (W₁ - W₂).IsHermitian := hW₁.1.sub hW₂.1
  refine herm_abs_quad_le_of_eigs_abs_le hX (fun i => ?_)
  set v : EuclideanSpace ℝ (Fin n) := hX.eigenvectorBasis i
  set μ : ℝ := hX.eigenvalues i
  have hv_norm : ‖v‖ = 1 := hX.eigenvectorBasis.orthonormal.1 i
  have hv_eig : (W₁ - W₂).mulVec v.ofLp = μ • v.ofLp := hX.mulVec_eigenvectorBasis i
  have hsylv : W₁ * (W₁ - W₂) + (W₁ - W₂) * W₂ = W₁ * W₁ - W₂ * W₂ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, sub_add_sub_cancel]
  have h1 : dotProduct v.ofLp ((W₁ * (W₁ - W₂)).mulVec v.ofLp) =
      μ * dotProduct v.ofLp (W₁.mulVec v.ofLp) := by
    rw [← Matrix.mulVec_mulVec, hv_eig, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have h2 : dotProduct v.ofLp (((W₁ - W₂) * W₂).mulVec v.ofLp) =
      μ * dotProduct v.ofLp (W₂.mulVec v.ofLp) := by
    rw [← Matrix.mulVec_mulVec, herm_dotProduct_mulVec_comm hX, hv_eig, smul_dotProduct, smul_eq_mul]
  have hcomb : μ * (dotProduct v.ofLp (W₁.mulVec v.ofLp) + dotProduct v.ofLp (W₂.mulVec v.ofLp)) =
      dotProduct v.ofLp ((W₁ * W₁ - W₂ * W₂).mulVec v.ofLp) := by
    rw [← hsylv, Matrix.add_mulVec, dotProduct_add, h1, h2, mul_add]
  have hpos1 : c ≤ dotProduct v.ofLp (W₁.mulVec v.ofLp) := by
    simpa [hv_norm] using hc₁ v
  have hpos2 : c ≤ dotProduct v.ofLp (W₂.mulVec v.ofLp) := by
    simpa [hv_norm] using hc₂ v
  have hsum : 2 * c ≤ dotProduct v.ofLp (W₁.mulVec v.ofLp) + dotProduct v.ofLp (W₂.mulVec v.ofLp) := by
    linarith
  have hD : |dotProduct v.ofLp ((W₁ * W₁ - W₂ * W₂).mulVec v.ofLp)| ≤ B := by
    simpa [hv_norm] using hB v
  have habs : |μ| * (2 * c) ≤ B := by
    have hsum_pos : 0 < dotProduct v.ofLp (W₁.mulVec v.ofLp) + dotProduct v.ofLp (W₂.mulVec v.ofLp) := by
      linarith
    calc
      |μ| * (2 * c)
          ≤ |μ| * (dotProduct v.ofLp (W₁.mulVec v.ofLp) + dotProduct v.ofLp (W₂.mulVec v.ofLp)) :=
        mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      _ = |μ * (dotProduct v.ofLp (W₁.mulVec v.ofLp) + dotProduct v.ofLp (W₂.mulVec v.ofLp))| := by
        rw [abs_mul, abs_of_pos hsum_pos]
      _ = |dotProduct v.ofLp ((W₁ * W₁ - W₂ * W₂).mulVec v.ofLp)| := by rw [hcomb]
      _ ≤ B := hD
  exact (le_div_iff₀ (by positivity)).mpr habs

/-! ### Part 2: Convexity, locally Lipschitz gradient, and descent lemma -/

/-- First-order convexity inequality for a differentiable convex function on `ℝ^n`. -/
private lemma convex_first_order {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {grad : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hf_grad : ∀ y, HasGradientAt f (grad y) y)
    (x y : EuclideanSpace ℝ (Fin n)) :
    f x + inner ℝ (grad x) (y - x) ≤ f y := by
  -- For `t ∈ (0, 1]`, `(f (x + t (y - x)) - f x) / t ≤ f y - f x`.
  let φ : ℝ → ℝ := fun t => f (x + t • (y - x))
  have hderiv : HasDerivAt φ (inner ℝ (grad x) (y - x)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
      have h0 : HasDerivAt (fun t : ℝ => t • (y - x)) (y - x) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const (y - x)
      exact h0.const_add x
    have h2 : HasFDerivAt f (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (grad x)) (x + (0 : ℝ) • (y - x)) := by
      simpa using (hf_grad x).hasFDerivAt
    have hcomp := h2.comp_hasDerivAt 0 h1
    simpa [φ, Function.comp_def, InnerProductSpace.toDual_apply_apply] using hcomp
  have hslope_tendsto : Filter.Tendsto (fun t : ℝ => (φ t - φ 0) / t) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (inner ℝ (grad x) (y - x))) := by
    have h := (hasDerivAt_iff_tendsto_slope.mp hderiv).mono_left (nhdsWithin_mono 0 (fun t ht => ne_of_gt ht))
    refine h.congr (fun t => ?_)
    simp [slope_def_field]
  have hle : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (φ t - φ 0) / t ≤ f y - f x := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have ht0 : 0 < t := ht.1
    have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
    have hconv := hf_conv.2 (Set.mem_univ x) (Set.mem_univ y) ht1 (le_of_lt ht0) (by ring : (1 - t) + t = 1)
    have hpt : (1 - t) • x + t • y = x + t • (y - x) := by
      rw [sub_smul, one_smul, smul_sub]
      abel
    rw [hpt] at hconv
    simp only [smul_eq_mul] at hconv
    change (f (x + t • (y - x)) - f (x + (0 : ℝ) • (y - x))) / t ≤ f y - f x
    rw [zero_smul, add_zero, div_le_iff₀ ht0]
    linarith
  have hlim : inner ℝ (grad x) (y - x) ≤ f y - f x :=
    le_of_tendsto hslope_tendsto hle
  linarith

/-- Locally Lipschitz functions are Lipschitz on compact sets. -/
private lemma locallyLipschitz_lipschitzOnWith_compact {E F : Type*}
    [PseudoMetricSpace E] [PseudoMetricSpace F]
    {g : E → F} (hg : LocallyLipschitz g) {K : Set E} (hK : IsCompact K) :
    ∃ L : NNReal, LipschitzOnWith L g K := by
  by_cases hKe : K = ∅
  · subst hKe; exact ⟨0, by simp [LipschitzOnWith]⟩
  have hloc : ∀ x : E, ∃ r > 0, ∃ L : NNReal, LipschitzOnWith L g (Metric.ball x r) := by
    intro x
    obtain ⟨L, t, ht, hlip⟩ := hg x
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp ht
    exact ⟨r, hr, L, hlip.mono hsub⟩
  choose r hr L hlip using hloc
  have hcov : K ⊆ ⋃ x ∈ K, Metric.ball x (r x / 2) := fun x hx =>
    Set.mem_biUnion hx (Metric.mem_ball_self (by linarith [hr x]))
  obtain ⟨s, _hsK, hs_fin, hscov⟩ := hK.elim_finite_subcover_image (fun x _ => Metric.isOpen_ball) hcov
  let sf : Finset E := hs_fin.toFinset
  have hsf_cov : K ⊆ ⋃ x ∈ sf, Metric.ball x (r x / 2) := by
    intro x hx
    have hx' := hscov hx
    simp only [Set.mem_iUnion, exists_prop] at hx' ⊢
    rcases hx' with ⟨z, hzs, hball⟩
    exact ⟨z, hs_fin.mem_toFinset.mpr hzs, hball⟩
  have hsf_ne : sf.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have : K = ∅ := Set.subset_eq_empty hsf_cov (by simp [h])
    exact hKe this
  let δ0 : ℝ := sf.inf' hsf_ne (fun x => r x / 2)
  have hδ0 : 0 < δ0 := (Finset.lt_inf'_iff hsf_ne).mpr (fun x _ => by linarith [hr x])
  let L0 : NNReal := sf.sup' hsf_ne L
  have hcont : Continuous g := hg.continuous
  have hbdd : Bornology.IsBounded (g '' K) := (hK.image hcont).isBounded
  obtain ⟨M, hM⟩ := hbdd.subset_closedBall (g (Classical.choose (Set.nonempty_iff_ne_empty.mpr hKe)))
  have hMnn : 0 ≤ max M 0 := le_max_right _ _
  let M' : ℝ := 2 * max M 0 / δ0
  have hM'nn : 0 ≤ M' := by positivity
  let Lfinal : NNReal := max L0 ⟨M', hM'nn⟩
  refine ⟨Lfinal, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  by_cases hxy : dist x y < δ0
  · have hx' := hsf_cov hx
    simp only [Set.mem_iUnion, exists_prop] at hx'
    obtain ⟨z, hzs, hxz⟩ := hx'
    have hδz : δ0 ≤ r z / 2 := Finset.inf'_le (fun w => r w / 2) hzs
    have hxz' : x ∈ Metric.ball z (r z) := by
      rw [Metric.mem_ball] at hxz ⊢; linarith [hr z]
    have hyz' : y ∈ Metric.ball z (r z) := by
      rw [Metric.mem_ball] at hxz ⊢
      calc
        dist y z ≤ dist y x + dist x z := dist_triangle y x z
        _ = dist x y + dist x z := by rw [dist_comm]
        _ < δ0 + r z / 2 := add_lt_add hxy hxz
        _ ≤ r z / 2 + r z / 2 := by linarith
        _ = r z := by ring
    have hd := (lipschitzOnWith_iff_dist_le_mul.mp (hlip z)) x hxz' y hyz'
    have hLz : (L z : ℝ) ≤ (Lfinal : ℝ) := by
      exact_mod_cast le_trans (Finset.le_sup' L hzs) (le_max_left L0 ⟨M', hM'nn⟩)
    exact le_trans hd (mul_le_mul_of_nonneg_right hLz dist_nonneg)
  · -- `δ0 ≤ dist x y`, so `dist (g x) (g y) ≤ 2 * max M 0 ≤ M' * dist x y ≤ Lfinal * dist x y`
    push Not at hxy
    set c0 := Classical.choose (Set.nonempty_iff_ne_empty.mpr hKe)
    have hgx : dist (g x) (g c0) ≤ max M 0 :=
      le_trans (Metric.mem_closedBall.mp (hM ⟨x, hx, rfl⟩)) (le_max_left _ _)
    have hgy : dist (g y) (g c0) ≤ max M 0 :=
      le_trans (Metric.mem_closedBall.mp (hM ⟨y, hy, rfl⟩)) (le_max_left _ _)
    have hdist : dist (g x) (g y) ≤ 2 * max M 0 := by
      calc
        dist (g x) (g y) ≤ dist (g x) (g c0) + dist (g c0) (g y) := dist_triangle _ _ _
        _ = dist (g x) (g c0) + dist (g y) (g c0) := by rw [dist_comm (g c0) (g y)]
        _ ≤ max M 0 + max M 0 := add_le_add hgx hgy
        _ = 2 * max M 0 := by ring
    have hM'le : M' ≤ (Lfinal : ℝ) := by
      have : (⟨M', hM'nn⟩ : NNReal) ≤ Lfinal := le_max_right L0 ⟨M', hM'nn⟩
      exact_mod_cast this
    calc
      dist (g x) (g y) ≤ 2 * max M 0 := hdist
      _ = M' * δ0 := by dsimp only [M']; field_simp [ne_of_gt hδ0]
      _ ≤ M' * dist x y := mul_le_mul_of_nonneg_left hxy hM'nn
      _ ≤ (Lfinal : ℝ) * dist x y := mul_le_mul_of_nonneg_right hM'le dist_nonneg

/-- Smoothness descent lemma on a convex set `S` where `grad` is `L`-Lipschitz. -/
private lemma descent_lemma {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {grad : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf_grad : ∀ y, HasGradientAt f (grad y) y)
    (hgrad_cont : Continuous grad)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : Convex ℝ S)
    {L : NNReal} (hL : LipschitzOnWith L grad S)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) (hy : y ∈ S) :
    f y ≤ f x + inner ℝ (grad x) (y - x) + ((L : ℝ) / 2) * ‖y - x‖ ^ 2 := by
  let γ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => x + t • (y - x)
  let φ : ℝ → ℝ := fun t => f (γ t)
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt φ (inner ℝ (grad (γ t)) (y - x)) t := by
    intro t _
    have h1 : HasDerivAt γ (y - x) t := by
      have h0 : HasDerivAt (fun s : ℝ => s • (y - x)) (y - x) t := by
        simpa using (hasDerivAt_id t).smul_const (y - x)
      exact h0.const_add x
    have h2 : HasFDerivAt f (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (grad (γ t))) (γ t) :=
      (hf_grad (γ t)).hasFDerivAt
    have hcomp := h2.comp_hasDerivAt t h1
    simpa [φ, Function.comp_def, InnerProductSpace.toDual_apply_apply] using hcomp
  have hcont_d : Continuous (fun t : ℝ => inner ℝ (grad (γ t)) (y - x)) := by
    have hγ : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
    exact (hgrad_cont.comp hγ).inner continuous_const
  have hftc : ∫ t in (0 : ℝ)..1, inner ℝ (grad (γ t)) (y - x) = φ 1 - φ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont_d.intervalIntegrable 0 1)
  have hφ0 : φ 0 = f x := by simp [φ, γ]
  have hφ1 : φ 1 = f y := by simp [φ, γ]
  rw [hφ0, hφ1] at hftc
  have hconst_int : ∫ _t in (0 : ℝ)..1, inner ℝ (grad x) (y - x) = inner ℝ (grad x) (y - x) := by
    simp
  have hdiff_int : f y - f x - inner ℝ (grad x) (y - x) =
      ∫ t in (0 : ℝ)..1, inner ℝ (grad (γ t) - grad x) (y - x) := by
    rw [← hftc, ← hconst_int, ← intervalIntegral.integral_sub
      (hcont_d.intervalIntegrable 0 1) (continuous_const.intervalIntegrable 0 1)]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [inner_sub_left]
  have hbound_int : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      inner ℝ (grad (γ t) - grad x) (y - x) ≤ (L : ℝ) * t * ‖y - x‖ ^ 2 := by
    intro t ht
    have hγS : γ t ∈ S := by
      have hpt : γ t = (1 - t) • x + t • y := by
        dsimp only [γ]; rw [sub_smul, one_smul, smul_sub]; abel
      rw [hpt]
      exact hS hx hy (by linarith [ht.2]) ht.1 (by ring)
    have hlip : ‖grad (γ t) - grad x‖ ≤ (L : ℝ) * ‖γ t - x‖ := by
      simpa [dist_eq_norm] using (lipschitzOnWith_iff_dist_le_mul.mp hL) (γ t) hγS x hx
    have hγsub : ‖γ t - x‖ = t * ‖y - x‖ := by
      have : γ t - x = t • (y - x) := by dsimp only [γ]; abel
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc
      inner ℝ (grad (γ t) - grad x) (y - x)
          ≤ ‖grad (γ t) - grad x‖ * ‖y - x‖ := real_inner_le_norm _ _
      _ ≤ ((L : ℝ) * (t * ‖y - x‖)) * ‖y - x‖ := by
        rw [hγsub] at hlip; exact mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
      _ = (L : ℝ) * t * ‖y - x‖ ^ 2 := by ring
  have hcont_diff : Continuous (fun t : ℝ => inner ℝ (grad (γ t) - grad x) (y - x)) := by
    have hγ : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
    exact ((hgrad_cont.comp hγ).sub continuous_const).inner continuous_const
  have hcont_rhs : Continuous (fun t : ℝ => (L : ℝ) * t * ‖y - x‖ ^ 2) :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hint_le : ∫ t in (0 : ℝ)..1, inner ℝ (grad (γ t) - grad x) (y - x) ≤
      ∫ t in (0 : ℝ)..1, (L : ℝ) * t * ‖y - x‖ ^ 2 :=
    intervalIntegral.integral_mono_on (by norm_num)
      (hcont_diff.intervalIntegrable 0 1) (hcont_rhs.intervalIntegrable 0 1) hbound_int
  have hrhs : ∫ t in (0 : ℝ)..1, (L : ℝ) * t * ‖y - x‖ ^ 2 = ((L : ℝ) / 2) * ‖y - x‖ ^ 2 := by
    have hrew : (fun t : ℝ => (L : ℝ) * t * ‖y - x‖ ^ 2) = fun t => ((L : ℝ) * ‖y - x‖ ^ 2) * t := by
      funext t; ring
    rw [hrew, intervalIntegral.integral_const_mul, integral_id]
    ring
  linarith

/-! ### Part 3: Properties of `adaGradMatrix` across all 3 variants -/

private lemma adaGradMatrix_hermitian {n : ℕ} (variant : AdaGradVariant)
    (grad : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (δ : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    (adaGradMatrix variant grad δ x k).IsHermitian := by
  cases variant with
  | adaNorm =>
    unfold adaGradMatrix
    ext i j
    by_cases h : i = j <;> simp [Matrix.conjTranspose_apply, h, eq_comm]
  | adaDiag =>
    unfold adaGradMatrix
    ext i j
    by_cases h : i = j <;> simp [Matrix.conjTranspose_apply, h, eq_comm]
  | adaFull =>
    unfold adaGradMatrix
    rw [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, Matrix.conjTranspose_sum]
    simp only [star_trivial]
    congr 1
    refine Finset.sum_congr rfl (fun s _ => ?_)
    ext i j
    simp [Matrix.vecMulVec_apply, mul_comm]

private lemma adaGradMatrix_quad_lower {n : ℕ} (variant : AdaGradVariant)
    (grad : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (δ : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) :
    δ ^ 2 * ‖u‖ ^ 2 ≤ dotProduct u.ofLp ((adaGradMatrix variant grad δ x k).mulVec u.ofLp) := by
  cases variant with
  | adaNorm =>
    simp only [adaGradMatrix, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
      dotProduct_self_eq_norm_sq]
    have hsum : 0 ≤ ∑ s ∈ Finset.range (k + 1), ‖grad (x s)‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    nlinarith [sq_nonneg ‖u‖]
  | adaDiag =>
    simp only [adaGradMatrix, Matrix.mulVec_diagonal, dotProduct]
    have h1 : ∑ i : Fin n, u.ofLp i * (δ ^ 2 * u.ofLp i) = δ ^ 2 * ‖u‖ ^ 2 := by
      rw [← dotProduct_self_eq_norm_sq, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    have h2 : 0 ≤ ∑ i : Fin n, u.ofLp i * ((∑ s ∈ Finset.range (k + 1), (grad (x s)).ofLp i ^ 2) * u.ofLp i) := by
      refine Finset.sum_nonneg (fun i _ => ?_)
      have hs : 0 ≤ ∑ s ∈ Finset.range (k + 1), (grad (x s)).ofLp i ^ 2 :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have : u.ofLp i * ((∑ s ∈ Finset.range (k + 1), (grad (x s)).ofLp i ^ 2) * u.ofLp i) =
          (∑ s ∈ Finset.range (k + 1), (grad (x s)).ofLp i ^ 2) * (u.ofLp i) ^ 2 := by ring
      rw [this]
      exact mul_nonneg hs (sq_nonneg _)
    have hrew : ∑ i : Fin n, u.ofLp i * ((δ ^ 2 + ∑ s ∈ Finset.range (k + 1), (grad (x s)).ofLp i ^ 2) * u.ofLp i) =
        (∑ i : Fin n, u.ofLp i * (δ ^ 2 * u.ofLp i)) +
        ∑ i : Fin n, u.ofLp i * ((∑ s ∈ Finset.range (k + 1), (grad (x s)).ofLp i ^ 2) * u.ofLp i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [hrew, h1]
    linarith
  | adaFull =>
    simp only [adaGradMatrix, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.sum_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_self_eq_norm_sq,
      dotProduct_sum]
    have h2 : 0 ≤ ∑ s ∈ Finset.range (k + 1), dotProduct u.ofLp
        ((Matrix.vecMulVec (grad (x s)).ofLp (grad (x s)).ofLp).mulVec u.ofLp) := by
      refine Finset.sum_nonneg (fun s _ => ?_)
      rw [dotProduct_vecMulVec_mulVec]
      exact sq_nonneg _
    linarith

private lemma adaGradMatrix_posDef {n : ℕ} (variant : AdaGradVariant)
    (grad : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    {δ : ℝ} (hδ : 0 < δ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    (adaGradMatrix variant grad δ x k).PosDef := by
  refine posDef_of_quad_pos (adaGradMatrix_hermitian variant grad δ x k) (fun u hu => ?_)
  let u' : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 u
  have hu' : u' ≠ 0 := fun h => hu (congrArg WithLp.ofLp h)
  have hlow := adaGradMatrix_quad_lower variant grad δ x k u'
  have hpos : 0 < δ ^ 2 * ‖u'‖ ^ 2 := mul_pos (sq_pos_of_pos hδ) (sq_pos_of_pos (norm_pos_iff.mpr hu'))
  exact lt_of_lt_of_le hpos hlow

private lemma adaGradMatrix_quad_upper {n : ℕ} (variant : AdaGradVariant)
    (grad : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (δ : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) {k T : ℕ} (hkT : k ≤ T)
    (u : EuclideanSpace ℝ (Fin n)) :
    dotProduct u.ofLp ((adaGradMatrix variant grad δ x k).mulVec u.ofLp) ≤
      (δ ^ 2 + ∑ s ∈ Finset.range (T + 1), ‖grad (x s)‖ ^ 2) * ‖u‖ ^ 2 := by
  have hmono : ∑ s ∈ Finset.range (k + 1), ‖grad (x s)‖ ^ 2 ≤
      ∑ s ∈ Finset.range (T + 1), ‖grad (x s)‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hkT))
      (fun _ _ _ => sq_nonneg _)
  cases variant with
  | adaNorm =>
    simp only [adaGradMatrix, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
      dotProduct_self_eq_norm_sq]
    nlinarith [sq_nonneg ‖u‖]
  | adaDiag =>
    simp only [adaGradMatrix, Matrix.mulVec_diagonal, dotProduct]
    have hcoord : ∀ i : Fin n, ∑ s ∈ Finset.range (k + 1), (grad (x s)).ofLp i ^ 2 ≤
        ∑ s ∈ Finset.range (k + 1), ‖grad (x s)‖ ^ 2 := by
      intro i
      refine Finset.sum_le_sum (fun s _ => ?_)
      rw [← dotProduct_self_eq_norm_sq, dotProduct]
      have hle : (grad (x s)).ofLp i * (grad (x s)).ofLp i ≤
          ∑ j : Fin n, (grad (x s)).ofLp j * (grad (x s)).ofLp j :=
        Finset.single_le_sum (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
      simpa [sq] using hle
    calc
      ∑ i : Fin n, u.ofLp i * ((δ ^ 2 + ∑ s ∈ Finset.range (k + 1), (grad (x s)).ofLp i ^ 2) * u.ofLp i)
          = ∑ i : Fin n, (δ ^ 2 + ∑ s ∈ Finset.range (k + 1), (grad (x s)).ofLp i ^ 2) * (u.ofLp i) ^ 2 :=
        Finset.sum_congr rfl (fun i _ => by ring)
      _ ≤ ∑ i : Fin n, (δ ^ 2 + ∑ s ∈ Finset.range (T + 1), ‖grad (x s)‖ ^ 2) * (u.ofLp i) ^ 2 := by
        refine Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
        linarith [hcoord i]
      _ = (δ ^ 2 + ∑ s ∈ Finset.range (T + 1), ‖grad (x s)‖ ^ 2) * ∑ i : Fin n, (u.ofLp i) ^ 2 := by
        rw [← Finset.mul_sum]
      _ = (δ ^ 2 + ∑ s ∈ Finset.range (T + 1), ‖grad (x s)‖ ^ 2) * ‖u‖ ^ 2 := by
        rw [← dotProduct_self_eq_norm_sq, dotProduct]
        congr 1; refine Finset.sum_congr rfl (fun i _ => sq _)
  | adaFull =>
    simp only [adaGradMatrix, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.sum_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_self_eq_norm_sq,
      dotProduct_sum]
    have hsum_le : ∑ s ∈ Finset.range (k + 1), dotProduct u.ofLp
        ((Matrix.vecMulVec (grad (x s)).ofLp (grad (x s)).ofLp).mulVec u.ofLp) ≤
        (∑ s ∈ Finset.range (k + 1), ‖grad (x s)‖ ^ 2) * ‖u‖ ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun s _ => ?_)
      have hterm : dotProduct u.ofLp ((Matrix.vecMulVec (grad (x s)).ofLp (grad (x s)).ofLp).mulVec u.ofLp) =
          (inner ℝ (grad (x s)) u) ^ 2 := by
        rw [dotProduct_vecMulVec_mulVec, dotProduct_eq_inner]
      rw [hterm, ← sq_abs (inner ℝ (grad (x s)) u)]
      have hcs : |inner ℝ (grad (x s)) u| ≤ ‖grad (x s)‖ * ‖u‖ := abs_real_inner_le_norm _ _
      have hsq : |inner ℝ (grad (x s)) u| ^ 2 ≤ (‖grad (x s)‖ * ‖u‖) ^ 2 :=
        sq_le_sq' (by linarith [abs_nonneg (inner ℝ (grad (x s)) u), mul_nonneg (norm_nonneg (grad (x s))) (norm_nonneg u)]) hcs
      linarith [mul_pow ‖grad (x s)‖ ‖u‖ 2]
    nlinarith [sq_nonneg ‖u‖]

/-- Extended matrix sequence `G_ext 0 = δ^2 I`, `G_ext (k + 1) = G_k`. -/
private noncomputable def adaGradMatrixExt {n : ℕ} (variant : AdaGradVariant)
    (grad : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (δ : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => δ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)
  | k + 1 => adaGradMatrix variant grad δ x k

/-- One-step increment bound: `|⟨u, (G_ext (k+1) - G_ext k) u⟩| ≤ ‖g_k‖^2 ‖u‖^2`. -/
private lemma adaGradMatrixExt_diff_bound {n : ℕ} (variant : AdaGradVariant)
    (grad : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (δ : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) :
    |dotProduct u.ofLp ((adaGradMatrixExt variant grad δ x (k + 1) -
      adaGradMatrixExt variant grad δ x k).mulVec u.ofLp)| ≤ ‖grad (x k)‖ ^ 2 * ‖u‖ ^ 2 := by
  have hdiff : ∀ (m : ℕ), adaGradMatrixExt variant grad δ x (m + 1) -
      adaGradMatrixExt variant grad δ x m =
      match variant with
      | .adaNorm => ‖grad (x m)‖ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)
      | .adaDiag => Matrix.diagonal (fun i => (grad (x m)).ofLp i ^ 2)
      | .adaFull => Matrix.vecMulVec (grad (x m)).ofLp (grad (x m)).ofLp := by
    intro m
    cases m with
    | zero =>
      cases variant with
      | adaNorm =>
        simp [adaGradMatrixExt, adaGradMatrix, add_smul]
      | adaDiag =>
        ext i j
        by_cases h : i = j <;> simp [adaGradMatrixExt, adaGradMatrix, h]
      | adaFull =>
        simp [adaGradMatrixExt, adaGradMatrix]
    | succ m' =>
      cases variant with
      | adaNorm =>
        simp only [adaGradMatrixExt, adaGradMatrix, Finset.sum_range_succ]
        rw [← add_assoc, add_smul, add_sub_cancel_left]
      | adaDiag =>
        ext i j
        by_cases h : i = j <;> simp [adaGradMatrixExt, adaGradMatrix, Finset.sum_range_succ, h]
      | adaFull =>
        simp only [adaGradMatrixExt, adaGradMatrix, Finset.sum_range_succ]
        rw [← add_assoc, add_sub_cancel_left]
  rw [hdiff k]
  cases variant with
  | adaNorm =>
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
      dotProduct_self_eq_norm_sq]
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg ‖grad (x k)‖) (sq_nonneg ‖u‖))]
  | adaDiag =>
    simp only [Matrix.mulVec_diagonal, dotProduct]
    have hnn : 0 ≤ ∑ i : Fin n, u.ofLp i * ((grad (x k)).ofLp i ^ 2 * u.ofLp i) :=
      Finset.sum_nonneg (fun i _ => by
        have : u.ofLp i * ((grad (x k)).ofLp i ^ 2 * u.ofLp i) = ((grad (x k)).ofLp i * u.ofLp i) ^ 2 := by ring
        rw [this]; exact sq_nonneg _)
    rw [abs_of_nonneg hnn]
    calc
      ∑ i : Fin n, u.ofLp i * ((grad (x k)).ofLp i ^ 2 * u.ofLp i)
          = ∑ i : Fin n, (grad (x k)).ofLp i ^ 2 * (u.ofLp i) ^ 2 :=
        Finset.sum_congr rfl (fun i _ => by ring)
      _ ≤ ∑ i : Fin n, ‖grad (x k)‖ ^ 2 * (u.ofLp i) ^ 2 := by
        refine Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
        rw [← dotProduct_self_eq_norm_sq, dotProduct]
        have hle : (grad (x k)).ofLp i * (grad (x k)).ofLp i ≤
            ∑ j : Fin n, (grad (x k)).ofLp j * (grad (x k)).ofLp j :=
          Finset.single_le_sum (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
        simpa [sq] using hle
      _ = ‖grad (x k)‖ ^ 2 * ‖u‖ ^ 2 := by
        rw [← Finset.mul_sum]
        congr 1
        rw [← dotProduct_self_eq_norm_sq, dotProduct]
        exact Finset.sum_congr rfl (fun i _ => sq (u.ofLp i))
  | adaFull =>
    have hterm : dotProduct u.ofLp ((Matrix.vecMulVec (grad (x k)).ofLp (grad (x k)).ofLp).mulVec u.ofLp) =
        (inner ℝ (grad (x k)) u) ^ 2 := by
      rw [dotProduct_vecMulVec_mulVec, dotProduct_eq_inner]
    rw [hterm, abs_of_nonneg (sq_nonneg _), ← sq_abs (inner ℝ (grad (x k)) u)]
    have hcs : |inner ℝ (grad (x k)) u| ≤ ‖grad (x k)‖ * ‖u‖ := abs_real_inner_le_norm _ _
    have hsq : |inner ℝ (grad (x k)) u| ^ 2 ≤ (‖grad (x k)‖ * ‖u‖) ^ 2 :=
      sq_le_sq' (by linarith [abs_nonneg (inner ℝ (grad (x k)) u), mul_nonneg (norm_nonneg (grad (x k))) (norm_nonneg u)]) hcs
    linarith [mul_pow ‖grad (x k)‖ ‖u‖ 2]

/-! ### Part 4: Logarithmic potential bound for all 3 variants -/

/-- Elementary scalar inequality: for `0 < a ≤ b`, `(b - a) / b ≤ log b - log a`. -/
private lemma sub_div_le_log_sub_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (b - a) / b ≤ Real.log b - Real.log a := by
  have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb)] at h
  have h1 : (b - a) / b = 1 - a / b := by field_simp [ne_of_gt hb]
  linarith

/-- Telescoping logarithmic potential bound for all 3 variants:
`∑_{k=0}^T ⟨g_k, G_k⁻¹ g_k⟩ ≤ n * log (1 + S_T / δ^2)` when `1 ≤ n`. -/
private lemma adaGrad_log_potential {n : ℕ} (hn : 1 ≤ n) (variant : AdaGradVariant)
    (grad : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    {δ : ℝ} (hδ : 0 < δ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (T : ℕ) :
    ∑ k ∈ Finset.range (T + 1),
      dotProduct (grad (x k)).ofLp ((adaGradMatrix variant grad δ x k)⁻¹.mulVec (grad (x k)).ofLp) ≤
      (n : ℝ) * Real.log (1 + (∑ s ∈ Finset.range (T + 1), ‖grad (x s)‖ ^ 2) / δ ^ 2) := by
  set S : ℕ → ℝ := fun m => ∑ s ∈ Finset.range m, ‖grad (x s)‖ ^ 2
  have hS_nn : ∀ m, 0 ≤ S m := fun m => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hlog_nn : 0 ≤ Real.log (1 + S (T + 1) / δ ^ 2) :=
    Real.log_nonneg (by linarith [div_nonneg (hS_nn (T + 1)) (sq_nonneg δ)])
  cases variant with
  | adaNorm =>
    have hstep : ∀ k : ℕ,
        dotProduct (grad (x k)).ofLp ((adaGradMatrix .adaNorm grad δ x k)⁻¹.mulVec (grad (x k)).ofLp) ≤
          Real.log (δ ^ 2 + S (k + 1)) - Real.log (δ ^ 2 + S k) := by
      intro k
      set c := δ ^ 2 + S (k + 1)
      have hc : 0 < c := by linarith [sq_pos_of_pos hδ, hS_nn (k + 1)]
      have hc_prev : 0 < δ ^ 2 + S k := by linarith [sq_pos_of_pos hδ, hS_nn k]
      have hinv : (c • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ = c⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ) := by
        have hmul : (c • (1 : Matrix (Fin n) (Fin n) ℝ)) * (c⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) = 1 := by
          rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (ne_of_gt hc), one_smul, Matrix.mul_one]
        have hGpd : (c • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := adaGradMatrix_posDef .adaNorm grad hδ x k
        calc
          (c • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹
              = (c • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ * ((c • (1 : Matrix (Fin n) (Fin n) ℝ)) * (c⁻¹ • 1)) := by
            rw [hmul, Matrix.mul_one]
          _ = ((c • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ * (c • 1)) * (c⁻¹ • 1) := by rw [Matrix.mul_assoc]
          _ = c⁻¹ • 1 := by rw [posDef_inv_mul_self hGpd, Matrix.one_mul]
      change dotProduct (grad (x k)).ofLp ((c • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹.mulVec (grad (x k)).ofLp) ≤ _
      rw [hinv, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
        dotProduct_self_eq_norm_sq]
      have hdiff : c - (δ ^ 2 + S k) = ‖grad (x k)‖ ^ 2 := by
        dsimp only [c, S]; rw [Finset.sum_range_succ]; ring
      have hdiv : c⁻¹ * ‖grad (x k)‖ ^ 2 = (c - (δ ^ 2 + S k)) / c := by
        rw [hdiff, div_eq_inv_mul]
      rw [hdiv]
      exact sub_div_le_log_sub_log hc_prev hc
    have htele : ∑ k ∈ Finset.range (T + 1),
        (Real.log (δ ^ 2 + S (k + 1)) - Real.log (δ ^ 2 + S k)) =
        Real.log (δ ^ 2 + S (T + 1)) - Real.log (δ ^ 2 + S 0) :=
      Finset.sum_range_sub (fun m => Real.log (δ ^ 2 + S m)) (T + 1)
    have hS0 : S 0 = 0 := by simp [S]
    have hratio : Real.log (δ ^ 2 + S (T + 1)) - Real.log (δ ^ 2) =
        Real.log (1 + S (T + 1) / δ ^ 2) := by
      rw [← Real.log_div (ne_of_gt (by linarith [sq_pos_of_pos hδ, hS_nn (T + 1)]))
        (ne_of_gt (sq_pos_of_pos hδ))]
      congr 1; field_simp [ne_of_gt (sq_pos_of_pos hδ)]
    calc
      ∑ k ∈ Finset.range (T + 1),
          dotProduct (grad (x k)).ofLp ((adaGradMatrix .adaNorm grad δ x k)⁻¹.mulVec (grad (x k)).ofLp)
          ≤ ∑ k ∈ Finset.range (T + 1), (Real.log (δ ^ 2 + S (k + 1)) - Real.log (δ ^ 2 + S k)) :=
        Finset.sum_le_sum (fun k _ => hstep k)
      _ = Real.log (1 + S (T + 1) / δ ^ 2) := by rw [htele, hS0, add_zero, hratio]
      _ ≤ (n : ℝ) * Real.log (1 + S (T + 1) / δ ^ 2) := by
        have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        nlinarith
  | adaDiag =>
    let d : ℕ → Fin n → ℝ := fun m i => δ ^ 2 + ∑ s ∈ Finset.range m, (grad (x s)).ofLp i ^ 2
    have hd_pos : ∀ m i, 0 < d m i := fun m i => by
      dsimp only [d]
      linarith [sq_pos_of_pos hδ, Finset.sum_nonneg (s := Finset.range m) (fun s _ => sq_nonneg ((grad (x s)).ofLp i))]
    have hinv : ∀ k : ℕ, (adaGradMatrix .adaDiag grad δ x k)⁻¹ =
        Matrix.diagonal (fun i => (d (k + 1) i)⁻¹) := by
      intro k
      have hGpd := adaGradMatrix_posDef .adaDiag grad hδ x k
      have hmul : adaGradMatrix .adaDiag grad δ x k * Matrix.diagonal (fun i => (d (k + 1) i)⁻¹) = 1 := by
        change Matrix.diagonal (d (k + 1)) * Matrix.diagonal (fun i => (d (k + 1) i)⁻¹) = 1
        rw [Matrix.diagonal_mul_diagonal]
        ext i j
        by_cases h : i = j
        · subst h; simp [mul_inv_cancel₀ (ne_of_gt (hd_pos (k + 1) i))]
        · simp [h]
      calc
        (adaGradMatrix .adaDiag grad δ x k)⁻¹
            = (adaGradMatrix .adaDiag grad δ x k)⁻¹ *
                (adaGradMatrix .adaDiag grad δ x k * Matrix.diagonal (fun i => (d (k + 1) i)⁻¹)) := by
          rw [hmul, Matrix.mul_one]
        _ = ((adaGradMatrix .adaDiag grad δ x k)⁻¹ * adaGradMatrix .adaDiag grad δ x k) *
              Matrix.diagonal (fun i => (d (k + 1) i)⁻¹) := by rw [Matrix.mul_assoc]
        _ = Matrix.diagonal (fun i => (d (k + 1) i)⁻¹) := by rw [posDef_inv_mul_self hGpd, Matrix.one_mul]
    have hrew : ∑ k ∈ Finset.range (T + 1),
        dotProduct (grad (x k)).ofLp ((adaGradMatrix .adaDiag grad δ x k)⁻¹.mulVec (grad (x k)).ofLp) =
        ∑ i : Fin n, ∑ k ∈ Finset.range (T + 1),
          (grad (x k)).ofLp i ^ 2 / d (k + 1) i := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hinv k, dotProduct]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Matrix.mulVec_diagonal, sq, div_eq_mul_inv]; ring
    rw [hrew]
    have hcoord_sum : ∀ i : Fin n,
        ∑ k ∈ Finset.range (T + 1), (grad (x k)).ofLp i ^ 2 / d (k + 1) i ≤
          Real.log (1 + S (T + 1) / δ ^ 2) := by
      intro i
      have hstep : ∀ k : ℕ, (grad (x k)).ofLp i ^ 2 / d (k + 1) i ≤
          Real.log (d (k + 1) i) - Real.log (d k i) := by
        intro k
        have hdiff : d (k + 1) i - d k i = (grad (x k)).ofLp i ^ 2 := by
          dsimp only [d]; rw [Finset.sum_range_succ]; ring
        rw [← hdiff]
        exact sub_div_le_log_sub_log (hd_pos k i) (hd_pos (k + 1) i)
      have htele : ∑ k ∈ Finset.range (T + 1), (Real.log (d (k + 1) i) - Real.log (d k i)) =
          Real.log (d (T + 1) i) - Real.log (d 0 i) :=
        Finset.sum_range_sub (fun m => Real.log (d m i)) (T + 1)
      have hd0 : d 0 i = δ ^ 2 := by simp [d]
      have hd_le : d (T + 1) i ≤ δ ^ 2 + S (T + 1) := by
        dsimp only [d, S]
        refine add_le_add (le_refl (δ ^ 2)) (Finset.sum_le_sum (fun s _ => ?_))
        rw [← dotProduct_self_eq_norm_sq, dotProduct]
        have hle : (grad (x s)).ofLp i * (grad (x s)).ofLp i ≤
            ∑ j : Fin n, (grad (x s)).ofLp j * (grad (x s)).ofLp j :=
          Finset.single_le_sum (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
        simpa [sq] using hle
      calc
        ∑ k ∈ Finset.range (T + 1), (grad (x k)).ofLp i ^ 2 / d (k + 1) i
            ≤ Real.log (d (T + 1) i) - Real.log (δ ^ 2) := by
          rw [← hd0, ← htele]; exact Finset.sum_le_sum (fun k _ => hstep k)
        _ ≤ Real.log (δ ^ 2 + S (T + 1)) - Real.log (δ ^ 2) := by
          linarith [Real.log_le_log (hd_pos (T + 1) i) hd_le]
        _ = Real.log (1 + S (T + 1) / δ ^ 2) := by
          rw [← Real.log_div (ne_of_gt (by linarith [sq_pos_of_pos hδ, hS_nn (T + 1)]))
            (ne_of_gt (sq_pos_of_pos hδ))]
          congr 1; field_simp [ne_of_gt (sq_pos_of_pos hδ)]
    calc
      ∑ i : Fin n, ∑ k ∈ Finset.range (T + 1), (grad (x k)).ofLp i ^ 2 / d (k + 1) i
          ≤ ∑ _i : Fin n, Real.log (1 + S (T + 1) / δ ^ 2) :=
        Finset.sum_le_sum (fun i _ => hcoord_sum i)
      _ = (n : ℝ) * Real.log (1 + S (T + 1) / δ ^ 2) := by
        simp [Finset.sum_const, nsmul_eq_mul]
  | adaFull =>
    -- Use the Matrix Determinant Lemma on `G_{k-1} = G_k - g_k g_kᵀ`!
    let Gext : ℕ → Matrix (Fin n) (Fin n) ℝ := adaGradMatrixExt .adaFull grad δ x
    have hGext_pd : ∀ m, (Gext m).PosDef := by
      intro m
      cases m with
      | zero =>
        change (δ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef
        refine posDef_of_quad_pos (by ext i j; by_cases h : i = j <;> simp [Matrix.conjTranspose_apply, h, eq_comm]) (fun u hu => ?_)
        rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
        have hu' : WithLp.toLp 2 u ≠ 0 := fun h => hu (congrArg WithLp.ofLp h)
        have hpos : 0 < ‖WithLp.toLp 2 u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu')
        rw [← dotProduct_self_eq_norm_sq] at hpos
        exact mul_pos (sq_pos_of_pos hδ) hpos
      | succ k => exact adaGradMatrix_posDef .adaFull grad hδ x k
    have hstep : ∀ k : ℕ,
        dotProduct (grad (x k)).ofLp ((Gext (k + 1))⁻¹.mulVec (grad (x k)).ofLp) ≤
          Real.log (Gext (k + 1)).det - Real.log (Gext k).det := by
      intro k
      set g := (grad (x k)).ofLp
      have hrel : Gext k = Gext (k + 1) + Matrix.replicateCol Unit (-g) * Matrix.replicateRow Unit g := by
        have hadd : Gext (k + 1) = Gext k + Matrix.vecMulVec g g := by
          cases k with
          | zero => simp [Gext, adaGradMatrixExt, adaGradMatrix, g]
          | succ k' =>
            simp only [Gext, adaGradMatrixExt, adaGradMatrix, Finset.sum_range_succ, g]
            rw [← add_assoc]
        have hrep : Matrix.replicateCol Unit (-g) * Matrix.replicateRow Unit g = -Matrix.vecMulVec g g := by
          ext i j
          simp [Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply,
            Matrix.vecMulVec_apply]
        rw [hrep, hadd, add_neg_cancel_right]
      have hdet_eq : (Gext k).det =
          (Gext (k + 1)).det * (1 - dotProduct g ((Gext (k + 1))⁻¹.mulVec g)) := by
        rw [hrel, Matrix.det_add_replicateCol_mul_replicateRow (posDef_isUnit_det (hGext_pd (k + 1)))]
        congr 1
        rw [Matrix.det_unique]
        simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply,
          Matrix.replicateRow_apply, Matrix.replicateCol_apply,
          Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
        have hquad : ∑ j : Fin n, (∑ i : Fin n, g i * (Gext (k + 1))⁻¹ i j) * g j =
            dotProduct g ((Gext (k + 1))⁻¹.mulVec g) := by
          simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
        rw [sub_eq_add_neg, ← hquad]
      have hd1 : 0 < (Gext (k + 1)).det := (hGext_pd (k + 1)).det_pos
      have hd0 : 0 < (Gext k).det := (hGext_pd k).det_pos
      have hfrac : dotProduct g ((Gext (k + 1))⁻¹.mulVec g) =
          ((Gext (k + 1)).det - (Gext k).det) / (Gext (k + 1)).det := by
        rw [hdet_eq]
        field_simp [ne_of_gt hd1]
        ring
      rw [hfrac]
      exact sub_div_le_log_sub_log hd0 hd1
    have htele : ∑ k ∈ Finset.range (T + 1), (Real.log (Gext (k + 1)).det - Real.log (Gext k).det) =
        Real.log (Gext (T + 1)).det - Real.log (Gext 0).det :=
      Finset.sum_range_sub (fun m => Real.log (Gext m).det) (T + 1)
    have hdet0 : (Gext 0).det = (δ ^ 2) ^ n := by
      change (δ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)).det = (δ ^ 2) ^ n
      rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
    have hdetT : (Gext (T + 1)).det ≤ (δ ^ 2 + S (T + 1)) ^ n := by
      have hGT := hGext_pd (T + 1)
      have heig_le : ∀ i : Fin n, hGT.1.eigenvalues i ≤ δ ^ 2 + S (T + 1) :=
        herm_eig_le_of_quad_le hGT.1 (fun u => adaGradMatrix_quad_upper .adaFull grad δ x le_rfl u)
      rw [hGT.1.det_eq_prod_eigenvalues]
      calc
        ∏ i : Fin n, hGT.1.eigenvalues i
            ≤ ∏ _i : Fin n, (δ ^ 2 + S (T + 1)) :=
          Finset.prod_le_prod (fun i _ => le_of_lt (hGT.eigenvalues_pos i)) (fun i _ => heig_le i)
        _ = (δ ^ 2 + S (T + 1)) ^ n := by simp
    have hGT_pos : 0 < (Gext (T + 1)).det := (hGext_pd (T + 1)).det_pos
    have hδn_pos : 0 < (δ ^ 2) ^ n := pow_pos (sq_pos_of_pos hδ) n
    have hST_pos : 0 < δ ^ 2 + S (T + 1) := by linarith [sq_pos_of_pos hδ, hS_nn (T + 1)]
    calc
      ∑ k ∈ Finset.range (T + 1),
          dotProduct (grad (x k)).ofLp ((adaGradMatrix .adaFull grad δ x k)⁻¹.mulVec (grad (x k)).ofLp)
          ≤ Real.log (Gext (T + 1)).det - Real.log (Gext 0).det := by
        rw [← htele]; exact Finset.sum_le_sum (fun k _ => hstep k)
      _ ≤ Real.log ((δ ^ 2 + S (T + 1)) ^ n) - Real.log ((δ ^ 2) ^ n) := by
        rw [hdet0]; linarith [Real.log_le_log hGT_pos hdetT]
      _ = (n : ℝ) * Real.log (1 + S (T + 1) / δ ^ 2) := by
        rw [Real.log_pow, Real.log_pow, ← mul_sub, ← Real.log_div (ne_of_gt hST_pos) (ne_of_gt (sq_pos_of_pos hδ))]
        congr 2; field_simp [ne_of_gt (sq_pos_of_pos hδ)]

/-! ### Part 5: Implication `(2) ⇒ (3)` (Bounded iterates imply `∑ ‖∇f(x_k)‖^2 < ∞`) -/

private lemma bounded_implies_summable {n : ℕ} (hn : 1 ≤ n) (variant : AdaGradVariant)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (grad : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hf_grad : ∀ y, HasGradientAt f (grad y) y)
    (hgrad_ll : LocallyLipschitz grad)
    (hmin : ∃ z : EuclideanSpace ℝ (Fin n), ∀ y, f z ≤ f y)
    (hada : IsAdaGradSeq variant grad δ η x)
    (hbdd : Bornology.IsBounded (Set.range x)) :
    Summable (fun k => ‖grad (x k)‖ ^ 2) := by
  obtain ⟨z, hz⟩ := hmin
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  have hxR : ∀ k, x k ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R :=
    fun k => hR ⟨k, rfl⟩
  obtain ⟨L, hL⟩ := locallyLipschitz_lipschitzOnWith_compact hgrad_ll (isCompact_closedBall 0 R)
  have hS_conv : Convex ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) :=
    convex_closedBall 0 R
  -- Choose `Γ k` for each `k`
  choose Γ hΓ_pd hΓ_sq hstep_x using hada
  have hΓ_sq_inv : ∀ k, Γ k * Γ k = (adaGradMatrix variant grad δ x k)⁻¹ := by
    intro k
    have hGpd := adaGradMatrix_posDef variant grad hδ x k
    calc
      Γ k * Γ k = (Γ k * Γ k) * (adaGradMatrix variant grad δ x k * (adaGradMatrix variant grad δ x k)⁻¹) := by
        rw [posDef_mul_inv_self hGpd, Matrix.mul_one]
      _ = (Γ k * Γ k * adaGradMatrix variant grad δ x k) * (adaGradMatrix variant grad δ x k)⁻¹ := by
        simp only [Matrix.mul_assoc]
      _ = (adaGradMatrix variant grad δ x k)⁻¹ := by rw [hΓ_sq k, Matrix.one_mul]
  -- One-step descent inequality for each `k`
  have hdesc : ∀ k,
      η * dotProduct (grad (x k)).ofLp ((Γ k).mulVec (grad (x k)).ofLp) ≤
        (f (x k) - f (x (k + 1))) +
        (η ^ 2 * (L : ℝ) / 2) *
          dotProduct (grad (x k)).ofLp ((adaGradMatrix variant grad δ x k)⁻¹.mulVec (grad (x k)).ofLp) := by
    intro k
    have hd := descent_lemma hf_grad hgrad_ll.continuous hS_conv hL (hxR k) (hxR (k + 1))
    have hdx : x (k + 1) - x k = -(η • WithLp.toLp 2 ((Γ k).mulVec (grad (x k)).ofLp)) := by
      rw [hstep_x k]; abel
    have hinner : inner ℝ (grad (x k)) (x (k + 1) - x k) =
        -(η * dotProduct (grad (x k)).ofLp ((Γ k).mulVec (grad (x k)).ofLp)) := by
      rw [hdx, inner_neg_right, inner_smul_right, ← dotProduct_eq_inner, WithLp.ofLp_toLp]
    have hnorm : ‖x (k + 1) - x k‖ ^ 2 =
        η ^ 2 * dotProduct (grad (x k)).ofLp ((adaGradMatrix variant grad δ x k)⁻¹.mulVec (grad (x k)).ofLp) := by
      rw [hdx, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hη, mul_pow,
        ← dotProduct_self_eq_norm_sq, WithLp.ofLp_toLp, ← herm_dotProduct_mulVec_comm (hΓ_pd k).1,
        Matrix.mulVec_mulVec, hΓ_sq_inv k]
    rw [hinner, hnorm] at hd
    linarith
  -- Sum from `k = 0` to `T` and deduce uniform bound on `S_T = ∑_{k=0}^T ‖g_k‖^2`
  let C1 : ℝ := max (f (x 0) - f z) 0
  let C2 : ℝ := η ^ 2 * (L : ℝ) / 2 * (n : ℝ)
  have hC1 : 0 ≤ C1 := le_max_right _ _
  have hC2 : 0 ≤ C2 := by positivity
  let U : ℝ := (C1 + η * δ + 8 * C2 ^ 2 / (η * δ)) / (η * δ / 2)
  have hU_nn : 0 ≤ U := by positivity
  have hS_bdd : ∀ N : ℕ, ∑ k ∈ Finset.range N, ‖grad (x k)‖ ^ 2 ≤ δ ^ 2 * U ^ 2 := by
    intro N
    cases N with
    | zero => simp; positivity
    | succ T =>
      set ST : ℝ := ∑ k ∈ Finset.range (T + 1), ‖grad (x k)‖ ^ 2
      have hST_nn : 0 ≤ ST := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      -- Upper bound on `η * ∑_{k=0}^T ⟨g_k, Γ_k g_k⟩`
      have hsum_desc : η * ∑ k ∈ Finset.range (T + 1),
          dotProduct (grad (x k)).ofLp ((Γ k).mulVec (grad (x k)).ofLp) ≤
          C1 + C2 * Real.log (1 + ST / δ ^ 2) := by
        have h1 : ∑ k ∈ Finset.range (T + 1),
            η * dotProduct (grad (x k)).ofLp ((Γ k).mulVec (grad (x k)).ofLp) ≤
            ∑ k ∈ Finset.range (T + 1), (f (x k) - f (x (k + 1))) +
            (η ^ 2 * (L : ℝ) / 2) * ∑ k ∈ Finset.range (T + 1),
              dotProduct (grad (x k)).ofLp ((adaGradMatrix variant grad δ x k)⁻¹.mulVec (grad (x k)).ofLp) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_le_sum (fun k _ => hdesc k)
        rw [← Finset.mul_sum] at h1
        have htele : ∑ k ∈ Finset.range (T + 1), (f (x k) - f (x (k + 1))) = f (x 0) - f (x (T + 1)) := by
          have := Finset.sum_range_sub' (fun m => f (x m)) (T + 1)
          exact this
        have hfx : f (x 0) - f (x (T + 1)) ≤ C1 :=
          le_trans (by linarith [hz (x (T + 1))]) (le_max_left _ _)
        have hpot := adaGrad_log_potential hn variant grad hδ x T
        have hcoef : 0 ≤ η ^ 2 * (L : ℝ) / 2 := by positivity
        have h2 := mul_le_mul_of_nonneg_left hpot hcoef
        dsimp only [C2]
        linarith
      -- Lower bound on `∑_{k=0}^T ⟨g_k, Γ_k g_k⟩`: `≥ ST / √(δ^2 + ST)`
      have hsum_low : ST / Real.sqrt (δ ^ 2 + ST) ≤
          ∑ k ∈ Finset.range (T + 1), dotProduct (grad (x k)).ofLp ((Γ k).mulVec (grad (x k)).ofLp) := by
        have hterm_low : ∀ k ∈ Finset.range (T + 1),
            (1 / Real.sqrt (δ ^ 2 + ST)) * ‖grad (x k)‖ ^ 2 ≤
              dotProduct (grad (x k)).ofLp ((Γ k).mulVec (grad (x k)).ofLp) := by
          intro k hk
          have hkT : k ≤ T := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          let W := (Γ k)⁻¹
          have hW_pd : W.PosDef := posDef_inv (hΓ_pd k)
          have hW_sq : W * W = adaGradMatrix variant grad δ x k := by
            have h1 : W * W * (Γ k * Γ k) = 1 := by
              calc
                W * W * (Γ k * Γ k) = W * (W * Γ k) * Γ k := by simp only [Matrix.mul_assoc]
                _ = W * 1 * Γ k := by rw [posDef_inv_mul_self (hΓ_pd k)]
                _ = 1 := by rw [Matrix.mul_one, posDef_inv_mul_self (hΓ_pd k)]
            calc
              W * W = (W * W) * (Γ k * Γ k * adaGradMatrix variant grad δ x k) := by
                rw [hΓ_sq k, Matrix.mul_one]
              _ = (W * W * (Γ k * Γ k)) * adaGradMatrix variant grad δ x k := by
                simp only [Matrix.mul_assoc]
              _ = adaGradMatrix variant grad δ x k := by rw [h1, Matrix.one_mul]
          have hW_up : ∀ u : EuclideanSpace ℝ (Fin n),
              dotProduct u.ofLp (W.mulVec u.ofLp) ≤ Real.sqrt (δ ^ 2 + ST) * ‖u‖ ^ 2 := by
            refine posDef_sqrt_upper hW_pd (fun u => ?_)
            rw [hW_sq]
            exact adaGradMatrix_quad_upper variant grad δ x hkT u
          have hWinv : W⁻¹ = Γ k := Matrix.nonsing_inv_nonsing_inv (Γ k) (posDef_isUnit_det (hΓ_pd k))
          have hlow := posDef_inv_lower hW_pd (Real.sqrt_pos.mpr (by positivity)) hW_up (grad (x k))
          rwa [hWinv] at hlow
        calc
          ST / Real.sqrt (δ ^ 2 + ST) = (1 / Real.sqrt (δ ^ 2 + ST)) * ST := by ring
          _ = ∑ k ∈ Finset.range (T + 1), (1 / Real.sqrt (δ ^ 2 + ST)) * ‖grad (x k)‖ ^ 2 := by
            rw [Finset.mul_sum]
          _ ≤ ∑ k ∈ Finset.range (T + 1),
                dotProduct (grad (x k)).ofLp ((Γ k).mulVec (grad (x k)).ofLp) :=
            Finset.sum_le_sum hterm_low
      set u : ℝ := Real.sqrt (1 + ST / δ ^ 2)
      have hu1 : 1 ≤ u := by
        have h1 : (1 : ℝ) ≤ 1 + ST / δ ^ 2 := by linarith [div_nonneg hST_nn (sq_nonneg δ)]
        have h2 := Real.sqrt_le_sqrt h1
        rwa [Real.sqrt_one] at h2
      have hu_pos : 0 < u := by linarith
      have hu_sq : u ^ 2 = 1 + ST / δ ^ 2 := Real.sq_sqrt (by positivity)
      have hST_eq : ST = δ ^ 2 * (u ^ 2 - 1) := by
        have h1 : ST / δ ^ 2 = u ^ 2 - 1 := by linarith
        field_simp [ne_of_gt (sq_pos_of_pos hδ)] at h1 ⊢
        linarith
      have hsqrt_eq : Real.sqrt (δ ^ 2 + ST) = δ * u := by
        have h1 : δ ^ 2 + ST = (δ * u) ^ 2 := by rw [hST_eq]; ring
        rw [h1, Real.sqrt_sq (by positivity)]
      have hlhs : η * δ * u - η * δ ≤ η * (ST / Real.sqrt (δ ^ 2 + ST)) := by
        rw [hsqrt_eq, hST_eq]
        have h1 : η * (δ ^ 2 * (u ^ 2 - 1) / (δ * u)) = η * δ * u - η * δ / u := by
          field_simp [ne_of_gt hδ, ne_of_gt hu_pos]
        rw [h1]
        have h2 : η * δ / u ≤ η * δ := by
          rw [div_le_iff₀ hu_pos]; nlinarith [mul_pos hη hδ]
        linarith
      have hlog_le : Real.log (1 + ST / δ ^ 2) ≤ 4 * Real.sqrt u := by
        have h1 : 1 + ST / δ ^ 2 = u ^ 2 := hu_sq.symm
        rw [h1, Real.log_pow]
        have h2 : Real.log u = 2 * Real.log (Real.sqrt u) := by
          rw [Real.log_sqrt (le_of_lt hu_pos)]; ring
        have h3 : Real.log (Real.sqrt u) ≤ Real.sqrt u - 1 :=
          Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hu_pos)
        push_cast
        linarith
      have hamgm : 4 * C2 * Real.sqrt u ≤ (η * δ / 2) * u + 8 * C2 ^ 2 / (η * δ) := by
        have hsq : 0 ≤ (η * δ * Real.sqrt u - 4 * C2) ^ 2 := sq_nonneg _
        have hsq2 : Real.sqrt u ^ 2 = u := Real.sq_sqrt (le_of_lt hu_pos)
        have h1 : 8 * (η * δ) * C2 * Real.sqrt u ≤ (η * δ) ^ 2 * u + 16 * C2 ^ 2 := by
          have hexp : (η * δ * Real.sqrt u - 4 * C2) ^ 2 =
              (η * δ) ^ 2 * u - 8 * (η * δ) * C2 * Real.sqrt u + 16 * C2 ^ 2 := by
            nlinarith [hsq2]
          linarith
        have h2 : 0 < 2 * (η * δ) := by positivity
        have h3 : (4 * C2 * Real.sqrt u) * (2 * (η * δ)) ≤
            ((η * δ / 2) * u + 8 * C2 ^ 2 / (η * δ)) * (2 * (η * δ)) := by
          have hr : ((η * δ / 2) * u + 8 * C2 ^ 2 / (η * δ)) * (2 * (η * δ)) =
              (η * δ) ^ 2 * u + 16 * C2 ^ 2 := by
            field_simp [ne_of_gt hη, ne_of_gt hδ]
            ring
          rw [hr]
          linarith
        exact le_of_mul_le_mul_right h3 h2
      have hcomb : η * δ * u - η * δ ≤ C1 + C2 * (4 * Real.sqrt u) := by
        have hA : η * (ST / Real.sqrt (δ ^ 2 + ST)) ≤ C1 + C2 * Real.log (1 + ST / δ ^ 2) :=
          le_trans (mul_le_mul_of_nonneg_left hsum_low (le_of_lt hη)) hsum_desc
        have hB : C2 * Real.log (1 + ST / δ ^ 2) ≤ C2 * (4 * Real.sqrt u) :=
          mul_le_mul_of_nonneg_left hlog_le hC2
        linarith
      have hu_le : u ≤ U := by
        dsimp only [U]
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < η * δ / 2)]
        linarith
      have hu_sq_le : u ^ 2 ≤ U ^ 2 := sq_le_sq' (by linarith) hu_le
      rw [hST_eq]
      nlinarith [sq_pos_of_pos hδ]
  exact summable_of_sum_range_le (fun _ => sq_nonneg _) hS_bdd

/-! ### Part 6: Quasi-Fejér monotonicity and `(3) ⇒ (1)` -/

/-- Variable-metric quasi-Fejér scalar convergence lemma:
if `a_k ≥ 0`, `ρ_k ≥ 0`, `ε_k ≥ 0`, `Summable ρ`, `Summable ε`, and
`a (k+1) ≤ (1 + ρ k) * a k + ε k` for all `k`, then `(a_k)` converges! -/
private lemma quasi_fejer_converges {a ρ ε : ℕ → ℝ}
    (ha : ∀ k, 0 ≤ a k) (hρ : ∀ k, 0 ≤ ρ k) (hε : ∀ k, 0 ≤ ε k)
    (hρ_sum : Summable ρ) (hε_sum : Summable ε)
    (hrec : ∀ k, a (k + 1) ≤ (1 + ρ k) * a k + ε k) :
    ∃ L : ℝ, Filter.Tendsto a Filter.atTop (nhds L) := by
  let P : ℕ → ℝ := fun k => ∏ j ∈ Finset.range k, (1 + ρ j)
  have hP_ge1 : ∀ k, 1 ≤ P k := by
    intro k
    exact Finset.one_le_prod (fun j _ => by linarith [hρ j])
  have hP_pos : ∀ k, 0 < P k := fun k => lt_of_lt_of_le zero_lt_one (hP_ge1 k)
  have hP_mono : Monotone P := by
    refine monotone_nat_of_le_succ (fun k => ?_)
    dsimp only [P]
    rw [Finset.prod_range_succ]
    have h1 : 1 ≤ 1 + ρ k := by linarith [hρ k]
    nlinarith [hP_pos k]
  have hP_bdd : BddAbove (Set.range P) := by
    refine ⟨Real.exp (∑' j, ρ j), ?_⟩
    rintro _ ⟨k, rfl⟩
    calc
      P k = ∏ j ∈ Finset.range k, (1 + ρ j) := rfl
      _ ≤ ∏ j ∈ Finset.range k, Real.exp (ρ j) :=
        Finset.prod_le_prod (fun j _ => by linarith [hρ j]) (fun j _ => by linarith [Real.add_one_le_exp (ρ j)])
      _ = Real.exp (∑ j ∈ Finset.range k, ρ j) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (∑' j, ρ j) :=
        Real.exp_le_exp.mpr (hρ_sum.sum_le_tsum (Finset.range k) (fun j _ => hρ j))
  obtain ⟨Pinf, hP_lim⟩ : ∃ Pinf, Filter.Tendsto P Filter.atTop (nhds Pinf) :=
    ⟨⨆ k, P k, tendsto_atTop_ciSup hP_mono hP_bdd⟩
  let Sε : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k, ε j
  have hSε_lim : Filter.Tendsto Sε Filter.atTop (nhds (∑' j, ε j)) :=
    hε_sum.hasSum.tendsto_sum_nat
  let c : ℕ → ℝ := fun k => a k / P k - Sε k
  have hc_anti : Antitone c := by
    refine antitone_nat_of_succ_le (fun k => ?_)
    dsimp only [c, Sε]
    rw [Finset.sum_range_succ]
    have hPsucc : P (k + 1) = P k * (1 + ρ k) := Finset.prod_range_succ _ k
    have h1 : a (k + 1) / P (k + 1) ≤ a k / P k + ε k / P (k + 1) := by
      rw [div_le_iff₀ (hP_pos (k + 1))]
      have hr : (a k / P k + ε k / P (k + 1)) * P (k + 1) = (1 + ρ k) * a k + ε k := by
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt (hP_pos (k + 1))), hPsucc]
        field_simp [ne_of_gt (hP_pos k)]
      rw [hr]
      exact hrec k
    have h2 : ε k / P (k + 1) ≤ ε k :=
      div_le_self (hε k) (hP_ge1 (k + 1))
    linarith
  have hc_bdd : BddBelow (Set.range c) := by
    refine ⟨-(∑' j, ε j), ?_⟩
    rintro _ ⟨k, rfl⟩
    dsimp only [c, Sε]
    have h1 : 0 ≤ a k / P k := div_nonneg (ha k) (le_of_lt (hP_pos k))
    have h2 : ∑ j ∈ Finset.range k, ε j ≤ ∑' j, ε j :=
      hε_sum.sum_le_tsum (Finset.range k) (fun j _ => hε j)
    linarith
  obtain ⟨cinf, hc_lim⟩ : ∃ cinf, Filter.Tendsto c Filter.atTop (nhds cinf) :=
    ⟨⨅ k, c k, tendsto_atTop_ciInf hc_anti hc_bdd⟩
  refine ⟨Pinf * (cinf + ∑' j, ε j), ?_⟩
  have hdiv_lim : Filter.Tendsto (fun k => a k / P k) Filter.atTop (nhds (cinf + ∑' j, ε j)) := by
    have h := hc_lim.add hSε_lim
    refine h.congr (fun k => ?_)
    dsimp only [c]; ring
  have hmul := hP_lim.mul hdiv_lim
  refine hmul.congr (fun k => ?_)
  exact mul_div_cancel₀ (a k) (ne_of_gt (hP_pos k))

private lemma summable_implies_convergent {n : ℕ} (variant : AdaGradVariant)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (grad : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hf_grad : ∀ y, HasGradientAt f (grad y) y)
    (hgrad_ll : LocallyLipschitz grad)
    (hmin : ∃ z : EuclideanSpace ℝ (Fin n), ∀ y, f z ≤ f y)
    (hada : IsAdaGradSeq variant grad δ η x)
    (hsum : Summable (fun k => ‖grad (x k)‖ ^ 2)) :
    ∃ xStar : EuclideanSpace ℝ (Fin n),
      (∀ y, f xStar ≤ f y) ∧ Filter.Tendsto x Filter.atTop (nhds xStar) := by
  choose Γ hΓ_pd hΓ_sq hstep_x using hada
  -- Define `W 0 = δ I`, `W (k + 1) = (Γ k)⁻¹`
  let W : ℕ → Matrix (Fin n) (Fin n) ℝ := fun m =>
    match m with
    | 0 => δ • (1 : Matrix (Fin n) (Fin n) ℝ)
    | k + 1 => (Γ k)⁻¹
  have hW_pd : ∀ m, (W m).PosDef := by
    intro m
    cases m with
    | zero =>
      refine posDef_of_quad_pos (by ext i j; by_cases h : i = j <;> simp [W, Matrix.conjTranspose_apply, h, eq_comm]) (fun u hu => ?_)
      change 0 < dotProduct u ((δ • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec u)
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
      have hu' : WithLp.toLp 2 u ≠ 0 := fun h => hu (congrArg WithLp.ofLp h)
      have hpos : 0 < ‖WithLp.toLp 2 u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu')
      rw [← dotProduct_self_eq_norm_sq] at hpos
      exact mul_pos hδ hpos
    | succ k => exact posDef_inv (hΓ_pd k)
  have hW_sq : ∀ m, W m * W m = adaGradMatrixExt variant grad δ x m := by
    intro m
    cases m with
    | zero =>
      simp only [W, adaGradMatrixExt, Matrix.mul_smul, smul_smul, Matrix.mul_one, sq]
    | succ k =>
      dsimp only [W, adaGradMatrixExt]
      have h1 : (Γ k)⁻¹ * (Γ k)⁻¹ * (Γ k * Γ k) = 1 := by
        calc
          (Γ k)⁻¹ * (Γ k)⁻¹ * (Γ k * Γ k) = (Γ k)⁻¹ * ((Γ k)⁻¹ * Γ k) * Γ k := by
            simp only [Matrix.mul_assoc]
          _ = (Γ k)⁻¹ * 1 * Γ k := by rw [posDef_inv_mul_self (hΓ_pd k)]
          _ = 1 := by rw [Matrix.mul_one, posDef_inv_mul_self (hΓ_pd k)]
      calc
        (Γ k)⁻¹ * (Γ k)⁻¹
            = ((Γ k)⁻¹ * (Γ k)⁻¹) * (Γ k * Γ k * adaGradMatrix variant grad δ x k) := by
          rw [hΓ_sq k, Matrix.mul_one]
        _ = ((Γ k)⁻¹ * (Γ k)⁻¹ * (Γ k * Γ k)) * adaGradMatrix variant grad δ x k := by
          simp only [Matrix.mul_assoc]
        _ = adaGradMatrix variant grad δ x k := by rw [h1, Matrix.one_mul]
  have hW_low : ∀ m (u : EuclideanSpace ℝ (Fin n)),
      δ * ‖u‖ ^ 2 ≤ dotProduct u.ofLp ((W m).mulVec u.ofLp) := by
    intro m
    have h := posDef_sqrt_lower (hW_pd m) (m := δ ^ 2) (fun u => by
      rw [hW_sq m]
      cases m with
      | zero =>
        simp [adaGradMatrixExt, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
          dotProduct_self_eq_norm_sq]
      | succ k => exact adaGradMatrix_quad_lower variant grad δ x k u)
    simpa [Real.sqrt_sq (le_of_lt hδ)] using h
  have hΓ_up : ∀ k (u : EuclideanSpace ℝ (Fin n)),
      dotProduct u.ofLp ((Γ k).mulVec u.ofLp) ≤ (1 / δ) * ‖u‖ ^ 2 := by
    intro k
    have h := posDef_inv_upper (hW_pd (k + 1)) hδ (hW_low (k + 1))
    have hinv : (W (k + 1))⁻¹ = Γ k :=
      Matrix.nonsing_inv_nonsing_inv (Γ k) (posDef_isUnit_det (hΓ_pd k))
    simpa [hinv] using h
  have hW_diff : ∀ k (u : EuclideanSpace ℝ (Fin n)),
      |dotProduct u.ofLp ((W (k + 1) - W k).mulVec u.ofLp)| ≤
        (‖grad (x k)‖ ^ 2 / (2 * δ)) * ‖u‖ ^ 2 := by
    intro k
    refine sqrt_diff_quad_bound (hW_pd (k + 1)) (hW_pd k) hδ (hW_low (k + 1)) (hW_low k) (fun u => ?_)
    rw [hW_sq (k + 1), hW_sq k]
    exact adaGradMatrixExt_diff_bound variant grad δ x k u
  -- Variable-metric quasi-Fejér monotonicity for EVERY `z ∈ argmin f`!
  have hfejer : ∀ z : EuclideanSpace ℝ (Fin n), (∀ y, f z ≤ f y) →
      ∃ Lz : ℝ, Filter.Tendsto
        (fun k => dotProduct (x k - z).ofLp ((W k).mulVec (x k - z).ofLp))
        Filter.atTop (nhds Lz) := by
    intro z hz
    let a : ℕ → ℝ := fun k => dotProduct (x k - z).ofLp ((W k).mulVec (x k - z).ofLp)
    let ρ : ℕ → ℝ := fun k => ‖grad (x k)‖ ^ 2 / (2 * δ ^ 2)
    let ε : ℕ → ℝ := fun k => (η ^ 2 / δ) * ‖grad (x k)‖ ^ 2
    refine quasi_fejer_converges (a := a) (ρ := ρ) (ε := ε) ?_ ?_ ?_ ?_ ?_ ?_
    · intro k; exact le_trans (mul_nonneg (le_of_lt hδ) (sq_nonneg _)) (hW_low k (x k - z))
    · intro k; exact div_nonneg (sq_nonneg _) (by positivity)
    · intro k; exact mul_nonneg (by positivity) (sq_nonneg _)
    · exact hsum.div_const (2 * δ ^ 2)
    · exact hsum.mul_left (η ^ 2 / δ)
    · intro k
      -- Expand `a (k + 1) = ⟨x (k+1) - z, W (k+1) (x (k+1) - z)⟩`
      let d : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 ((Γ k).mulVec (grad (x k)).ofLp)
      have hsub : x (k + 1) - z = (x k - z) - η • d := by
        rw [hstep_x k]; abel
      have hWd : (W (k + 1)).mulVec d.ofLp = (grad (x k)).ofLp := by
        change (Γ k)⁻¹.mulVec ((Γ k).mulVec (grad (x k)).ofLp) = (grad (x k)).ofLp
        rw [Matrix.mulVec_mulVec, posDef_inv_mul_self (hΓ_pd k), Matrix.one_mulVec]
      have hexp : a (k + 1) =
          dotProduct (x k - z).ofLp ((W (k + 1)).mulVec (x k - z).ofLp)
          - 2 * η * inner ℝ (grad (x k)) (x k - z)
          + η ^ 2 * dotProduct (grad (x k)).ofLp ((Γ k).mulVec (grad (x k)).ofLp) := by
        dsimp only [a]
        rw [hsub]
        have h1 : ((x k - z) - η • d).ofLp = (x k - z).ofLp - η • d.ofLp := rfl
        rw [h1]
        simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
          smul_dotProduct, dotProduct_smul, smul_eq_mul]
        have hcross1 : dotProduct (x k - z).ofLp ((W (k + 1)).mulVec d.ofLp) =
            inner ℝ (grad (x k)) (x k - z) := by
          rw [hWd, dotProduct_comm, dotProduct_eq_inner]
        have hcross2 : dotProduct d.ofLp ((W (k + 1)).mulVec (x k - z).ofLp) =
            inner ℝ (grad (x k)) (x k - z) := by
          rw [herm_dotProduct_mulVec_comm (hW_pd (k + 1)).1, hWd, dotProduct_eq_inner]
        have hquad_d : dotProduct d.ofLp ((W (k + 1)).mulVec d.ofLp) =
            dotProduct (grad (x k)).ofLp ((Γ k).mulVec (grad (x k)).ofLp) := by
          rw [hWd, dotProduct_comm]
        rw [hcross1, hcross2, hquad_d]
        ring
      -- Bound each of the 3 pieces:
      have hconv : 0 ≤ inner ℝ (grad (x k)) (x k - z) := by
        have h := convex_first_order hf_conv hf_grad (x k) z
        have hneg : z - x k = -(x k - z) := by abel
        rw [hneg, inner_neg_right] at h
        linarith [hz (x k)]
      have hconv_term : 0 ≤ 2 * η * inner ℝ (grad (x k)) (x k - z) :=
        mul_nonneg (by positivity) hconv
      have hquad_bound : dotProduct (grad (x k)).ofLp ((Γ k).mulVec (grad (x k)).ofLp) ≤
          (1 / δ) * ‖grad (x k)‖ ^ 2 := hΓ_up k (grad (x k))
      have hW_step : dotProduct (x k - z).ofLp ((W (k + 1)).mulVec (x k - z).ofLp) ≤
          (1 + ρ k) * a k := by
        have hdiff_eq : dotProduct (x k - z).ofLp ((W (k + 1)).mulVec (x k - z).ofLp) - a k =
            dotProduct (x k - z).ofLp ((W (k + 1) - W k).mulVec (x k - z).ofLp) := by
          dsimp only [a]; rw [Matrix.sub_mulVec, dotProduct_sub]
        have hle1 : dotProduct (x k - z).ofLp ((W (k + 1) - W k).mulVec (x k - z).ofLp) ≤
            (‖grad (x k)‖ ^ 2 / (2 * δ)) * ‖x k - z‖ ^ 2 :=
          le_trans (le_abs_self _) (hW_diff k (x k - z))
        have hle2 : (‖grad (x k)‖ ^ 2 / (2 * δ)) * ‖x k - z‖ ^ 2 ≤ ρ k * a k := by
          have hlow := hW_low k (x k - z)
          have h1 : ‖x k - z‖ ^ 2 ≤ a k / δ := (le_div_iff₀ hδ).mpr (by dsimp only [a]; linarith)
          calc
            (‖grad (x k)‖ ^ 2 / (2 * δ)) * ‖x k - z‖ ^ 2
                ≤ (‖grad (x k)‖ ^ 2 / (2 * δ)) * (a k / δ) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = ρ k * a k := by dsimp only [ρ]; ring
        linarith
      have hε_bound : η ^ 2 * dotProduct (grad (x k)).ofLp ((Γ k).mulVec (grad (x k)).ofLp) ≤ ε k := by
        dsimp only [ε]
        have := mul_le_mul_of_nonneg_left hquad_bound (sq_nonneg η)
        linarith [show η ^ 2 * ((1 / δ) * ‖grad (x k)‖ ^ 2) = (η ^ 2 / δ) * ‖grad (x k)‖ ^ 2 by ring]
      linarith
  -- Step 1: `x` is bounded (from `hfejer` at any `z0 ∈ argmin f`)
  obtain ⟨z0, hz0⟩ := hmin
  obtain ⟨Lz0, hLz0⟩ := hfejer z0 hz0
  have hB0_ex : ∃ B0 : ℝ, ∀ k, dotProduct (x k - z0).ofLp ((W k).mulVec (x k - z0).ofLp) ≤ B0 := by
    have hev : ∀ᶠ k in Filter.atTop,
        dotProduct (x k - z0).ofLp ((W k).mulVec (x k - z0).ofLp) ≤ Lz0 + 1 :=
      hLz0.eventually (ge_mem_nhds (by linarith))
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    let B0 := max (Lz0 + 1) ((Finset.range (N + 1)).sup' (by simp)
      (fun k => dotProduct (x k - z0).ofLp ((W k).mulVec (x k - z0).ofLp)))
    refine ⟨B0, fun k => ?_⟩
    by_cases hk : N ≤ k
    · exact le_trans (hN k hk) (le_max_left _ _)
    · exact le_trans (Finset.le_sup'
        (fun j => dotProduct (x j - z0).ofLp ((W j).mulVec (x j - z0).ofLp))
        (Finset.mem_range.mpr (by omega))) (le_max_right _ _)
  obtain ⟨B0, hB0⟩ := hB0_ex
  have hx_bdd_dist : ∃ R : ℝ, ∀ k, ‖x k‖ ≤ R := by
    refine ⟨‖z0‖ + Real.sqrt (max B0 0 / δ), fun k => ?_⟩
    have ha : dotProduct (x k - z0).ofLp ((W k).mulVec (x k - z0).ofLp) ≤ max B0 0 :=
      le_trans (hB0 k) (le_max_left _ _)
    have hnorm_sq : ‖x k - z0‖ ^ 2 ≤ max B0 0 / δ :=
      (le_div_iff₀ hδ).mpr (by linarith [hW_low k (x k - z0)])
    have hnorm : ‖x k - z0‖ ≤ Real.sqrt (max B0 0 / δ) := by
      have := Real.sqrt_le_sqrt hnorm_sq
      rwa [Real.sqrt_sq (norm_nonneg _)] at this
    calc
      ‖x k‖ = ‖(x k - z0) + z0‖ := by abel_nf
      _ ≤ ‖x k - z0‖ + ‖z0‖ := norm_add_le _ _
      _ ≤ ‖z0‖ + Real.sqrt (max B0 0 / δ) := by linarith
  obtain ⟨R, hR⟩ := hx_bdd_dist
  -- Step 2: `W k` converges to a symmetric matrix `Winf` with `δ ‖u‖^2 ≤ ⟨u, Winf u⟩`!
  -- Show each quadratic form `k ↦ ⟨u, W k u⟩` is Cauchy, hence each entry `(W k) i j` converges!
  have hW_quad_cauchy : ∀ u : EuclideanSpace ℝ (Fin n),
      ∃ L : ℝ, Filter.Tendsto (fun k => dotProduct u.ofLp ((W k).mulVec u.ofLp)) Filter.atTop (nhds L) := by
    intro u
    have hdiff_sum : Summable (fun k =>
        dotProduct u.ofLp ((W (k + 1)).mulVec u.ofLp) - dotProduct u.ofLp ((W k).mulVec u.ofLp)) := by
      refine Summable.of_norm_bounded (g := fun k => (‖grad (x k)‖ ^ 2 / (2 * δ)) * ‖u‖ ^ 2)
        ((hsum.div_const (2 * δ)).mul_right (‖u‖ ^ 2)) (fun k => ?_)
      rw [Real.norm_eq_abs, ← dotProduct_sub, ← Matrix.sub_mulVec]
      exact hW_diff k u
    have hlim := hdiff_sum.hasSum.tendsto_sum_nat
    refine ⟨dotProduct u.ofLp ((W 0).mulVec u.ofLp) +
        ∑' k, (dotProduct u.ofLp ((W (k + 1)).mulVec u.ofLp) - dotProduct u.ofLp ((W k).mulVec u.ofLp)), ?_⟩
    have hconst := tendsto_const_nhds (x := dotProduct u.ofLp ((W 0).mulVec u.ofLp)) (f := (Filter.atTop : Filter ℕ))
    refine (hconst.add hlim).congr (fun N => ?_)
    rw [Finset.sum_range_sub (fun k => dotProduct u.ofLp ((W k).mulVec u.ofLp)) N]
    ring
  -- Extract entrywise limit `Winf` via polarization on standard basis vectors `e i`
  let eb : Fin n → EuclideanSpace ℝ (Fin n) := fun i => EuclideanSpace.single i (1 : ℝ)
  have heb_dot : ∀ (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (i j : Fin n),
      A i j = (dotProduct (eb i + eb j).ofLp (A.mulVec (eb i + eb j).ofLp)
        - dotProduct (eb i).ofLp (A.mulVec (eb i).ofLp)
        - dotProduct (eb j).ofLp (A.mulVec (eb j).ofLp)) / 2 := by
    intro A hA i j
    have hmul : ∀ a b : Fin n, dotProduct (eb a).ofLp (A.mulVec (eb b).ofLp) = A a b := by
      intro a b
      simp only [eb, dotProduct, Matrix.mulVec, PiLp.single_apply]
      rw [Finset.sum_eq_single a]
      · rw [if_pos rfl, one_mul, Finset.sum_eq_single b]
        · simp
        · intro c _ hcb; simp [hcb]
        · intro hb; exact absurd (Finset.mem_univ b) hb
      · intro c _ hca; simp [hca]
      · intro ha; exact absurd (Finset.mem_univ a) ha
    have hsym : A j i = A i j := by
      have := congrFun (congrFun (herm_transpose_eq hA) i) j
      simpa [Matrix.transpose_apply] using this
    have hexp : dotProduct (eb i + eb j).ofLp (A.mulVec (eb i + eb j).ofLp) =
        A i i + A i j + A j i + A j j := by
      have h1 : (eb i + eb j).ofLp = (eb i).ofLp + (eb j).ofLp := rfl
      rw [h1, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
        hmul i i, hmul i j, hmul j i, hmul j j]
      ring
    rw [hexp, hmul i i, hmul j j, hsym]
    ring
  have hW_entry_lim : ∀ i j : Fin n, ∃ L : ℝ, Filter.Tendsto (fun k => W k i j) Filter.atTop (nhds L) := by
    intro i j
    obtain ⟨Lij, hLij⟩ := hW_quad_cauchy (eb i + eb j)
    obtain ⟨Li, hLi⟩ := hW_quad_cauchy (eb i)
    obtain ⟨Lj, hLj⟩ := hW_quad_cauchy (eb j)
    refine ⟨(Lij - Li - Lj) / 2, ?_⟩
    refine (((hLij.sub hLi).sub hLj).div_const 2).congr (fun k => ?_)
    exact (heb_dot (W k) (hW_pd k).1 i j).symm
  choose Winf_fn hWinf using hW_entry_lim
  let Winf : Matrix (Fin n) (Fin n) ℝ := Matrix.of Winf_fn
  have hWinf_herm : Winf.IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    have h1 : Filter.Tendsto (fun k => W k j i) Filter.atTop (nhds (Winf j i)) := hWinf j i
    have h2 : Filter.Tendsto (fun k => W k i j) Filter.atTop (nhds (Winf i j)) := hWinf i j
    have heq : ∀ k, W k j i = W k i j := fun k => by
      have := congrFun (congrFun (herm_transpose_eq (hW_pd k).1) i) j
      simpa [Matrix.transpose_apply] using this
    exact tendsto_nhds_unique h1 (h2.congr (fun k => (heq k).symm))
  have hWinf_low : ∀ u : EuclideanSpace ℝ (Fin n),
      δ * ‖u‖ ^ 2 ≤ dotProduct u.ofLp (Winf.mulVec u.ofLp) := by
    intro u
    have hlim : Filter.Tendsto (fun k => dotProduct u.ofLp ((W k).mulVec u.ofLp))
        Filter.atTop (nhds (dotProduct u.ofLp (Winf.mulVec u.ofLp))) := by
      simp only [dotProduct, Matrix.mulVec]
      exact tendsto_finsetSum _ (fun i _ => tendsto_const_nhds.mul
        (tendsto_finsetSum _ (fun j _ => (hWinf i j).mul tendsto_const_nhds)))
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall (fun k => hW_low k u))
  -- Also `⟨x k - z, (W k - Winf) (x k - z)⟩ → 0` for any `z`, hence `⟨x k - z, Winf (x k - z)⟩` converges for every `z ∈ argmin f`!
  have hWinf_fejer : ∀ z : EuclideanSpace ℝ (Fin n), (∀ y, f z ≤ f y) →
      ∃ Lz : ℝ, Filter.Tendsto
        (fun k => dotProduct (x k - z).ofLp (Winf.mulVec (x k - z).ofLp))
        Filter.atTop (nhds Lz) := by
    intro z hz
    obtain ⟨Lz, hLz⟩ := hfejer z hz
    refine ⟨Lz, ?_⟩
    have hdiff_zero : Filter.Tendsto
        (fun k => dotProduct (x k - z).ofLp ((W k).mulVec (x k - z).ofLp) -
          dotProduct (x k - z).ofLp (Winf.mulVec (x k - z).ofLp)) Filter.atTop (nhds 0) := by
      -- Bound `|⟨u_k, (W k - Winf) u_k⟩| ≤ (∑ i j, |W k i j - Winf i j|) * (R + ‖z‖)^2 → 0`
      have hM : ∀ k i, |(x k - z).ofLp i| ≤ R + ‖z‖ := by
        intro k i
        have hi : |(x k - z).ofLp i| ≤ ‖x k - z‖ := PiLp.norm_apply_le (x k - z) i
        calc
          |(x k - z).ofLp i| ≤ ‖x k - z‖ := hi
          _ ≤ ‖x k‖ + ‖z‖ := norm_sub_le _ _
          _ ≤ R + ‖z‖ := by linarith [hR k]
      have hRznn : 0 ≤ R + ‖z‖ := by
        linarith [norm_nonneg (x 0), hR 0, norm_nonneg z]
      have hupper_tendsto : Filter.Tendsto
          (fun k => (∑ i : Fin n, ∑ j : Fin n, |W k i j - Winf i j|) * (R + ‖z‖) ^ 2)
          Filter.atTop (nhds 0) := by
        have h0 : Filter.Tendsto (fun k => ∑ i : Fin n, ∑ j : Fin n, |W k i j - Winf i j|)
            Filter.atTop (nhds 0) := by
          have : (0 : ℝ) = ∑ _i : Fin n, ∑ _j : Fin n, (0 : ℝ) := by simp
          rw [this]
          refine tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ => ?_))
          simpa [Winf] using ((hWinf i j).sub (tendsto_const_nhds (x := Winf_fn i j))).abs
        simpa using h0.mul_const ((R + ‖z‖) ^ 2)
      refine squeeze_zero_norm (a := fun k => (∑ i : Fin n, ∑ j : Fin n, |W k i j - Winf i j|) * (R + ‖z‖) ^ 2)
        (fun k => ?_) hupper_tendsto
      rw [Real.norm_eq_abs, ← dotProduct_sub, ← Matrix.sub_mulVec]
      simp only [dotProduct, Matrix.mulVec, Matrix.sub_apply, Finset.mul_sum]
      calc
        |∑ i : Fin n, ∑ j : Fin n, (x k - z).ofLp i * ((W k i j - Winf i j) * (x k - z).ofLp j)|
            ≤ ∑ i : Fin n, |∑ j : Fin n, (x k - z).ofLp i * ((W k i j - Winf i j) * (x k - z).ofLp j)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin n, ∑ j : Fin n, |(x k - z).ofLp i * ((W k i j - Winf i j) * (x k - z).ofLp j)| :=
          Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
        _ ≤ ∑ i : Fin n, ∑ j : Fin n, |W k i j - Winf i j| * (R + ‖z‖) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
          rw [abs_mul, abs_mul]
          have h1 : |(x k - z).ofLp i| * |(x k - z).ofLp j| ≤ (R + ‖z‖) ^ 2 := by
            rw [sq]; exact mul_le_mul (hM k i) (hM k j) (abs_nonneg _) hRznn
          calc
            |(x k - z).ofLp i| * (|W k i j - Winf i j| * |(x k - z).ofLp j|)
                = |W k i j - Winf i j| * (|(x k - z).ofLp i| * |(x k - z).ofLp j|) := by ring
            _ ≤ |W k i j - Winf i j| * (R + ‖z‖) ^ 2 :=
              mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = (∑ i : Fin n, ∑ j : Fin n, |W k i j - Winf i j|) * (R + ‖z‖) ^ 2 := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => (Finset.sum_mul _ _ _).symm)
    have h := hLz.sub hdiff_zero
    simpa using h
  -- Step 3: Every cluster point of `x` is in `argmin f`!
  have hgrad_zero : Filter.Tendsto (fun k => grad (x k)) Filter.atTop (nhds 0) := by
    have hnorm_sq : Filter.Tendsto (fun k => ‖grad (x k)‖ ^ 2) Filter.atTop (nhds 0) :=
      hsum.tendsto_atTop_zero
    have hnorm : Filter.Tendsto (fun k => ‖grad (x k)‖) Filter.atTop (nhds 0) := by
      have := hnorm_sq.sqrt
      simpa [Real.sqrt_sq (norm_nonneg _)] using this
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hcluster_min : ∀ (xStar : EuclideanSpace ℝ (Fin n)) (φ : ℕ → ℕ),
      StrictMono φ → Filter.Tendsto (x ∘ φ) Filter.atTop (nhds xStar) →
      ∀ y, f xStar ≤ f y := by
    intro xStar φ hφ hlim y
    have hg1 : Filter.Tendsto (fun k => grad (x (φ k))) Filter.atTop (nhds (grad xStar)) :=
      (hgrad_ll.continuous.tendsto xStar).comp hlim
    have hg2 : Filter.Tendsto (fun k => grad (x (φ k))) Filter.atTop (nhds 0) :=
      hgrad_zero.comp hφ.tendsto_atTop
    have hg0 : grad xStar = 0 := tendsto_nhds_unique hg1 hg2
    have hconv := convex_first_order hf_conv hf_grad xStar y
    rw [hg0, inner_zero_left, add_zero] at hconv
    exact hconv
  -- Step 4: Extract one cluster point `xStar` from compactness of `closedBall 0 R`
  have hR_nn : 0 ≤ R := le_trans (norm_nonneg _) (hR 0)
  have hx_mem : ∀ k, x k ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := fun k => by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hR k
  obtain ⟨xStar, _, φ, hφ, hlim_xStar⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).tendsto_subseq hx_mem
  have hxStar_min : ∀ y, f xStar ≤ f y := hcluster_min xStar φ hφ hlim_xStar
  -- Step 5: Opial uniqueness ⇒ full sequence `x k → xStar`!
  refine ⟨xStar, hxStar_min, ?_⟩
  by_contra hnot
  rw [Metric.tendsto_atTop] at hnot
  push Not at hnot
  obtain ⟨ε, hε, hbad⟩ := hnot
  -- Build a strictly increasing subsequence `ψ` with `dist (x (ψ k)) xStar ≥ ε`
  have hψ_exists : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ k, ε ≤ dist (x (ψ k)) xStar := by
    choose next hnext_ge hnext_dist using hbad
    let ψ : ℕ → ℕ := Nat.rec (next 0) (fun _ prev => next (prev + 1))
    refine ⟨ψ, strictMono_nat_of_lt_succ (fun k => ?_), fun k => ?_⟩
    · exact Nat.lt_of_succ_le (hnext_ge (ψ k + 1))
    · cases k with
      | zero => exact hnext_dist 0
      | succ k' => exact hnext_dist (ψ k' + 1)
  obtain ⟨ψ, hψ, hψ_dist⟩ := hψ_exists
  obtain ⟨yStar, _, τ, hτ, hlim_yStar⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).tendsto_subseq (fun k => hx_mem (ψ k))
  have hψτ_mono : StrictMono (ψ ∘ τ) := hψ.comp hτ
  have hlim_yStar' : Filter.Tendsto (x ∘ (ψ ∘ τ)) Filter.atTop (nhds yStar) := hlim_yStar
  have hyStar_min : ∀ y, f yStar ≤ f y := hcluster_min yStar (ψ ∘ τ) hψτ_mono hlim_yStar'
  have hne : yStar ≠ xStar := by
    have hdist_lim : Filter.Tendsto (fun k => dist (x (ψ (τ k))) xStar) Filter.atTop (nhds (dist yStar xStar)) :=
      hlim_yStar'.dist tendsto_const_nhds
    have hge : ε ≤ dist yStar xStar :=
      ge_of_tendsto hdist_lim (Filter.Eventually.of_forall (fun k => hψ_dist (τ k)))
    intro heq; rw [heq, dist_self] at hge; linarith
  -- Compare limits of `⟨x k - xStar, Winf (x k - xStar)⟩ - ⟨x k - yStar, Winf (x k - yStar)⟩`
  obtain ⟨Lx, hLx⟩ := hWinf_fejer xStar hxStar_min
  obtain ⟨Ly, hLy⟩ := hWinf_fejer yStar hyStar_min
  have hdiff_lim : Filter.Tendsto
      (fun k => dotProduct (x k - xStar).ofLp (Winf.mulVec (x k - xStar).ofLp) -
        dotProduct (x k - yStar).ofLp (Winf.mulVec (x k - yStar).ofLp))
      Filter.atTop (nhds (Lx - Ly)) := hLx.sub hLy
  have hquad_cont : Continuous (fun u : EuclideanSpace ℝ (Fin n) =>
      dotProduct u.ofLp (Winf.mulVec u.ofLp)) := by
    simp only [dotProduct, Matrix.mulVec]
    exact continuous_finsetSum _ (fun i _ => (EuclideanSpace.proj i).continuous.mul
      (continuous_finsetSum _ (fun j _ => continuous_const.mul (EuclideanSpace.proj j).continuous)))
  have hlim1 : Lx - Ly =
      dotProduct (xStar - xStar).ofLp (Winf.mulVec (xStar - xStar).ofLp) -
      dotProduct (xStar - yStar).ofLp (Winf.mulVec (xStar - yStar).ofLp) := by
    have hA : Filter.Tendsto
        (fun k => dotProduct (x (φ k) - xStar).ofLp (Winf.mulVec (x (φ k) - xStar).ofLp) -
          dotProduct (x (φ k) - yStar).ofLp (Winf.mulVec (x (φ k) - yStar).ofLp))
        Filter.atTop (nhds (Lx - Ly)) := hdiff_lim.comp hφ.tendsto_atTop
    have hB : Filter.Tendsto
        (fun k => dotProduct (x (φ k) - xStar).ofLp (Winf.mulVec (x (φ k) - xStar).ofLp) -
          dotProduct (x (φ k) - yStar).ofLp (Winf.mulVec (x (φ k) - yStar).ofLp))
        Filter.atTop (nhds (dotProduct (xStar - xStar).ofLp (Winf.mulVec (xStar - xStar).ofLp) -
          dotProduct (xStar - yStar).ofLp (Winf.mulVec (xStar - yStar).ofLp))) :=
      (hquad_cont.tendsto _).comp (hlim_xStar.sub tendsto_const_nhds) |>.sub
        ((hquad_cont.tendsto _).comp (hlim_xStar.sub tendsto_const_nhds))
    exact tendsto_nhds_unique hA hB
  have hlim2 : Lx - Ly =
      dotProduct (yStar - xStar).ofLp (Winf.mulVec (yStar - xStar).ofLp) -
      dotProduct (yStar - yStar).ofLp (Winf.mulVec (yStar - yStar).ofLp) := by
    have hA : Filter.Tendsto
        (fun k => dotProduct (x (ψ (τ k)) - xStar).ofLp (Winf.mulVec (x (ψ (τ k)) - xStar).ofLp) -
          dotProduct (x (ψ (τ k)) - yStar).ofLp (Winf.mulVec (x (ψ (τ k)) - yStar).ofLp))
        Filter.atTop (nhds (Lx - Ly)) := hdiff_lim.comp hψτ_mono.tendsto_atTop
    have hB : Filter.Tendsto
        (fun k => dotProduct (x (ψ (τ k)) - xStar).ofLp (Winf.mulVec (x (ψ (τ k)) - xStar).ofLp) -
          dotProduct (x (ψ (τ k)) - yStar).ofLp (Winf.mulVec (x (ψ (τ k)) - yStar).ofLp))
        Filter.atTop (nhds (dotProduct (yStar - xStar).ofLp (Winf.mulVec (yStar - xStar).ofLp) -
          dotProduct (yStar - yStar).ofLp (Winf.mulVec (yStar - yStar).ofLp))) :=
      (hquad_cont.tendsto _).comp (hlim_yStar'.sub tendsto_const_nhds) |>.sub
        ((hquad_cont.tendsto _).comp (hlim_yStar'.sub tendsto_const_nhds))
    exact tendsto_nhds_unique hA hB
  have hsym_quad : dotProduct (yStar - xStar).ofLp (Winf.mulVec (yStar - xStar).ofLp) =
      dotProduct (xStar - yStar).ofLp (Winf.mulVec (xStar - yStar).ofLp) := by
    have : (yStar - xStar).ofLp = -(xStar - yStar).ofLp := by ext i; simp
    rw [this, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  simp only [sub_self, WithLp.ofLp_zero, Matrix.mulVec_zero, dotProduct_zero, zero_sub, sub_zero] at hlim1 hlim2
  rw [hsym_quad] at hlim2
  have hzero : dotProduct (xStar - yStar).ofLp (Winf.mulVec (xStar - yStar).ofLp) = 0 := by linarith
  have hlow := hWinf_low (xStar - yStar)
  rw [hzero] at hlow
  have hnorm0 : ‖xStar - yStar‖ = 0 := by
    by_contra h
    have : 0 < δ * ‖xStar - yStar‖ ^ 2 := mul_pos hδ (sq_pos_of_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)))
    linarith
  exact hne (sub_eq_zero.mp (norm_eq_zero.mp hnorm0)).symm

/-! ### Part 7: Assembly of `theorem main` -/

private theorem main_proved :
    ∀ (n : ℕ) (variant : AdaGradVariant)
      (f : EuclideanSpace ℝ (Fin n) → ℝ)
      (grad : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (δ η : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)),
      0 < δ →
      0 < η →
      ConvexOn ℝ Set.univ f →
      (∀ y, HasGradientAt f (grad y) y) →
      LocallyLipschitz grad →
      (∃ z : EuclideanSpace ℝ (Fin n), ∀ y, f z ≤ f y) →
      IsAdaGradSeq variant grad δ η x →
      ((∃ xStar : EuclideanSpace ℝ (Fin n),
          (∀ y, f xStar ≤ f y) ∧ Filter.Tendsto x Filter.atTop (nhds xStar)) ↔
        Bornology.IsBounded (Set.range x)) ∧
      (Bornology.IsBounded (Set.range x) ↔
        Summable (fun k => ‖grad (x k)‖ ^ 2)) := by
  intro n variant f grad δ η x hδ hη hf_conv hf_grad hgrad_ll hmin hada
  -- Handle `n = 0` separately (all vectors are `0`, so all 3 statements are trivially true)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hsub : ∀ u v : EuclideanSpace ℝ (Fin 0), u = v := fun u v => by
      ext i; exact Fin.elim0 i
    have h1 : ∃ xStar : EuclideanSpace ℝ (Fin 0),
        (∀ y, f xStar ≤ f y) ∧ Filter.Tendsto x Filter.atTop (nhds xStar) := by
      refine ⟨0, fun y => by rw [hsub 0 y], ?_⟩
      simp [show x = fun _ => (0 : EuclideanSpace ℝ (Fin 0)) from funext (fun k => hsub (x k) 0)]
    have h2 : Bornology.IsBounded (Set.range x) := by
      refine Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin 0)) |>.mpr ⟨0, ?_⟩
      rintro _ ⟨k, rfl⟩
      simp [hsub (x k) 0]
    have h3 : Summable (fun k => ‖grad (x k)‖ ^ 2) := by
      have : (fun k => ‖grad (x k)‖ ^ 2) = fun _ => (0 : ℝ) := by
        funext k; rw [hsub (grad (x k)) 0]; simp
      rw [this]
      exact summable_zero
    exact ⟨⟨fun _ => h2, fun _ => h1⟩, ⟨fun _ => h3, fun _ => h2⟩⟩
  -- For `n ≥ 1`, prove the cycle `(1) ⇒ (2) ⇒ (3) ⇒ (1)`!
  have h12 : (∃ xStar : EuclideanSpace ℝ (Fin n),
      (∀ y, f xStar ≤ f y) ∧ Filter.Tendsto x Filter.atTop (nhds xStar)) →
      Bornology.IsBounded (Set.range x) := by
    rintro ⟨xStar, _, hlim⟩
    exact Metric.isBounded_range_of_tendsto x hlim
  have h23 : Bornology.IsBounded (Set.range x) → Summable (fun k => ‖grad (x k)‖ ^ 2) :=
    bounded_implies_summable hn variant f grad hδ hη x hf_grad hgrad_ll hmin hada
  have h31 : Summable (fun k => ‖grad (x k)‖ ^ 2) →
      ∃ xStar : EuclideanSpace ℝ (Fin n),
        (∀ y, f xStar ≤ f y) ∧ Filter.Tendsto x Filter.atTop (nhds xStar) :=
    summable_implies_convergent variant f grad hδ hη x hf_conv hf_grad hgrad_ll hmin hada
  exact ⟨⟨h12, fun h2 => h31 (h23 h2)⟩, ⟨h23, fun h3 => h12 (h31 h3)⟩⟩

end OMA.P_arxiv_2608_00482

theorem OMA.solution : type_of% @OMA.S_arxiv_2608_00482.main :=
  OMA.P_arxiv_2608_00482.main_proved
