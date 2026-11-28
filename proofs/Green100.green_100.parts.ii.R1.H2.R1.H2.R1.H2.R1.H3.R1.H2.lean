import OMAReductions.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1_H3_R1

/-!
Proof of `Green100.green_100.parts.ii.R1.H2.R1.H2.R1.H2.R1.H3.R1.H2`
(Alekseev-Liu-Thom, arXiv:2609.37761v2, Theorem 5.2: matrix-unit rounding for
positive self-adjoint unitary-mixture channels).
-/

namespace OMA.H3R1H2Proof

open Filter Matrix
open scoped Topology
open OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1
open OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1_H3_R1

/- ### Section 1: Hilbert-Schmidt space, rank-one operators, projections, and block SVD -/

abbrev Mat (k : ℕ) := Matrix (Fin k) (Fin k) ℂ
abbrev Vec (k : ℕ) := EuclideanSpace ℂ (Fin k)

noncomputable def ss {k : ℕ} (x : Mat k) : ℝ := ∑ a, ∑ b, ‖x a b‖ ^ 2

lemma ss_nonneg {k : ℕ} (x : Mat k) : 0 ≤ ss x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma ss_eq_re_trace {k : ℕ} (x : Mat k) : ss x = ((star x * x).trace).re :=
  (re_trace_star_mul_self x).symm

lemma trace_star_mul_self_eq_ss {k : ℕ} (x : Mat k) :
    (star x * x).trace = ((ss x : ℝ) : ℂ) :=
  trace_star_mul_self_eq x

lemma ss_zero {k : ℕ} : ss (0 : Mat k) = 0 := by
  simp [ss]

lemma ss_neg_eq {k : ℕ} (x : Mat k) : ss (-x) = ss x := by
  simp [ss]

lemma ss_eq_zero_iff' {k : ℕ} (x : Mat k) : ss x = 0 ↔ x = 0 :=
  ss_eq_zero_iff x

lemma ss_pos_of_ne_zero {k : ℕ} {x : Mat k} (hx : x ≠ 0) : 0 < ss x :=
  lt_of_le_of_ne (ss_nonneg x) (Ne.symm (mt (ss_eq_zero_iff' x).1 hx))

lemma ss_smul' {k : ℕ} (c : ℂ) (x : Mat k) : ss (c • x) = ‖c‖ ^ 2 * ss x :=
  ss_smul c x

lemma sqrt_ss_add_le' {k : ℕ} (A B : Mat k) :
    Real.sqrt (ss (A + B)) ≤ Real.sqrt (ss A) + Real.sqrt (ss B) :=
  sqrt_ss_add_le A B

lemma sqrt_ss_smul' {k : ℕ} (c : ℂ) (A : Mat k) :
    Real.sqrt (ss (c • A)) = ‖c‖ * Real.sqrt (ss A) :=
  sqrt_ss_smul c A

lemma orthonormal_inner_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} {u : ι → E} (hu : Orthonormal ℂ u) (a : ι) :
    @inner ℂ _ _ (u a) (u a) = 1 := by
  classical
  simpa using (orthonormal_iff_ite.1 hu a a)

noncomputable def toHS {k : ℕ} :
    Mat k ≃ₗ[ℂ] EuclideanSpace ℂ (Fin k × Fin k) where
  toFun A := WithLp.toLp 2 (fun p : Fin k × Fin k => A p.1 p.2)
  invFun v := fun i j => v.ofLp (i, j)
  map_add' _ _ := by ext ⟨i, j⟩; rfl
  map_smul' _ _ := by ext ⟨i, j⟩; rfl
  left_inv _ := by ext i j; rfl
  right_inv _ := by ext ⟨i, j⟩; rfl

lemma toHS_norm_sq {k : ℕ} (A : Mat k) : ‖toHS A‖ ^ 2 = ss A := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

lemma toHS_norm {k : ℕ} (A : Mat k) : ‖toHS A‖ = Real.sqrt (ss A) := by
  rw [← Real.sqrt_sq (norm_nonneg (toHS A)), toHS_norm_sq]

lemma toHS_inner {k : ℕ} (A B : Mat k) :
    @inner ℂ _ _ (toHS A) (toHS B) = (star A * B).trace := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_prod_type,
    Matrix.trace, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.star_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  change B j i * star (A j i) = star (A j i) * B j i
  rw [mul_comm]

lemma norm_trace_star_mul_le {k : ℕ} (A B : Mat k) :
    ‖(star A * B).trace‖ ≤ Real.sqrt (ss A) * Real.sqrt (ss B) := by
  rw [← toHS_inner, ← toHS_norm A, ← toHS_norm B]
  exact norm_inner_le_norm (toHS A) (toHS B)

lemma inner_vec_eq_sum {k : ℕ} (u v : Vec k) :
    @inner ℂ _ _ u v = ∑ c : Fin k, star (u.ofLp c) * v.ofLp c := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  refine Finset.sum_congr rfl fun c _ => ?_
  change v.ofLp c * star (u.ofLp c) = star (u.ofLp c) * v.ofLp c
  rw [mul_comm]

lemma inner_toEuclideanCLM {k : ℕ} (A : Mat k) (u v : Vec k) :
    @inner ℂ _ _ u (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) A v) =
      @inner ℂ _ _ (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (star A) u) v := by
  rw [inner_vec_eq_sum, inner_vec_eq_sum]
  simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Matrix.star_apply,
    Finset.mul_sum, Finset.sum_mul, star_sum, star_mul', star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma toEuclideanCLM_mul_apply {k : ℕ} (A B : Mat k) (ξ : Vec k) :
    Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (A * B) ξ =
      Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) A
        (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) B ξ) := by
  ext r
  simp [Matrix.mulVec_mulVec]

lemma bessel_ineq {k : ℕ} {ι : Type*} [Fintype ι] {φ : ι → Vec k}
    (hφ : Orthonormal ℂ φ) (ξ : Vec k) :
    ∑ a : ι, ‖@inner ℂ _ _ (φ a) ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
  classical
  let w : Vec k := ∑ a : ι, (@inner ℂ _ _ (φ a) ξ) • φ a
  have h1 : ‖w‖ ^ 2 = ∑ a : ι, ‖@inner ℂ _ _ (φ a) ξ‖ ^ 2 := by
    have hre : (@inner ℂ _ _ w w).re = ∑ a : ι, ‖@inner ℂ _ _ (φ a) ξ‖ ^ 2 := by
      have hsum : @inner ℂ _ _ w w = ((∑ a : ι, ‖@inner ℂ _ _ (φ a) ξ‖ ^ 2 : ℝ) : ℂ) := by
        simp only [w, Complex.ofReal_sum]
        rw [sum_inner]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [inner_sum]
        have horth : ∀ b : ι,
            @inner ℂ _ _ ((@inner ℂ _ _ (φ a) ξ) • φ a) ((@inner ℂ _ _ (φ b) ξ) • φ b) =
              if b = a then ((‖@inner ℂ _ _ (φ a) ξ‖ ^ 2 : ℝ) : ℂ) else 0 := fun b => by
          rw [inner_smul_left, inner_smul_right]
          by_cases hba : b = a
          · subst hba
            rw [if_pos rfl, orthonormal_inner_self hφ b, mul_one, mul_comm, Complex.mul_conj',
              Complex.ofReal_pow]
          · rw [if_neg hba, hφ.2 (Ne.symm hba), mul_zero, mul_zero]
        rw [Finset.sum_congr rfl fun b _ => horth b, Finset.sum_ite_eq' Finset.univ a,
          if_pos (Finset.mem_univ a)]
      rw [hsum, Complex.ofReal_re]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) w).symm.trans hre
  have h2 : @inner ℂ _ _ w ξ = ((∑ a : ι, ‖@inner ℂ _ _ (φ a) ξ‖ ^ 2 : ℝ) : ℂ) := by
    simp only [w, sum_inner, inner_smul_left, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm, Complex.mul_conj', Complex.ofReal_pow]
  have h3 : 0 ≤ ‖ξ - w‖ ^ 2 := sq_nonneg _
  have h4 : ‖ξ - w‖ ^ 2 = ‖ξ‖ ^ 2 - 2 * (@inner ℂ _ _ w ξ).re + ‖w‖ ^ 2 := by
    have hξw : RCLike.re (@inner ℂ _ _ (ξ - w) (ξ - w)) = ‖ξ - w‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) (ξ - w)
    rw [inner_sub_left, inner_sub_right, inner_sub_right, map_sub, map_sub, map_sub,
      inner_self_eq_norm_sq (𝕜 := ℂ) ξ, inner_self_eq_norm_sq (𝕜 := ℂ) w] at hξw
    have hsym : RCLike.re (@inner ℂ _ _ ξ w) = (@inner ℂ _ _ w ξ).re := by
      rw [← inner_conj_symm]
      exact Complex.conj_re _
    have hwξ : RCLike.re (@inner ℂ _ _ w ξ) = (@inner ℂ _ _ w ξ).re := rfl
    rw [hsym, hwξ] at hξw
    linarith
  rw [h2, Complex.ofReal_re, h1] at h4
  linarith

lemma orthonormal_sum_norm_sq {k : ℕ} {ι : Type*} [Fintype ι] {u : ι → Vec k}
    (hu : Orthonormal ℂ u) (c : ι → ℂ) :
    ‖∑ a : ι, c a • u a‖ ^ 2 = ∑ a : ι, ‖c a‖ ^ 2 := by
  classical
  have hre : (@inner ℂ _ _ (∑ a : ι, c a • u a) (∑ a : ι, c a • u a)).re =
      ∑ a : ι, ‖c a‖ ^ 2 := by
    have hsum : @inner ℂ _ _ (∑ a : ι, c a • u a) (∑ a : ι, c a • u a) =
        ((∑ a : ι, ‖c a‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum, sum_inner]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [inner_sum]
      have horth : ∀ b : ι,
          @inner ℂ _ _ (c a • u a) (c b • u b) =
            if b = a then ((‖c a‖ ^ 2 : ℝ) : ℂ) else 0 := fun b => by
        rw [inner_smul_left, inner_smul_right]
        by_cases hba : b = a
        · subst hba
          rw [if_pos rfl, orthonormal_inner_self hu b, mul_one, mul_comm, Complex.mul_conj',
            Complex.ofReal_pow]
        · rw [if_neg hba, hu.2 (Ne.symm hba), mul_zero, mul_zero]
      rw [Finset.sum_congr rfl fun b _ => horth b, Finset.sum_ite_eq' Finset.univ a,
        if_pos (Finset.mem_univ a)]
    rw [hsum, Complex.ofReal_re]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm.trans hre

/-- Rank-one outer product `|u⟩⟨φ|` as a `k × k` matrix. -/
def rankOne {k : ℕ} (u φ : Vec k) : Mat k :=
  fun r c => u.ofLp r * star (φ.ofLp c)

lemma toEuclideanCLM_rankOne {k : ℕ} (u φ ξ : Vec k) :
    Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (rankOne u φ) ξ =
      (@inner ℂ _ _ φ ξ) • u := by
  ext r
  rw [Matrix.ofLp_toEuclideanCLM]
  change (∑ c : Fin k, u.ofLp r * star (φ.ofLp c) * ξ.ofLp c) = (@inner ℂ _ _ φ ξ) * u.ofLp r
  rw [inner_vec_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

lemma star_rankOne {k : ℕ} (u φ : Vec k) : star (rankOne u φ) = rankOne φ u := by
  ext r c
  simp [rankOne, Matrix.star_apply, mul_comm]

lemma rankOne_mul_rankOne {k : ℕ} (u₁ φ₁ u₂ φ₂ : Vec k) :
    rankOne u₁ φ₁ * rankOne u₂ φ₂ = (@inner ℂ _ _ φ₁ u₂) • rankOne u₁ φ₂ := by
  ext r c
  simp only [Matrix.mul_apply, rankOne, Matrix.smul_apply, smul_eq_mul, inner_vec_eq_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

lemma trace_rankOne {k : ℕ} (u φ : Vec k) :
    (rankOne u φ).trace = @inner ℂ _ _ φ u := by
  rw [Matrix.trace, inner_vec_eq_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [rankOne, mul_comm]

lemma mul_rankOne {k : ℕ} (A : Mat k) (u φ : Vec k) :
    A * rankOne u φ = rankOne (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) A u) φ := by
  ext r c
  simp only [Matrix.mul_apply, rankOne, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

lemma rankOne_mul {k : ℕ} (u φ : Vec k) (A : Mat k) :
    rankOne u φ * A = rankOne u (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (star A) φ) := by
  ext r c
  simp only [Matrix.mul_apply, rankOne, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
    Matrix.star_apply, star_sum, star_mul', star_star, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

lemma sum_rankOne_star_mul {k : ℕ} {ι : Type*} [Fintype ι] {u φ : ι → Vec k}
    (hu : Orthonormal ℂ u) (c : ι → ℂ) :
    star (∑ a : ι, c a • rankOne (u a) (φ a)) * (∑ a : ι, c a • rankOne (u a) (φ a)) =
      ∑ a : ι, ((‖c a‖ ^ 2 : ℝ) : ℂ) • rankOne (φ a) (φ a) := by
  classical
  rw [star_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  have hterm : ∀ b : ι,
      star (c a • rankOne (u a) (φ a)) * (c b • rankOne (u b) (φ b)) =
        if b = a then ((‖c a‖ ^ 2 : ℝ) : ℂ) • rankOne (φ a) (φ a) else 0 := fun b => by
    rw [star_smul, star_rankOne, smul_mul_assoc, mul_smul_comm, rankOne_mul_rankOne, smul_smul,
      smul_smul]
    by_cases hba : b = a
    · subst hba
      rw [if_pos rfl, orthonormal_inner_self hu b, mul_one, Complex.star_def, mul_comm,
        Complex.mul_conj', Complex.ofReal_pow]
    · rw [if_neg hba, hu.2 (Ne.symm hba), mul_zero, zero_smul]
  simp_rw [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma sum_rankOne_mul_star {k : ℕ} {ι : Type*} [Fintype ι] {u φ : ι → Vec k}
    (hφ : Orthonormal ℂ φ) (c : ι → ℂ) :
    (∑ a : ι, c a • rankOne (u a) (φ a)) * star (∑ a : ι, c a • rankOne (u a) (φ a)) =
      ∑ a : ι, ((‖c a‖ ^ 2 : ℝ) : ℂ) • rankOne (u a) (u a) := by
  have h := sum_rankOne_star_mul (u := φ) (φ := u) hφ (fun a => star (c a))
  have hLHS : ∑ a : ι, star (c a) • rankOne (φ a) (u a) =
      star (∑ a : ι, c a • rankOne (u a) (φ a)) := by
    rw [star_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [star_smul, star_rankOne]
  rw [hLHS, star_star] at h
  refine h.trans (Finset.sum_congr rfl fun a _ => ?_)
  rw [norm_star]

lemma sum_rankOne_ss {k : ℕ} {ι : Type*} [Fintype ι] {u φ : ι → Vec k}
    (hu : Orthonormal ℂ u) (hφ : Orthonormal ℂ φ) (c : ι → ℂ) :
    ss (∑ a : ι, c a • rankOne (u a) (φ a)) = ∑ a : ι, ‖c a‖ ^ 2 := by
  rw [ss_eq_re_trace, sum_rankOne_star_mul hu c, Matrix.trace_sum]
  have ht : ∀ a : ι, (((‖c a‖ ^ 2 : ℝ) : ℂ) • rankOne (φ a) (φ a)).trace =
      ((‖c a‖ ^ 2 : ℝ) : ℂ) := fun a => by
    rw [Matrix.trace_smul, trace_rankOne, orthonormal_inner_self hφ a, smul_eq_mul, mul_one]
  simp_rw [ht, ← Complex.ofReal_sum, Complex.ofReal_re]

lemma sum_rankOne_fourth_moment {k : ℕ} {ι : Type*} [Fintype ι] {u φ : ι → Vec k}
    (hu : Orthonormal ℂ u) (hφ : Orthonormal ℂ φ) (c : ι → ℂ) :
    ss (star (∑ a : ι, c a • rankOne (u a) (φ a)) * (∑ a : ι, c a • rankOne (u a) (φ a))) =
      ∑ a : ι, ‖c a‖ ^ 4 := by
  rw [sum_rankOne_star_mul hu c, sum_rankOne_ss hφ hφ]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  ring

lemma sum_rankOne_opNorm_le {k : ℕ} {ι : Type*} [Fintype ι] {u φ : ι → Vec k}
    (hu : Orthonormal ℂ u) (hφ : Orthonormal ℂ φ) (c : ι → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hc : ∀ a, ‖c a‖ ≤ R) :
    ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (∑ a : ι, c a • rankOne (u a) (φ a))‖ ≤ R := by
  refine ContinuousLinearMap.opNorm_le_bound _ hR fun ξ => ?_
  have happ : Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ)
      (∑ a : ι, c a • rankOne (u a) (φ a)) ξ =
      ∑ a : ι, (c a * @inner ℂ _ _ (φ a) ξ) • u a := by
    rw [map_sum, _root_.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, _root_.smul_apply, toEuclideanCLM_rankOne, smul_smul]
  rw [happ]
  have hsq : ‖∑ a : ι, (c a * @inner ℂ _ _ (φ a) ξ) • u a‖ ^ 2 ≤ (R * ‖ξ‖) ^ 2 := by
    rw [orthonormal_sum_norm_sq hu]
    calc ∑ a : ι, ‖c a * @inner ℂ _ _ (φ a) ξ‖ ^ 2
        = ∑ a : ι, ‖c a‖ ^ 2 * ‖@inner ℂ _ _ (φ a) ξ‖ ^ 2 := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [norm_mul, mul_pow]
      _ ≤ ∑ a : ι, R ^ 2 * ‖@inner ℂ _ _ (φ a) ξ‖ ^ 2 := by
          refine Finset.sum_le_sum fun a _ => ?_
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hc a) 2) (sq_nonneg _)
      _ = R ^ 2 * ∑ a : ι, ‖@inner ℂ _ _ (φ a) ξ‖ ^ 2 := by rw [← Finset.mul_sum]
      _ ≤ R ^ 2 * ‖ξ‖ ^ 2 := mul_le_mul_of_nonneg_left (bessel_ineq hφ ξ) (sq_nonneg R)
      _ = (R * ‖ξ‖) ^ 2 := by ring
  nlinarith [norm_nonneg (∑ a : ι, (c a * @inner ℂ _ _ (φ a) ξ) • u a),
    mul_nonneg hR (norm_nonneg ξ)]

/-- Range subspace of a matrix `e` acting on `Vec k`. -/
noncomputable def projRange {k : ℕ} (e : Mat k) : Submodule ℂ (Vec k) :=
  LinearMap.range (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) e).toLinearMap

lemma mem_projRange_iff {k : ℕ} {e : Mat k} (he2 : e * e = e) (ξ : Vec k) :
    ξ ∈ projRange e ↔ Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) e ξ = ξ := by
  constructor
  · rintro ⟨η, rfl⟩
    change Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) e
      (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) e η) =
      Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) e η
    rw [← toEuclideanCLM_mul_apply, he2]
  · intro h
    exact ⟨ξ, h⟩

lemma proj_eq_sum_rankOne_basis {k : ℕ} {e : Mat k} (he1 : star e = e) (he2 : e * e = e)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ (projRange e)) :
    e = ∑ a : ι, rankOne (b a : Vec k) (b a : Vec k) := by
  have hclm : Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) e =
      Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ)
        (∑ a : ι, rankOne (b a : Vec k) (b a : Vec k)) := by
    refine ContinuousLinearMap.ext fun ξ => ?_
    rw [map_sum, _root_.sum_apply]
    let ξ₁ : projRange e := ⟨Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) e ξ, ⟨ξ, rfl⟩⟩
    have hinner : ∀ a : ι, @inner ℂ _ _ (b a : Vec k) ξ = @inner ℂ _ _ (b a) ξ₁ := fun a => by
      have hb : Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) e (b a : Vec k) = (b a : Vec k) :=
        (mem_projRange_iff he2 _).1 (b a).2
      calc @inner ℂ _ _ (b a : Vec k) ξ
          = @inner ℂ _ _ (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (star e) (b a : Vec k)) ξ := by
            rw [he1, hb]
        _ = @inner ℂ _ _ (b a : Vec k) (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) e ξ) :=
            (inner_toEuclideanCLM e _ _).symm
        _ = @inner ℂ _ _ (b a) ξ₁ := rfl
    have hsum : ∑ a : ι, Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ)
        (rankOne (b a : Vec k) (b a : Vec k)) ξ =
        ((∑ a : ι, (@inner ℂ _ _ (b a) ξ₁) • b a : projRange e) : Vec k) := by
      simp only [toEuclideanCLM_rankOne, hinner, AddSubmonoidClass.coe_finsetSum,
        SetLike.val_smul]
    rw [hsum, b.sum_repr' ξ₁]
  exact (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ)).injective hclm

lemma proj_trace_eq_finrank {k : ℕ} {e : Mat k} (he1 : star e = e) (he2 : e * e = e) :
    e.trace = (Module.finrank ℂ (projRange e) : ℂ) := by
  let b := stdOrthonormalBasis ℂ (projRange e)
  have heq := proj_eq_sum_rankOne_basis he1 he2 b
  conv_lhs => rw [heq]
  rw [Matrix.trace_sum]
  have ht : ∀ a : Fin (Module.finrank ℂ (projRange e)),
      (rankOne (b a : Vec k) (b a : Vec k)).trace = 1 := fun a => by
    rw [trace_rankOne]
    exact orthonormal_inner_self b.orthonormal a
  simp_rw [ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

lemma proj_re_trace_eq_finrank {k : ℕ} {e : Mat k} (he1 : star e = e) (he2 : e * e = e) :
    (e.trace).re = (Module.finrank ℂ (projRange e) : ℝ) := by
  rw [proj_trace_eq_finrank he1 he2, Complex.natCast_re]

lemma proj_trace_eq_ofReal_re {k : ℕ} {e : Mat k} (he1 : star e = e) (he2 : e * e = e) :
    e.trace = (((e.trace).re : ℝ) : ℂ) := by
  rw [proj_trace_eq_finrank he1 he2, Complex.natCast_re, Complex.ofReal_natCast]

lemma proj_finrank_pos {k : ℕ} {e : Mat k} (he1 : star e = e) (he2 : e * e = e) (hne : e ≠ 0) :
    0 < Module.finrank ℂ (projRange e) := by
  by_contra h
  have h0 : Module.finrank ℂ (projRange e) = 0 := Nat.eq_zero_of_not_pos h
  have htr : ss e = 0 := by
    rw [ss_eq_re_trace, he1, he2, proj_re_trace_eq_finrank he1 he2, h0, Nat.cast_zero]
  exact hne ((ss_eq_zero_iff' e).1 htr)

lemma proj_ss_eq_re_trace {k : ℕ} {e : Mat k} (he1 : star e = e) (he2 : e * e = e) :
    ss e = (e.trace).re := by
  rw [ss_eq_re_trace, he1, he2]

lemma proj_opNorm_le_one {k : ℕ} {e : Mat k} (he1 : star e = e) (he2 : e * e = e) :
    ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) e‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => ?_
  rw [one_mul]
  let w := Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) e ξ
  have hinner : @inner ℂ _ _ w (ξ - w) = 0 := by
    change @inner ℂ _ _ (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) e ξ)
      (ξ - Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) e ξ) = 0
    have h1 : @inner ℂ _ _ (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (star e) ξ)
        (ξ - Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) e ξ) =
        @inner ℂ _ _ ξ (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) e
          (ξ - Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) e ξ)) :=
      (inner_toEuclideanCLM e ξ _).symm
    rw [he1] at h1
    rw [h1, map_sub, ← toEuclideanCLM_mul_apply, he2, sub_self, inner_zero_right]
  have hpyth : ‖ξ‖ ^ 2 = ‖w‖ ^ 2 + ‖ξ - w‖ ^ 2 := by
    have hξ : ξ = w + (ξ - w) := by abel
    conv_lhs => rw [hξ]
    have hsym : @inner ℂ _ _ (ξ - w) w = 0 := by
      rw [← inner_conj_symm, hinner, map_zero]
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_add_left, inner_add_right, inner_add_right,
      hinner, hsym, add_zero, zero_add, map_add, inner_self_eq_norm_sq (𝕜 := ℂ) w,
      inner_self_eq_norm_sq (𝕜 := ℂ) (ξ - w)]
  have hsq : ‖w‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by linarith [sq_nonneg ‖ξ - w‖]
  nlinarith [norm_nonneg w, norm_nonneg ξ]

lemma proj_eq_of_le_and_trace_eq {k : ℕ} {P e : Mat k}
    (hP1 : star P = P) (hP2 : P * P = P) (he1 : star e = e) (he2 : e * e = e)
    (hPe : e * P * e = P) (htr : P.trace = e.trace) : P = e := by
  have hPl : e * P = P := by
    calc e * P = e * (e * P * e) := by rw [hPe]
      _ = (e * e) * P * e := by noncomm_ring
      _ = e * P * e := by rw [he2]
      _ = P := hPe
  have hPr : P * e = P := by
    calc P * e = (e * P * e) * e := by rw [hPe]
      _ = e * P * (e * e) := by noncomm_ring
      _ = e * P * e := by rw [he2]
      _ = P := hPe
  have hD1 : star (e - P) = e - P := by rw [star_sub, he1, hP1]
  have hD2 : (e - P) * (e - P) = e - P := by
    calc (e - P) * (e - P) = e * e - e * P - P * e + P * P := by noncomm_ring
      _ = e - P - P + P := by rw [he2, hPl, hPr, hP2]
      _ = e - P := by abel
  have hss : ss (e - P) = 0 := by
    rw [ss_eq_re_trace, hD1, hD2, Matrix.trace_sub, htr, sub_self, Complex.zero_re]
  exact (sub_eq_zero.1 ((ss_eq_zero_iff' (e - P)).1 hss)).symm

/-- Trace intersection bound for two subprojections of `e`:
`Re Tr(P Q) ≥ Re Tr(P) + Re Tr(Q) - Re Tr(e)`. -/
lemma proj_mul_trace_ge {k : ℕ} {P Q e : Mat k}
    (hP1 : star P = P) (hP2 : P * P = P)
    (hQ1 : star Q = Q) (hQ2 : Q * Q = Q)
    (he1 : star e = e) (he2 : e * e = e)
    (hPe : e * P * e = P) (hQe : e * Q * e = Q) :
    (P.trace).re + (Q.trace).re - (e.trace).re ≤ ((P * Q).trace).re := by
  have hPl : e * P = P := by
    calc e * P = e * (e * P * e) := by rw [hPe]
      _ = (e * e) * P * e := by noncomm_ring
      _ = P := by rw [he2, hPe]
  have hPr : P * e = P := by
    calc P * e = (e * P * e) * e := by rw [hPe]
      _ = e * P * (e * e) := by noncomm_ring
      _ = P := by rw [he2, hPe]
  have hQl : e * Q = Q := by
    calc e * Q = e * (e * Q * e) := by rw [hQe]
      _ = (e * e) * Q * e := by noncomm_ring
      _ = Q := by rw [he2, hQe]
  have hQr : Q * e = Q := by
    calc Q * e = (e * Q * e) * e := by rw [hQe]
      _ = e * Q * (e * e) := by noncomm_ring
      _ = Q := by rw [he2, hQe]
  let P' := e - P
  let Q' := e - Q
  have hP'1 : star P' = P' := by simp [P', he1, hP1]
  have hP'2 : P' * P' = P' := by
    calc (e - P) * (e - P) = e * e - e * P - P * e + P * P := by noncomm_ring
      _ = e - P := by rw [he2, hPl, hPr, hP2]; abel
  have hQ'1 : star Q' = Q' := by simp [Q', he1, hQ1]
  have hQ'2 : Q' * Q' = Q' := by
    calc (e - Q) * (e - Q) = e * e - e * Q - Q * e + Q * Q := by noncomm_ring
      _ = e - Q := by rw [he2, hQl, hQr, hQ2]; abel
  have hid : P' * Q' = e - P - Q + P * Q := by
    calc (e - P) * (e - Q) = e * e - e * Q - P * e + P * Q := by noncomm_ring
      _ = e - Q - P + P * Q := by rw [he2, hQl, hPr]
      _ = e - P - Q + P * Q := by abel
  have hnn : 0 ≤ ((P' * Q').trace).re := by
    have htr : (P' * Q').trace = (star (P' * Q') * (P' * Q')).trace := by
      rw [star_mul, hP'1, hQ'1]
      calc (P' * Q').trace = ((P' * P') * (Q' * Q')).trace := by rw [hP'2, hQ'2]
        _ = ((P' * P' * Q') * Q').trace := by noncomm_ring
        _ = (Q' * (P' * P' * Q')).trace := Matrix.trace_mul_comm _ _
        _ = (Q' * P' * (P' * Q')).trace := by noncomm_ring
    rw [htr, re_trace_star_mul_self]
    exact ss_nonneg _
  rw [hid, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
    Complex.add_re, Complex.sub_re, Complex.sub_re] at hnn
  linarith

lemma finset_exists_superset_card_eq {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) {n : ℕ} (hsn : s.card ≤ n) (hn : n ≤ Fintype.card α) :
    ∃ J : Finset α, s ⊆ J ∧ J.card = n :=
  Finset.exists_superset_card_eq hsn hn

/-- Positive-singular-value SVD of `v ∈ B(e₁, e₂)` on `projRange e₂`. -/
lemma exists_block_svd_pos {k : ℕ} {e₁ e₂ v : Mat k}
    (_h1a : star e₁ = e₁) (h1b : e₁ * e₁ = e₁)
    (h2a : star e₂ = e₂) (h2b : e₂ * e₂ = e₂)
    (hv : e₁ * v * e₂ = v) :
    let r₂ := Module.finrank ℂ (projRange e₂)
    ∃ (b₂ : OrthonormalBasis (Fin r₂) ℂ (projRange e₂)) (s : Fin r₂ → ℝ)
      (Kpos : Finset (Fin r₂)) (u₀ : Fin r₂ → projRange e₁),
      (∀ a, 0 ≤ s a) ∧
      (∀ a, a ∈ Kpos ↔ 0 < s a) ∧
      Kpos.card ≤ min (Module.finrank ℂ (projRange e₁)) r₂ ∧
      Orthonormal ℂ (fun a : Kpos => u₀ a.1) ∧
      (∀ a : Fin r₂, Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) v (b₂ a).1 =
        (s a : ℂ) • (u₀ a).1) := by
  classical
  let r₁ := Module.finrank ℂ (projRange e₁)
  let r₂ := Module.finrank ℂ (projRange e₂)
  let A : Mat k := star v * v
  have hv_l : e₁ * v = v := by
    calc e₁ * v = e₁ * (e₁ * v * e₂) := by rw [hv]
      _ = (e₁ * e₁) * v * e₂ := by noncomm_ring
      _ = v := by rw [h1b, hv]
  have hv_r : v * e₂ = v := by
    calc v * e₂ = (e₁ * v * e₂) * e₂ := by rw [hv]
      _ = e₁ * v * (e₂ * e₂) := by noncomm_ring
      _ = v := by rw [h2b, hv]
  have hA_star : star A = A := by simp [A, star_mul]
  have hA_l : e₂ * A = A := by
    have h1 : e₂ * star v = star v := by
      calc e₂ * star v = star (v * e₂) := by rw [star_mul, h2a]
        _ = star v := by rw [hv_r]
    calc e₂ * A = (e₂ * star v) * v := by simp only [A, mul_assoc]
      _ = A := by rw [h1]
  let TA : (projRange e₂) →ₗ[ℂ] (projRange e₂) :=
    { toFun := fun ξ =>
        ⟨Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) A ξ.1,
          (mem_projRange_iff h2b _).2 (by rw [← toEuclideanCLM_mul_apply, hA_l])⟩
      map_add' := fun x y => by
        apply Subtype.ext
        exact map_add (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) A) x.1 y.1
      map_smul' := fun c x => by
        apply Subtype.ext
        exact map_smul (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) A) c x.1 }
  have hTA_symm : @LinearMap.IsSymmetric ℂ (projRange e₂) _ _ _ TA := fun x y => by
    change @inner ℂ _ _ (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) A x.1) y.1 =
      @inner ℂ _ _ x.1 (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) A y.1)
    rw [← hA_star, ← inner_toEuclideanCLM A x.1 y.1, hA_star]
  have hTA_nonneg : ∀ x : projRange e₂,
      (@inner ℂ _ _ x (TA x)).re = ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) v x.1‖ ^ 2 :=
    fun x => by
      change (@inner ℂ _ _ x.1 (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (star v * v) x.1)).re = _
      rw [toEuclideanCLM_mul_apply, inner_toEuclideanCLM, star_star]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  let b₂ : OrthonormalBasis (Fin r₂) ℂ (projRange e₂) := hTA_symm.eigenvectorBasis rfl
  let μ : Fin r₂ → ℝ := hTA_symm.eigenvalues rfl
  have hμ_ev : ∀ a : Fin r₂, TA (b₂ a) = (μ a : ℂ) • b₂ a := fun a =>
    (Module.End.mem_eigenspace_iff.1 (hTA_symm.hasEigenvector_eigenvectorBasis rfl a).1)
  have hμ_nn : ∀ a : Fin r₂, 0 ≤ μ a := fun a => by
    have h := hTA_nonneg (b₂ a)
    rw [hμ_ev a] at h
    have hin : @inner ℂ _ _ (b₂ a) ((μ a : ℂ) • b₂ a) = (μ a : ℂ) := by
      change @inner ℂ _ _ (b₂ a).1 ((μ a : ℂ) • (b₂ a).1) = (μ a : ℂ)
      rw [inner_smul_right]
      have h1 : @inner ℂ _ _ (b₂ a).1 (b₂ a).1 = 1 := orthonormal_inner_self b₂.orthonormal a
      rw [h1, mul_one]
    rw [hin, Complex.ofReal_re] at h
    linarith [sq_nonneg ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) v (b₂ a).1‖]
  let s : Fin r₂ → ℝ := fun a => Real.sqrt (μ a)
  have hs_nn : ∀ a, 0 ≤ s a := fun a => Real.sqrt_nonneg _
  have hs_sq : ∀ a, s a ^ 2 = μ a := fun a => Real.sq_sqrt (hμ_nn a)
  let Kpos : Finset (Fin r₂) := Finset.univ.filter (fun a => 0 < s a)
  let u₀ : Fin r₂ → projRange e₁ := fun a =>
    ((s a : ℂ)⁻¹) • ⟨Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) v (b₂ a).1,
      (mem_projRange_iff h1b _).2 (by rw [← toEuclideanCLM_mul_apply, hv_l])⟩
  have hu₀_orth : Orthonormal ℂ (fun a : Kpos => u₀ a.1) := by
    rw [orthonormal_iff_ite]
    intro a b
    have ha : 0 < s a.1 := (Finset.mem_filter.1 a.2).2
    change @inner ℂ _ _ (u₀ a.1).1 (u₀ b.1).1 = _
    simp only [u₀, SetLike.val_smul, inner_smul_left, inner_smul_right]
    have hin : @inner ℂ _ _
        (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) v (b₂ a.1).1)
        (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) v (b₂ b.1).1) =
        (μ b.1 : ℂ) * @inner ℂ _ _ (b₂ a.1) (b₂ b.1) := by
      rw [inner_toEuclideanCLM v, ← toEuclideanCLM_mul_apply]
      change @inner ℂ _ _ (TA (b₂ a.1)) (b₂ b.1) = _
      rw [hTA_symm, hμ_ev b.1]
      change @inner ℂ _ _ (b₂ a.1).1 ((μ b.1 : ℂ) • (b₂ b.1).1) = _
      rw [inner_smul_right]; rfl
    rw [hin]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, orthonormal_inner_self b₂.orthonormal a.1, mul_one]
      have hne : (s a.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt ha)
      have hstar : starRingEnd ℂ ((s a.1 : ℂ)⁻¹) = (s a.1 : ℂ)⁻¹ := by
        rw [map_inv₀, Complex.conj_ofReal]
      rw [hstar, ← hs_sq a.1, Complex.ofReal_pow]
      field_simp [hne]
    · have hne : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
      rw [if_neg hab, b₂.orthonormal.2 hne, mul_zero, mul_zero, mul_zero]
  have hKpos_le : Kpos.card ≤ min r₁ r₂ := by
    refine le_min ?_ ?_
    · have hli := hu₀_orth.linearIndependent
      simpa [Fintype.card_coe] using hli.fintype_card_le_finrank
    · calc Kpos.card ≤ (Finset.univ : Finset (Fin r₂)).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = r₂ := by simp
  have hact : ∀ a : Fin r₂,
      Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) v (b₂ a).1 = (s a : ℂ) • (u₀ a).1 := fun a => by
    by_cases ha : 0 < s a
    · have hne : (s a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt ha)
      simp only [u₀, SetLike.val_smul, smul_smul, mul_inv_cancel₀ hne, one_smul]
    · have hs0 : s a = 0 := le_antisymm (not_lt.1 ha) (hs_nn a)
      have hμ0 : μ a = 0 := by rw [← hs_sq a, hs0]; norm_num
      have hnorm0 : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) v (b₂ a).1‖ ^ 2 = 0 := by
        rw [← hTA_nonneg (b₂ a), hμ_ev a, hμ0]
        simp
      have hv0 : Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) v (b₂ a).1 = 0 := by
        rw [← norm_eq_zero]
        nlinarith [norm_nonneg (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) v (b₂ a).1)]
      rw [hv0, hs0, Complex.ofReal_zero, zero_smul]
  exact ⟨b₂, s, Kpos, u₀, hs_nn, fun a => by simp [Kpos], hKpos_le, hu₀_orth, hact⟩

/-- Block SVD with rank-`t` orthonormal extension (`t = min (rank e₁) (rank e₂)`). -/
lemma exists_block_svd {k : ℕ} {e₁ e₂ v : Mat k}
    (h1a : star e₁ = e₁) (h1b : e₁ * e₁ = e₁)
    (h2a : star e₂ = e₂) (h2b : e₂ * e₂ = e₂)
    (hv : e₁ * v * e₂ = v) :
    ∃ (r₂ : ℕ) (J : Finset (Fin r₂)) (s : Fin r₂ → ℝ) (u φ : Fin r₂ → Vec k),
      J.card = min (Module.finrank ℂ (projRange e₁)) (Module.finrank ℂ (projRange e₂)) ∧
      (∀ a, 0 ≤ s a) ∧
      (∀ a, a ∉ J → s a = 0) ∧
      (∀ a ∈ J, u a ∈ projRange e₁ ∧ φ a ∈ projRange e₂) ∧
      Orthonormal ℂ (fun a : J => u a.1) ∧
      Orthonormal ℂ (fun a : J => φ a.1) ∧
      v = ∑ a ∈ J, (s a : ℂ) • rankOne (u a) (φ a) := by
  classical
  let r₁ := Module.finrank ℂ (projRange e₁)
  let r₂ := Module.finrank ℂ (projRange e₂)
  let t := min r₁ r₂
  have hv_r : v * e₂ = v := by
    calc v * e₂ = (e₁ * v * e₂) * e₂ := by rw [hv]
      _ = e₁ * v * (e₂ * e₂) := by noncomm_ring
      _ = v := by rw [h2b, hv]
  obtain ⟨b₂, s, Kpos, u₀, hs_nn, hKpos_iff, hKpos_le_t, hu₀_orth, hact⟩ :=
    exists_block_svd_pos h1a h1b h2a h2b hv
  have ht_le_r₂ : t ≤ r₂ := min_le_right _ _
  have ht_le_r₁ : t ≤ r₁ := min_le_left _ _
  obtain ⟨J, hKposJ, hJcard⟩ := finset_exists_superset_card_eq Kpos hKpos_le_t
    (by simp)
  have hu₀_inj : Function.Injective (fun a : Kpos => u₀ a.1) :=
    hu₀_orth.linearIndependent.injective
  let S₀ : Set (projRange e₁) := Set.range (fun a : Kpos => u₀ a.1)
  have hS₀_orth : Orthonormal ℂ ((↑) : S₀ → projRange e₁) :=
    (orthonormal_subtype_range hu₀_inj).2 hu₀_orth
  obtain ⟨U, b₁, hS₀U, hb₁⟩ := hS₀_orth.exists_orthonormalBasis_extension
  have hUcard : U.card = r₁ := (Module.finrank_eq_card_finset_basis b₁.toBasis).symm
  let U₀ : Finset (projRange e₁) := Kpos.image u₀
  have hU₀sub : U₀ ⊆ U := by
    intro x hx
    rcases Finset.mem_image.1 hx with ⟨a, ha, rfl⟩
    exact hS₀U ⟨⟨a, ha⟩, rfl⟩
  have hU₀card : U₀.card = Kpos.card := by
    rw [Finset.card_image_iff]
    intro a ha b hb hab
    exact congrArg Subtype.val (hu₀_inj (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
  have hdiff_le : (J \ Kpos).card ≤ (U \ U₀).card := by
    rw [Finset.card_sdiff_of_subset hKposJ, Finset.card_sdiff_of_subset hU₀sub, hJcard, hUcard,
      hU₀card]
    omega
  have hcard_le : Fintype.card (↥(J \ Kpos)) ≤ Fintype.card (↥(U \ U₀)) := by
    rw [Fintype.card_coe, Fintype.card_coe]
    exact hdiff_le
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard_le
  let u_sub : Fin r₂ → projRange e₁ := fun a =>
    if ha : a ∈ Kpos then u₀ a
    else if haJ : a ∈ J then (emb ⟨a, Finset.mem_sdiff.2 ⟨haJ, ha⟩⟩).1
    else 0
  let u : Fin r₂ → Vec k := fun a => (u_sub a).1
  let φ : Fin r₂ → Vec k := fun a => (b₂ a).1
  have hu_mem : ∀ a ∈ J, u a ∈ projRange e₁ := fun a _ => (u_sub a).2
  have hφ_mem : ∀ a ∈ J, φ a ∈ projRange e₂ := fun a _ => (b₂ a).2
  have hu_in_U : ∀ a : J, u_sub a.1 ∈ U := fun a => by
    dsimp only [u_sub]
    split_ifs with ha haJ
    · exact hS₀U ⟨⟨a.1, ha⟩, rfl⟩
    · exact (Finset.mem_sdiff.1 (emb ⟨a.1, Finset.mem_sdiff.2 ⟨haJ, ha⟩⟩).2).1
    · exact absurd a.2 haJ
  have hu_inj : Function.Injective (fun a : J => u_sub a.1) := by
    intro a b hab
    by_cases ha : a.1 ∈ Kpos <;> by_cases hb : b.1 ∈ Kpos
    · simp only [u_sub, dif_pos ha, dif_pos hb] at hab
      have heq : (⟨a.1, ha⟩ : ↥Kpos) = ⟨b.1, hb⟩ :=
        hu₀_inj (a₁ := ⟨a.1, ha⟩) (a₂ := ⟨b.1, hb⟩) hab
      exact Subtype.ext (congrArg (fun x : ↥Kpos => x.1) heq)
    · simp only [u_sub, dif_pos ha, dif_neg hb, dif_pos b.2] at hab
      have hmem : (emb ⟨b.1, Finset.mem_sdiff.2 ⟨b.2, hb⟩⟩).1 ∈ U₀ := by
        rw [← hab]
        exact Finset.mem_image.2 ⟨a.1, ha, rfl⟩
      exact absurd hmem (Finset.mem_sdiff.1 (emb ⟨b.1, Finset.mem_sdiff.2 ⟨b.2, hb⟩⟩).2).2
    · simp only [u_sub, dif_neg ha, dif_pos a.2, dif_pos hb] at hab
      have hmem : (emb ⟨a.1, Finset.mem_sdiff.2 ⟨a.2, ha⟩⟩).1 ∈ U₀ := by
        rw [hab]
        exact Finset.mem_image.2 ⟨b.1, hb, rfl⟩
      exact absurd hmem (Finset.mem_sdiff.1 (emb ⟨a.1, Finset.mem_sdiff.2 ⟨a.2, ha⟩⟩).2).2
    · simp only [u_sub, dif_neg ha, dif_pos a.2, dif_neg hb, dif_pos b.2] at hab
      have heq : (⟨a.1, Finset.mem_sdiff.2 ⟨a.2, ha⟩⟩ : ↥(J \ Kpos)) =
          ⟨b.1, Finset.mem_sdiff.2 ⟨b.2, hb⟩⟩ := emb.injective (Subtype.ext hab)
      exact Subtype.ext (congrArg (fun x : ↥(J \ Kpos) => x.1) heq)
  have hu_orth : Orthonormal ℂ (fun a : J => u a.1) := by
    rw [orthonormal_iff_ite]
    intro a b
    have haU : u_sub a.1 = b₁ ⟨u_sub a.1, hu_in_U a⟩ := by
      have := congrFun hb₁ ⟨u_sub a.1, hu_in_U a⟩
      simpa using this.symm
    have hbU : u_sub b.1 = b₁ ⟨u_sub b.1, hu_in_U b⟩ := by
      have := congrFun hb₁ ⟨u_sub b.1, hu_in_U b⟩
      simpa using this.symm
    change @inner ℂ _ _ (u_sub a.1) (u_sub b.1) = _
    rw [haU, hbU]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl]
      exact orthonormal_inner_self b₁.orthonormal _
    · rw [if_neg hab]
      refine b₁.orthonormal.2 fun h => hab (hu_inj ?_)
      exact congrArg Subtype.val h
  have hφ_orth : Orthonormal ℂ (fun a : J => φ a.1) := by
    rw [orthonormal_iff_ite]
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl]
      exact orthonormal_inner_self b₂.orthonormal a.1
    · rw [if_neg hab]
      exact b₂.orthonormal.2 (fun h => hab (Subtype.ext h))
  have hs_zero_outside : ∀ a, a ∉ J → s a = 0 := fun a haJ => by
    by_contra hne
    have hpos : 0 < s a := lt_of_le_of_ne (hs_nn a) (Ne.symm hne)
    exact haJ (hKposJ ((hKpos_iff a).2 hpos))
  have hv_eq : v = ∑ a ∈ J, (s a : ℂ) • rankOne (u a) (φ a) := by
    have hclm : Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) v =
        Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ)
          (∑ a ∈ J, (s a : ℂ) • rankOne (u a) (φ a)) := by
      refine ContinuousLinearMap.ext fun ξ => ?_
      let ξ₁ : projRange e₂ := ⟨Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) e₂ ξ, ⟨ξ, rfl⟩⟩
      have hvξ : Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) v ξ =
          Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) v ξ₁.1 := by
        conv_lhs => rw [← hv_r]
        rw [toEuclideanCLM_mul_apply]
      have hinner : ∀ a : Fin r₂, @inner ℂ _ _ (φ a) ξ = @inner ℂ _ _ (b₂ a) ξ₁ := fun a => by
        have hb : Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) e₂ (b₂ a).1 = (b₂ a).1 :=
          (mem_projRange_iff h2b _).1 (b₂ a).2
        calc @inner ℂ _ _ (b₂ a).1 ξ
            = @inner ℂ _ _ (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (star e₂) (b₂ a).1) ξ := by
              rw [h2a, hb]
          _ = @inner ℂ _ _ (b₂ a).1 (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) e₂ ξ) :=
              (inner_toEuclideanCLM e₂ _ _).symm
          _ = @inner ℂ _ _ (b₂ a) ξ₁ := rfl
      have haction : ∀ a : Fin r₂,
          Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) v (b₂ a).1 = (s a : ℂ) • u a := fun a => by
        by_cases ha : a ∈ Kpos
        · simp only [u, u_sub, dif_pos ha]
          exact hact a
        · have hs0 : s a = 0 := le_antisymm (not_lt.1 (mt (hKpos_iff a).2 ha)) (hs_nn a)
          rw [hact a, hs0, Complex.ofReal_zero, zero_smul, zero_smul]
      rw [hvξ, ← b₂.sum_repr' ξ₁, AddSubmonoidClass.coe_finsetSum, map_sum, map_sum,
        _root_.sum_apply]
      have hLHS : ∑ a : Fin r₂,
          Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) v ((@inner ℂ _ _ (b₂ a) ξ₁ • b₂ a : projRange e₂) : Vec k) =
          ∑ a : Fin r₂, ((@inner ℂ _ _ (b₂ a) ξ₁) * (s a : ℂ)) • u a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [SetLike.val_smul, map_smul, haction a, smul_smul]
      rw [hLHS]
      have hRHS : ∑ a ∈ J, Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ)
          ((s a : ℂ) • rankOne (u a) (φ a)) ξ =
          ∑ a ∈ J, ((@inner ℂ _ _ (b₂ a) ξ₁) * (s a : ℂ)) • u a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [map_smul, _root_.smul_apply, toEuclideanCLM_rankOne, hinner a, smul_smul,
          mul_comm]
      rw [hRHS]
      symm
      refine Finset.sum_subset (Finset.subset_univ J) fun a _ haJ => ?_
      rw [hs_zero_outside a haJ, Complex.ofReal_zero, mul_zero, zero_smul]
    exact (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ)).injective hclm
  exact ⟨r₂, J, s, u, φ, hJcard, hs_nn, hs_zero_outside,
    fun a ha => ⟨hu_mem a ha, hφ_mem a ha⟩, hu_orth, hφ_orth, hv_eq⟩

/-- Cauchy-Schwarz fourth-moment lower bound from block SVD:
`(ss v)^2 ≤ min(rank e₁, rank e₂) * ss (star v * v)`. -/
lemma block_fourth_moment_ge {k : ℕ} {e₁ e₂ v : Mat k}
    (h1a : star e₁ = e₁) (h1b : e₁ * e₁ = e₁)
    (h2a : star e₂ = e₂) (h2b : e₂ * e₂ = e₂)
    (hv : e₁ * v * e₂ = v) :
    (ss v) ^ 2 ≤
      (min (Module.finrank ℂ (projRange e₁)) (Module.finrank ℂ (projRange e₂)) : ℝ) *
        ss (star v * v) := by
  obtain ⟨r₂, J, s, u, φ, hJcard, hs_nn, _, _, hu_orth, hφ_orth, hv_eq⟩ :=
    exists_block_svd h1a h1b h2a h2b hv
  have hv_coe : v = ∑ a : J, (s a.1 : ℂ) • rankOne (u a.1) (φ a.1) := by
    rw [hv_eq, ← Finset.sum_coe_sort J]
  have hss : ss v = ∑ a : J, s a.1 ^ 2 := by
    rw [hv_coe, sum_rankOne_ss hu_orth hφ_orth]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (hs_nn a.1)]
  have h4 : ss (star v * v) = ∑ a : J, (s a.1 ^ 2) ^ 2 := by
    rw [hv_coe, sum_rankOne_fourth_moment hu_orth hφ_orth]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (hs_nn a.1)]
    ring
  have hJcard' : (J.card : ℝ) =
      min (Module.finrank ℂ (projRange e₁) : ℝ) (Module.finrank ℂ (projRange e₂) : ℝ) := by
    rw [hJcard, Nat.cast_min]
  rw [hss, h4, ← hJcard']
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset J)) (f := fun a : J => s a.1 ^ 2)
  simpa [Fintype.card_coe] using hcs

/-- Singular-value clipping of `v ∈ B(e₁, e₂)` at threshold `R > 0`. -/
lemma exists_block_clip {k : ℕ} {e₁ e₂ v : Mat k}
    (h1a : star e₁ = e₁) (h1b : e₁ * e₁ = e₁)
    (h2a : star e₂ = e₂) (h2b : e₂ * e₂ = e₂)
    (hv : e₁ * v * e₂ = v) {R : ℝ} (hR : 0 < R) :
    ∃ vR : Mat k,
      e₁ * vR * e₂ = vR ∧
      ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) vR‖ ≤ R ∧
      ss (v - vR) ≤ ss (star v * v) / R ^ 2 := by
  obtain ⟨r₂, J, s, u, φ, _, hs_nn, _, hmem, hu_orth, hφ_orth, hv_eq⟩ :=
    exists_block_svd h1a h1b h2a h2b hv
  let vR : Mat k := ∑ a : J, ((min (s a.1) R : ℝ) : ℂ) • rankOne (u a.1) (φ a.1)
  have hblock : e₁ * vR * e₂ = vR := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, mul_rankOne, rankOne_mul, h2a,
      (mem_projRange_iff h1b _).1 (hmem a.1 a.2).1,
      (mem_projRange_iff h2b _).1 (hmem a.1 a.2).2]
  have hop : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) vR‖ ≤ R := by
    refine sum_rankOne_opNorm_le hu_orth hφ_orth _ (le_of_lt hR) fun a => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (le_min (hs_nn a.1) (le_of_lt hR))]
    exact min_le_right _ _
  have hdiff : v - vR =
      ∑ a : J, (((s a.1 - min (s a.1) R : ℝ) : ℂ)) • rankOne (u a.1) (φ a.1) := by
    rw [hv_eq, ← Finset.sum_coe_sort J]
    simp only [vR, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← sub_smul, Complex.ofReal_sub]
  have h4 : ss (star v * v) = ∑ a : J, s a.1 ^ 4 := by
    rw [hv_eq, ← Finset.sum_coe_sort J, sum_rankOne_fourth_moment hu_orth hφ_orth]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (hs_nn a.1)]
  have hss_diff : ss (v - vR) ≤ ss (star v * v) / R ^ 2 := by
    rw [hdiff, sum_rankOne_ss hu_orth hφ_orth, h4, Finset.sum_div]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.2 (min_le_left _ _))]
    by_cases hle : s a.1 ≤ R
    · rw [min_eq_left hle, sub_self, zero_pow two_ne_zero]
      positivity
    · push Not at hle
      rw [min_eq_right (le_of_lt hle), le_div_iff₀ (sq_pos_of_pos hR)]
      have h1 : (s a.1 - R) ^ 2 ≤ s a.1 ^ 2 := by nlinarith [hs_nn a.1]
      have h2 : s a.1 ^ 2 * R ^ 2 ≤ s a.1 ^ 4 := by
        have : R ^ 2 ≤ s a.1 ^ 2 := by nlinarith [hs_nn a.1]
        nlinarith [sq_nonneg (s a.1)]
      nlinarith [sq_nonneg R]
  exact ⟨vR, hblock, hop, hss_diff⟩

/-- Rank-`t` polar completion of `v ∈ B(e₁, e₂)`. -/
lemma exists_block_polar {k : ℕ} {e₁ e₂ v : Mat k}
    (h1a : star e₁ = e₁) (h1b : e₁ * e₁ = e₁)
    (h2a : star e₂ = e₂) (h2b : e₂ * e₂ = e₂)
    (hv : e₁ * v * e₂ = v) :
    ∃ u : Mat k,
      let t := min (Module.finrank ℂ (projRange e₁)) (Module.finrank ℂ (projRange e₂))
      e₁ * u * e₂ = u ∧
      ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) u‖ ≤ 1 ∧
      star (star u * u) = star u * u ∧
      (star u * u) * (star u * u) = star u * u ∧
      e₂ * (star u * u) * e₂ = star u * u ∧
      (star u * u).trace = (t : ℂ) ∧
      star (u * star u) = u * star u ∧
      (u * star u) * (u * star u) = u * star u ∧
      e₁ * (u * star u) * e₁ = u * star u ∧
      (u * star u).trace = (t : ℂ) ∧
      ss (v - u) ≤ ss (star v * v) - 2 * ss v + (t : ℝ) := by
  obtain ⟨r₂, J, s, u, φ, hJcard, hs_nn, _, hmem, hu_orth, hφ_orth, hv_eq⟩ :=
    exists_block_svd h1a h1b h2a h2b hv
  let t := min (Module.finrank ℂ (projRange e₁)) (Module.finrank ℂ (projRange e₂))
  let U : Mat k := ∑ a : J, (1 : ℂ) • rankOne (u a.1) (φ a.1)
  have hU_block : e₁ * U * e₂ = U := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [one_smul, mul_rankOne, rankOne_mul, h2a,
      (mem_projRange_iff h1b _).1 (hmem a.1 a.2).1,
      (mem_projRange_iff h2b _).1 (hmem a.1 a.2).2]
  have hU_op : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) U‖ ≤ 1 := by
    refine sum_rankOne_opNorm_le hu_orth hφ_orth _ zero_le_one fun _ => by simp
  have hU_su : star U * U = ∑ a : J, rankOne (φ a.1) (φ a.1) := by
    rw [sum_rankOne_star_mul hu_orth]
    refine Finset.sum_congr rfl fun a _ => by simp
  have hU_us : U * star U = ∑ a : J, rankOne (u a.1) (u a.1) := by
    rw [sum_rankOne_mul_star hφ_orth]
    refine Finset.sum_congr rfl fun a _ => by simp
  have hsu_sa : star (star U * U) = star U * U := by simp [star_mul]
  have hus_sa : star (U * star U) = U * star U := by simp [star_mul]
  have hsu_sq : (star U * U) * (star U * U) = star U * U := by
    rw [hU_su]
    have h := sum_rankOne_star_mul (u := fun a : J => φ a.1) (φ := fun a : J => φ a.1)
      hφ_orth (fun _ : J => (1 : ℂ))
    have h1 : ∑ a : J, (1 : ℂ) • rankOne (φ a.1) (φ a.1) =
        ∑ a : J, rankOne (φ a.1) (φ a.1) := by simp
    have hstar : star (∑ a : J, rankOne (φ a.1) (φ a.1)) =
        ∑ a : J, rankOne (φ a.1) (φ a.1) := by
      rw [star_sum]; refine Finset.sum_congr rfl fun a _ => star_rankOne _ _
    rw [h1, hstar] at h
    simpa using h
  have hus_sq : (U * star U) * (U * star U) = U * star U := by
    rw [hU_us]
    have h := sum_rankOne_star_mul (u := fun a : J => u a.1) (φ := fun a : J => u a.1)
      hu_orth (fun _ : J => (1 : ℂ))
    have h1 : ∑ a : J, (1 : ℂ) • rankOne (u a.1) (u a.1) =
        ∑ a : J, rankOne (u a.1) (u a.1) := by simp
    have hstar : star (∑ a : J, rankOne (u a.1) (u a.1)) =
        ∑ a : J, rankOne (u a.1) (u a.1) := by
      rw [star_sum]; refine Finset.sum_congr rfl fun a _ => star_rankOne _ _
    rw [h1, hstar] at h
    simpa using h
  have hsu_corner : e₂ * (star U * U) * e₂ = star U * U := by
    rw [hU_su, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_rankOne, rankOne_mul, h2a, (mem_projRange_iff h2b _).1 (hmem a.1 a.2).2]
  have hus_corner : e₁ * (U * star U) * e₁ = U * star U := by
    rw [hU_us, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_rankOne, rankOne_mul, h1a, (mem_projRange_iff h1b _).1 (hmem a.1 a.2).1]
  have hsu_tr : (star U * U).trace = (t : ℂ) := by
    rw [hU_su, Matrix.trace_sum]
    have ht : ∀ a : J, (rankOne (φ a.1) (φ a.1)).trace = 1 := fun a => by
      rw [trace_rankOne]; exact orthonormal_inner_self hφ_orth a
    simp_rw [ht, Finset.sum_const, Finset.card_univ, Fintype.card_coe, hJcard, nsmul_eq_mul,
      mul_one]
    rfl
  have hus_tr : (U * star U).trace = (t : ℂ) := by
    rw [hU_us, Matrix.trace_sum]
    have ht : ∀ a : J, (rankOne (u a.1) (u a.1)).trace = 1 := fun a => by
      rw [trace_rankOne]; exact orthonormal_inner_self hu_orth a
    simp_rw [ht, Finset.sum_const, Finset.card_univ, Fintype.card_coe, hJcard, nsmul_eq_mul,
      mul_one]
    rfl
  have hdiff : v - U = ∑ a : J, (((s a.1 - 1 : ℝ) : ℂ)) • rankOne (u a.1) (φ a.1) := by
    rw [hv_eq, ← Finset.sum_coe_sort J]
    simp only [U, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← sub_smul, Complex.ofReal_sub, Complex.ofReal_one]
  have hss_v : ss v = ∑ a : J, s a.1 ^ 2 := by
    rw [hv_eq, ← Finset.sum_coe_sort J, sum_rankOne_ss hu_orth hφ_orth]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (hs_nn a.1)]
  have h4 : ss (star v * v) = ∑ a : J, s a.1 ^ 4 := by
    rw [hv_eq, ← Finset.sum_coe_sort J, sum_rankOne_fourth_moment hu_orth hφ_orth]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (hs_nn a.1)]
  have hdist : ss (v - U) ≤ ss (star v * v) - 2 * ss v + (t : ℝ) := by
    rw [hdiff, sum_rankOne_ss hu_orth hφ_orth, h4, hss_v]
    have ht_sum : (t : ℝ) = ∑ _a : J, (1 : ℝ) := by
      simp [hJcard, t]
    rw [ht_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hnn := hs_nn a.1
    nlinarith [sq_nonneg (s a.1 - 1), sq_nonneg (s a.1)]
  exact ⟨U, hU_block, hU_op, hsu_sa, hsu_sq, hsu_corner, hsu_tr, hus_sa, hus_sq, hus_corner,
    hus_tr, hdist⟩

/- ### Section 2: Channel setup, Kadison-Schwarz, mid-spectrum defect, and energy seminorm -/

structure ChannelCtx (k m L : ℕ) where
  hk : 0 < k
  e : Fin m → Mat k
  he_sa : ∀ i, star (e i) = e i
  he_sq : ∀ i, e i * e i = e i
  he_ne : ∀ i, e i ≠ 0
  he_orth : ∀ i j, i ≠ j → e i * e j = 0
  he_sum : ∑ i, e i = 1
  w : Fin L → ℝ
  V : Fin L → Matrix.unitaryGroup (Fin k) ℂ
  hw : ∀ s, 0 ≤ w s
  hw_sum : ∑ s, w s = 1
  hV_comm : ∀ s i, (V s : Mat k) * e i = e i * (V s : Mat k)
  hF_sa : ∀ x : Mat k,
    (∑ s : Fin L, (w s : ℂ) • (star (V s : Mat k) * x * (V s : Mat k))) =
    (∑ s : Fin L, (w s : ℂ) • ((V s : Mat k) * x * star (V s : Mat k)))
  hF_pos : ∀ x : Mat k,
    0 ≤ ((star x * (∑ s : Fin L, (w s : ℂ) • (star (V s : Mat k) * x * (V s : Mat k)))).trace).re
  δ₀ : ℝ
  σ₀ : ℝ
  ρ : ℝ
  hδ₀_nn : 0 ≤ δ₀
  hσ₀_nn : 0 ≤ σ₀
  hρ_pos : 0 < ρ
  hρ_small : ρ ≤ 1 / 10000
  hδ₀_le : δ₀ ≤ ρ ^ 8
  hσ₀_le : σ₀ ≤ ρ ^ 8
  hδ_bound : ∀ x : Mat k, ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ≤ 1 →
    let F := fun y : Mat k => ∑ s : Fin L, (w s : ℂ) • (star (V s : Mat k) * y * (V s : Mat k))
    ss (F (F x) - F x) ≤ δ₀ * (k : ℝ)
  hσ_bound : ∀ i (x : Mat k), e i * x * e i = x →
    let F := fun y : Mat k => ∑ s : Fin L, (w s : ℂ) • (star (V s : Mat k) * y * (V s : Mat k))
    ss (F x - (x.trace / (e i).trace) • e i) ≤ σ₀ * ss x

namespace ChannelCtx

variable {k m L : ℕ} (C : ChannelCtx k m L)

noncomputable def F (x : Mat k) : Mat k :=
  ∑ s : Fin L, (C.w s : ℂ) • (star (C.V s : Mat k) * x * (C.V s : Mat k))

noncomputable def rk (i : Fin m) : ℕ := Module.finrank ℂ (projRange (C.e i))

noncomputable def rkr (i : Fin m) : ℝ := (C.rk i : ℝ)

lemma rk_pos (i : Fin m) : 0 < C.rk i :=
  proj_finrank_pos (C.he_sa i) (C.he_sq i) (C.he_ne i)

lemma rkr_pos (i : Fin m) : 0 < C.rkr i :=
  Nat.cast_pos.2 (C.rk_pos i)

lemma e_trace (i : Fin m) : (C.e i).trace = (C.rk i : ℂ) :=
  proj_trace_eq_finrank (C.he_sa i) (C.he_sq i)

lemma e_re_trace (i : Fin m) : ((C.e i).trace).re = C.rkr i :=
  proj_re_trace_eq_finrank (C.he_sa i) (C.he_sq i)

lemma sum_rkr : ∑ i : Fin m, C.rkr i = (k : ℝ) := by
  have h1 : (∑ i : Fin m, C.e i).trace = (k : ℂ) := by
    rw [C.he_sum]
    simp [Matrix.trace]
  rw [Matrix.trace_sum] at h1
  have h2 := congrArg Complex.re h1
  simp only [Complex.re_sum, C.e_re_trace, Complex.natCast_re] at h2
  exact h2

lemma F_add (x y : Mat k) : C.F (x + y) = C.F x + C.F y := by
  simp only [F, mul_add, add_mul, smul_add, Finset.sum_add_distrib]

lemma F_sub (x y : Mat k) : C.F (x - y) = C.F x - C.F y := by
  simp only [F, mul_sub, sub_mul, smul_sub, Finset.sum_sub_distrib]

lemma F_smul (c : ℂ) (x : Mat k) : C.F (c • x) = c • C.F x := by
  simp only [F, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, smul_comm]

lemma F_zero : C.F 0 = 0 := by simp [F]

lemma F_star (x : Mat k) : C.F (star x) = star (C.F x) := by
  simp only [F, star_sum, star_smul, Complex.star_def, Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  rw [star_mul, star_mul, star_star]
  noncomm_ring

lemma F_sa (x y : Mat k) : (star (C.F x) * y).trace = (star x * C.F y).trace := by
  rw [F, unitary_mix_adjoint, ← C.hF_sa y]; rfl

lemma F_ss_le (x : Mat k) : ss (C.F x) ≤ ss x :=
  unitary_mix_ss_le C.w C.V C.hw C.hw_sum x

lemma F_opNorm_le (x : Mat k) :
    ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (C.F x)‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ :=
  unitary_mix_opNorm_le C.w C.V C.hw C.hw_sum x

lemma F_block (i j : Fin m) (x : Mat k) :
    C.F (C.e i * x * C.e j) = C.e i * C.F x * C.e j := by
  simp only [F, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  have h1 := comm_star_of_comm_unitary (C.V s).2 (C.hV_comm s i)
  have h2 := C.hV_comm s j
  calc star (C.V s : Mat k) * (C.e i * x * C.e j) * (C.V s : Mat k)
      = (star (C.V s : Mat k) * C.e i) * x * (C.e j * (C.V s : Mat k)) := by noncomm_ring
    _ = (C.e i * star (C.V s : Mat k)) * x * ((C.V s : Mat k) * C.e j) := by rw [h1, h2]
    _ = C.e i * (star (C.V s : Mat k) * x * (C.V s : Mat k)) * C.e j := by noncomm_ring

lemma F_fix_e (i : Fin m) : C.F (C.e i) = C.e i :=
  unitary_mix_fix C.w C.V C.hw_sum (fun s => C.hV_comm s i)

lemma F_sum {α : Type*} (S : Finset α) (f : α → Mat k) :
    C.F (∑ a ∈ S, f a) = ∑ a ∈ S, C.F (f a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [C.F_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, C.F_add, ih]

/-- Pairwise orthogonality of distinct `(i, j)` blocks under Hilbert-Schmidt trace. -/
lemma block_trace_eq_zero {i j i' j' : Fin m} {x y : Mat k}
    (hx : C.e i * x * C.e j = x) (hy : C.e i' * y * C.e j' = y)
    (hne : (i, j) ≠ (i', j')) :
    (star x * y).trace = 0 := by
  have hx' : star x = C.e j * star x * C.e i := by
    conv_lhs => rw [← hx]
    rw [star_mul, star_mul, C.he_sa i, C.he_sa j, mul_assoc]
  by_cases hi : i = i'
  · have hj : j ≠ j' := fun h => hne (Prod.ext hi h)
    calc (star x * y).trace
        = ((C.e j * star x * C.e i) * (C.e i' * y * C.e j')).trace := by rw [← hx', hy]
      _ = (C.e j * (star x * C.e i * C.e i' * y * C.e j')).trace := by simp only [mul_assoc]
      _ = (star x * C.e i * C.e i' * y * C.e j' * C.e j).trace := Matrix.trace_mul_comm _ _
      _ = (star x * C.e i * C.e i' * y * (C.e j' * C.e j)).trace := by simp only [mul_assoc]
      _ = 0 := by rw [C.he_orth j' j (Ne.symm hj), mul_zero, Matrix.trace_zero]
  · calc (star x * y).trace
        = ((C.e j * star x * C.e i) * (C.e i' * y * C.e j')).trace := by rw [← hx', hy]
      _ = (C.e j * (star x * ((C.e i * C.e i') * (y * C.e j')))).trace := by
          simp only [mul_assoc]
      _ = 0 := by rw [C.he_orth i i' hi, zero_mul, mul_zero, mul_zero, Matrix.trace_zero]

lemma ss_sum_blocks {S : Finset (Fin m × Fin m)} (f : Fin m × Fin m → Mat k)
    (hf : ∀ p ∈ S, C.e p.1 * f p * C.e p.2 = f p) :
    ss (∑ p ∈ S, f p) = ∑ p ∈ S, ss (f p) := by
  rw [ss_eq_re_trace, star_sum, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mul_sum, Matrix.trace_sum]
  have hterm : ∀ q ∈ S, (star (f p) * f q).trace =
      if q = p then (star (f p) * f p).trace else 0 := fun q hq => by
    by_cases hqp : q = p
    · subst hqp; rw [if_pos rfl]
    · rw [if_neg hqp]
      exact C.block_trace_eq_zero (hf p hp) (hf q hq) (Ne.symm hqp)
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' S p, if_pos hp, re_trace_star_mul_self]
  rfl

/-- Block subspace `B(i, j)` inside Hilbert-Schmidt Euclidean space. -/
noncomputable def blockSub (i j : Fin m) :
    Submodule ℂ (EuclideanSpace ℂ (Fin k × Fin k)) where
  carrier := {v | C.e i * toHS.symm v * C.e j = toHS.symm v}
  zero_mem' := by simp
  add_mem' {u v} hu hv := by
    change C.e i * (toHS.symm u + toHS.symm v) * C.e j = toHS.symm u + toHS.symm v
    rw [mul_add, add_mul, hu, hv]
  smul_mem' c {v} hv := by
    change C.e i * (c • toHS.symm v) * C.e j = c • toHS.symm v
    rw [mul_smul_comm, smul_mul_assoc, hv]

/-- Restriction of `F` as a symmetric endomorphism of `blockSub i j`. -/
noncomputable def blockEnd (i j : Fin m) : (C.blockSub i j) →ₗ[ℂ] (C.blockSub i j) where
  toFun v := ⟨toHS (C.F (toHS.symm v.1)), by
    change C.e i * toHS.symm (toHS (C.F (toHS.symm v.1))) * C.e j =
      toHS.symm (toHS (C.F (toHS.symm v.1)))
    rw [LinearEquiv.symm_apply_apply, ← C.F_block, v.2]⟩
  map_add' u v := by
    apply Subtype.ext
    change toHS (C.F (toHS.symm (u.1 + v.1))) =
      toHS (C.F (toHS.symm u.1)) + toHS (C.F (toHS.symm v.1))
    rw [map_add, C.F_add, map_add]
  map_smul' c v := by
    apply Subtype.ext
    change toHS (C.F (toHS.symm (c • v.1))) = c • toHS (C.F (toHS.symm v.1))
    rw [map_smul, C.F_smul, map_smul]

lemma blockEnd_isSymmetric (i j : Fin m) :
    @LinearMap.IsSymmetric ℂ (C.blockSub i j) _ _ _ (C.blockEnd i j) := fun u v => by
  change @inner ℂ _ _ (toHS (C.F (toHS.symm u.1))) (toHS (toHS.symm v.1)) =
    @inner ℂ _ _ (toHS (toHS.symm u.1)) (toHS (C.F (toHS.symm v.1)))
  rw [toHS_inner, toHS_inner, C.F_sa]

lemma blockEnd_eigenvalue_bounds
    {μ : ℝ} {v : Mat k} (hv_ne : v ≠ 0) (hv_ev : C.F v = (μ : ℂ) • v) :
    0 ≤ μ ∧ μ ≤ 1 := by
  have hss_pos : 0 < ss v := ss_pos_of_ne_zero hv_ne
  have h0 : 0 ≤ μ * ss v := by
    have h := C.hF_pos v
    change 0 ≤ ((star v * C.F v).trace).re at h
    rw [hv_ev, mul_smul_comm, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
      re_trace_star_mul_self] at h
    exact h
  have h1 : μ ^ 2 * ss v ≤ ss v := by
    have h := C.F_ss_le v
    rw [hv_ev, ss_smul', Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
    exact h
  constructor
  · nlinarith
  · nlinarith

/-- Kadison-Schwarz trace inequality for `F`:
`Re Tr((star v * v) * (star (F v) * F v)) ≤ Re Tr((star v * v) * F (star v * v))`. -/
lemma kadison_schwarz_trace (v : Mat k) :
    ((star v * v * (star (C.F v) * C.F v)).trace).re ≤
      ((star v * v * C.F (star v * v)).trace).re := by
  let D : Mat k := C.F (star v * v) - star (C.F v) * C.F v
  suffices hD : 0 ≤ ((star v * v * D).trace).re by
    simp only [D, mul_sub, Matrix.trace_sub, Complex.sub_re] at hD
    linarith
  have hcyc : (star v * v * D).trace = (v * D * star v).trace := by
    have ha : star v * v * D = star v * (v * D) := by noncomm_ring
    rw [ha, Matrix.trace_mul_comm]
  rw [hcyc, Matrix.trace, Complex.re_sum]
  refine Finset.sum_nonneg fun r _ => ?_
  let ξ : Fin k → ℂ := fun c => star (v r c)
  have hrow : (v * D * star v) r r = star ξ ⬝ᵥ (D *ᵥ ξ) := by
    simp only [Matrix.mul_apply, Matrix.star_apply, dotProduct, Matrix.mulVec, Pi.star_apply,
      star_star, ξ, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [Matrix.diag_apply, hrow]
  let η : Fin L → Fin k → ℂ := fun s =>
    (star (C.V s : Mat k) * v * (C.V s : Mat k)) *ᵥ ξ
  let μ : Fin k → ℂ := (C.F v) *ᵥ ξ
  have hμ_eq : ∀ a, μ a = ∑ s : Fin L, (C.w s : ℂ) * η s a := fun a => by
    simp only [μ, η, F, Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp_rw [mul_assoc, ← Finset.mul_sum]
  have hterm1 : star ξ ⬝ᵥ (C.F (star v * v) *ᵥ ξ) =
      ∑ s : Fin L, (C.w s : ℂ) * (star (η s) ⬝ᵥ η s) := by
    have hFmul : C.F (star v * v) *ᵥ ξ =
        ∑ s : Fin L, (C.w s : ℂ) •
          ((star (star (C.V s : Mat k) * v * (C.V s : Mat k)) *
            (star (C.V s : Mat k) * v * (C.V s : Mat k))) *ᵥ ξ) := by
      ext a
      simp only [F, Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, Finset.sum_apply, Pi.smul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      have hV := Unitary.mul_star_self_of_mem (C.V s).2
      have hsq : star (star (C.V s : Mat k) * v * (C.V s : Mat k)) *
          (star (C.V s : Mat k) * v * (C.V s : Mat k)) =
          star (C.V s : Mat k) * (star v * v) * (C.V s : Mat k) := by
        rw [star_mul, star_mul, star_star]
        calc star (C.V s : Mat k) * (star v * (C.V s : Mat k)) *
              (star (C.V s : Mat k) * v * (C.V s : Mat k))
            = star (C.V s : Mat k) * (star v *
                (((C.V s : Mat k) * star (C.V s : Mat k)) * (v * (C.V s : Mat k)))) := by
                simp only [mul_assoc]
          _ = star (C.V s : Mat k) * (star v * v) * (C.V s : Mat k) := by
              rw [hV, one_mul]; simp only [mul_assoc]
      rw [hsq]
      simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [hFmul, dotProduct_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [dotProduct_smul, smul_eq_mul]
    congr 1
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_eq_conjTranspose,
      ← Matrix.star_mulVec]
  have hterm2 : star ξ ⬝ᵥ ((star (C.F v) * C.F v) *ᵥ ξ) = star μ ⬝ᵥ μ := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_eq_conjTranspose,
      ← Matrix.star_mulVec]
  have hD_dot : star ξ ⬝ᵥ (D *ᵥ ξ) =
      (∑ s : Fin L, (C.w s : ℂ) * (star (η s) ⬝ᵥ η s)) - star μ ⬝ᵥ μ := by
    simp only [D, Matrix.sub_mulVec, dotProduct_sub, hterm1, hterm2]
  rw [hD_dot]
  have hvar : ((∑ s : Fin L, (C.w s : ℂ) * (star (η s) ⬝ᵥ η s)) - star μ ⬝ᵥ μ).re =
      ∑ s : Fin L, C.w s * ∑ a : Fin k, ‖η s a - μ a‖ ^ 2 := by
    have hdot_norm : ∀ z : Fin k → ℂ, (star z ⬝ᵥ z).re = ∑ a : Fin k, ‖z a‖ ^ 2 := fun z => by
      simp only [dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    have hexp : ∀ s : Fin L, ∑ a : Fin k, ‖η s a - μ a‖ ^ 2 =
        (star (η s) ⬝ᵥ η s).re - 2 * (star μ ⬝ᵥ η s).re + (star μ ⬝ᵥ μ).re := fun s => by
      change ∑ a : Fin k, ‖(η s - μ) a‖ ^ 2 = _
      rw [← hdot_norm (η s - μ)]
      have h1 : star (η s - μ) ⬝ᵥ (η s - μ) =
          star (η s) ⬝ᵥ η s - star (η s) ⬝ᵥ μ - star μ ⬝ᵥ η s + star μ ⬝ᵥ μ := by
        simp only [star_sub, sub_dotProduct, dotProduct_sub]; ring
      have hsym : (star (η s) ⬝ᵥ μ).re = (star μ ⬝ᵥ η s).re := by
        have hc : star (star (η s) ⬝ᵥ μ) = star μ ⬝ᵥ η s := by
          rw [star_dotProduct, star_star, dotProduct_comm]
        rw [← Complex.conj_re, ← Complex.star_def, hc]
      rw [h1, Complex.add_re, Complex.sub_re, Complex.sub_re, hsym]
      ring
    simp_rw [hexp, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, C.hw_sum, one_mul]
    have hcross : ∑ s : Fin L, C.w s * (2 * (star μ ⬝ᵥ η s).re) = 2 * (star μ ⬝ᵥ μ).re := by
      have h1 : ∑ s : Fin L, C.w s * (star μ ⬝ᵥ η s).re = (star μ ⬝ᵥ μ).re := by
        have h2 : (∑ s : Fin L, (C.w s : ℂ) * (star μ ⬝ᵥ η s)) = star μ ⬝ᵥ μ := by
          simp only [dotProduct, Finset.mul_sum, hμ_eq]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun s _ => by ring
        rw [← h2, Complex.re_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Complex.re_ofReal_mul]
      calc ∑ s : Fin L, C.w s * (2 * (star μ ⬝ᵥ η s).re)
          = 2 * ∑ s : Fin L, C.w s * (star μ ⬝ᵥ η s).re := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ => by ring
        _ = 2 * (star μ ⬝ᵥ μ).re := by rw [h1]
    rw [hcross, Complex.sub_re, Complex.re_sum]
    have hre_s : ∀ s : Fin L, ((C.w s : ℂ) * (star (η s) ⬝ᵥ η s)).re =
        C.w s * (star (η s) ⬝ᵥ η s).re := fun s => Complex.re_ofReal_mul _ _
    simp_rw [hre_s]
    ring
  rw [hvar]
  exact Finset.sum_nonneg fun s _ =>
    mul_nonneg (C.hw s) (Finset.sum_nonneg fun a _ => sq_nonneg _)

/-- Combined Kadison-Schwarz and diagonal-corner fourth-moment upper bound:
`(λ^2 - √σ₀) * ss (star v * v) ≤ (ss v)^2 / max (rkr i) (rkr j)`. -/
lemma fourth_moment_bound {i j : Fin m} {v : Mat k} {μ : ℝ}
    (hv : C.e i * v * C.e j = v) (hev : C.F v = (μ : ℂ) • v) :
    (μ ^ 2 - Real.sqrt C.σ₀) * ss (star v * v) ≤ (ss v) ^ 2 / max (C.rkr i) (C.rkr j) := by
  have hsingle : ∀ (i₀ j₀ : Fin m) (w : Mat k),
      C.e i₀ * w * C.e j₀ = w → C.F w = (μ : ℂ) • w →
      (μ ^ 2 - Real.sqrt C.σ₀) * ss (star w * w) ≤ (ss w) ^ 2 / C.rkr j₀ := by
    intro i₀ j₀ w hw hwev
    let a : Mat k := star w * w
    have ha_sa : star a = a := by simp [a, star_mul]
    have ha_block : C.e j₀ * a * C.e j₀ = a := by
      have hwr : w * C.e j₀ = w := by
        calc w * C.e j₀ = (C.e i₀ * w * C.e j₀) * C.e j₀ := by rw [hw]
          _ = C.e i₀ * w * (C.e j₀ * C.e j₀) := by noncomm_ring
          _ = w := by rw [C.he_sq j₀, hw]
      have hwl : C.e j₀ * star w = star w := by
        calc C.e j₀ * star w = star (w * C.e j₀) := by rw [star_mul, C.he_sa j₀]
          _ = star w := by rw [hwr]
      calc C.e j₀ * a * C.e j₀ = (C.e j₀ * star w) * (w * C.e j₀) := by simp only [a, mul_assoc]
        _ = a := by rw [hwl, hwr]
    have hks : μ ^ 2 * ss a ≤ ((a * C.F a).trace).re := by
      have h := C.kadison_schwarz_trace w
      have h1 : star (C.F w) * C.F w = ((μ ^ 2 : ℝ) : ℂ) • a := by
        rw [hwev, star_smul, Complex.star_def, Complex.conj_ofReal, smul_mul_assoc,
          mul_smul_comm, smul_smul, Complex.ofReal_pow, sq]
      rw [h1, mul_smul_comm, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul] at h
      have h2 : ((a * a).trace).re = ss a := by
        rw [ss_eq_re_trace, ha_sa]
      rw [h2] at h
      exact h
    let rem : Mat k := C.F a - (a.trace / (C.e j₀).trace) • C.e j₀
    have hrem : ss rem ≤ C.σ₀ * ss a := C.hσ_bound j₀ a ha_block
    have hsplit : ((a * C.F a).trace).re =
        (ss w) ^ 2 / C.rkr j₀ + ((star a * rem).trace).re := by
      have hFa : C.F a = (a.trace / (C.e j₀).trace) • C.e j₀ + rem :=
        (add_sub_cancel _ _).symm
      rw [hFa, mul_add, Matrix.trace_add, Complex.add_re, ha_sa]
      congr 1
      have hae : a * C.e j₀ = a := by
        calc a * C.e j₀ = (C.e j₀ * a * C.e j₀) * C.e j₀ := by rw [ha_block]
          _ = C.e j₀ * a * (C.e j₀ * C.e j₀) := by noncomm_ring
          _ = a := by rw [C.he_sq j₀, ha_block]
      rw [mul_smul_comm, hae, Matrix.trace_smul, smul_eq_mul, trace_star_mul_self_eq_ss,
        C.e_trace j₀, ← Complex.ofReal_natCast, ← Complex.ofReal_div, ← Complex.ofReal_mul,
        Complex.ofReal_re]
      change (ss w / C.rkr j₀) * ss w = (ss w) ^ 2 / C.rkr j₀
      ring
    have hrem_cs : ((star a * rem).trace).re ≤ Real.sqrt C.σ₀ * ss a := by
      calc ((star a * rem).trace).re
          ≤ |((star a * rem).trace).re| := le_abs_self _
        _ ≤ Real.sqrt (ss a) * Real.sqrt (ss rem) := abs_re_trace_star_mul_le a rem
        _ ≤ Real.sqrt (ss a) * Real.sqrt (C.σ₀ * ss a) := by
            gcongr
        _ = Real.sqrt C.σ₀ * (Real.sqrt (ss a) * Real.sqrt (ss a)) := by
            rw [Real.sqrt_mul C.hσ₀_nn]; ring
        _ = Real.sqrt C.σ₀ * ss a := by rw [Real.mul_self_sqrt (ss_nonneg a)]
    linarith
  have hj := hsingle i j v hv hev
  have hv_star_block : C.e j * star v * C.e i = star v := by
    conv_rhs => rw [← hv]
    rw [star_mul, star_mul, C.he_sa i, C.he_sa j]
    noncomm_ring
  have hv_star_ev : C.F (star v) = (μ : ℂ) • star v := by
    rw [C.F_star, hev, star_smul, Complex.star_def, Complex.conj_ofReal]
  have hi := hsingle j i (star v) hv_star_block hv_star_ev
  have hss_star : ss (star v) = ss v := ss_star v
  have h4_star : ss (star (star v) * star v) = ss (star v * v) := by
    rw [star_star, ss_eq_re_trace, ss_eq_re_trace, star_mul, star_mul, star_star]
    congr 1
    have h1 : (v * star v) * (v * star v) = v * (star v * v * star v) := by noncomm_ring
    rw [h1, Matrix.trace_mul_comm]
    congr 1; noncomm_ring
  rw [hss_star, h4_star] at hi
  rcases le_total (C.rkr i) (C.rkr j) with hle | hle
  · rwa [max_eq_right hle]
  · rwa [max_eq_left hle]

/-- Consequence of fourth-moment lower and upper bounds:
`λ^2 - √σ₀ ≤ min (rkr i) (rkr j) / max (rkr i) (rkr j)`. -/
lemma eigval_sq_sub_sigma_le_ratio {i j : Fin m} {v : Mat k} {μ : ℝ}
    (hv : C.e i * v * C.e j = v) (hv_ne : v ≠ 0) (hev : C.F v = (μ : ℂ) • v) :
    μ ^ 2 - Real.sqrt C.σ₀ ≤ min (C.rkr i) (C.rkr j) / max (C.rkr i) (C.rkr j) := by
  have hM_pos : 0 < max (C.rkr i) (C.rkr j) := lt_of_lt_of_le (C.rkr_pos i) (le_max_left _ _)
  have ht_pos : 0 < min (C.rkr i) (C.rkr j) := lt_min (C.rkr_pos i) (C.rkr_pos j)
  by_cases hneg : μ ^ 2 - Real.sqrt C.σ₀ ≤ 0
  · exact hneg.trans (div_nonneg (le_of_lt ht_pos) (le_of_lt hM_pos))
  · push Not at hneg
    have hup := C.fourth_moment_bound hv hev
    have hlo : (ss v) ^ 2 ≤ min (C.rkr i) (C.rkr j) * ss (star v * v) := by
      have h := block_fourth_moment_ge (C.he_sa i) (C.he_sq i) (C.he_sa j) (C.he_sq j) hv
      simpa [rkr, rk, Nat.cast_min] using h
    have hss_pos : 0 < ss v := ss_pos_of_ne_zero hv_ne
    have h1 : (μ ^ 2 - Real.sqrt C.σ₀) * ((ss v) ^ 2 / min (C.rkr i) (C.rkr j)) ≤
        (ss v) ^ 2 / max (C.rkr i) (C.rkr j) := by
      have h2 : (ss v) ^ 2 / min (C.rkr i) (C.rkr j) ≤ ss (star v * v) :=
        (div_le_iff₀ ht_pos).2 (by linarith)
      exact (mul_le_mul_of_nonneg_left h2 (le_of_lt hneg)).trans hup
    rw [le_div_iff₀ hM_pos]
    have h3 : (μ ^ 2 - Real.sqrt C.σ₀) * max (C.rkr i) (C.rkr j) * (ss v) ^ 2 ≤
        min (C.rkr i) (C.rkr j) * (ss v) ^ 2 := by
      have h4 := mul_le_mul_of_nonneg_right h1 (le_of_lt (mul_pos ht_pos hM_pos))
      have hL : (μ ^ 2 - Real.sqrt C.σ₀) * ((ss v) ^ 2 / min (C.rkr i) (C.rkr j)) *
          (min (C.rkr i) (C.rkr j) * max (C.rkr i) (C.rkr j)) =
          (μ ^ 2 - Real.sqrt C.σ₀) * max (C.rkr i) (C.rkr j) * (ss v) ^ 2 := by
        field_simp [ne_of_gt ht_pos, ne_of_gt hM_pos]
      have hR : (ss v) ^ 2 / max (C.rkr i) (C.rkr j) *
          (min (C.rkr i) (C.rkr j) * max (C.rkr i) (C.rkr j)) =
          min (C.rkr i) (C.rkr j) * (ss v) ^ 2 := by
        field_simp [ne_of_gt ht_pos, ne_of_gt hM_pos]
      linarith
    have hss2_pos : 0 < (ss v) ^ 2 := sq_pos_of_pos hss_pos
    nlinarith

/-- Mid-spectrum defect: any eigenvector in `B(i, j)` with `ρ < μ < 1 - ρ` produces a
contraction `x ∈ B(i, j)` with `ss (F (F x) - F x) ≥ ρ^4 * max(rkr i, rkr j) / 128`. -/
lemma mid_eigenvalue_defect {i j : Fin m} {v : Mat k} {μ : ℝ}
    (hv : C.e i * v * C.e j = v) (hv_ne : v ≠ 0) (hev : C.F v = (μ : ℂ) • v)
    (hlo : C.ρ < μ) (hhi : μ < 1 - C.ρ) :
    ∃ x : Mat k,
      C.e i * x * C.e j = x ∧
      ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ≤ 1 ∧
      C.ρ ^ 4 * max (C.rkr i) (C.rkr j) / 128 ≤ ss (C.F (C.F x) - C.F x) := by
  let M : ℝ := max (C.rkr i) (C.rkr j)
  have hM_pos : 0 < M := lt_of_lt_of_le (C.rkr_pos i) (le_max_left _ _)
  have hss_pos : 0 < ss v := ss_pos_of_ne_zero hv_ne
  -- Normalize `v` to `w` with `ss w = M`
  let scale : ℝ := Real.sqrt (M / ss v)
  have hscale_pos : 0 < scale := Real.sqrt_pos.2 (div_pos hM_pos hss_pos)
  let w : Mat k := (scale : ℂ) • v
  have hw_block : C.e i * w * C.e j = w := by
    simp only [w, mul_smul_comm, smul_mul_assoc, hv]
  have hw_ev : C.F w = (μ : ℂ) • w := by
    change C.F ((scale : ℂ) • v) = (μ : ℂ) • ((scale : ℂ) • v)
    rw [C.F_smul, hev, smul_comm]
  have hw_ss : ss w = M := by
    rw [show ss w = ‖(scale : ℂ)‖ ^ 2 * ss v from ss_smul _ _,
      Complex.norm_real, Real.norm_of_nonneg (le_of_lt hscale_pos),
      Real.sq_sqrt (le_of_lt (div_pos hM_pos hss_pos)), div_mul_cancel₀ _ (ne_of_gt hss_pos)]
  have hσ₁ : Real.sqrt C.σ₀ ≤ C.ρ ^ 4 := by
    have h1 : Real.sqrt C.σ₀ ≤ Real.sqrt (C.ρ ^ 8) := Real.sqrt_le_sqrt C.hσ₀_le
    have h2 : Real.sqrt (C.ρ ^ 8) = C.ρ ^ 4 := by
      rw [show C.ρ ^ 8 = (C.ρ ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    linarith
  have hρ_le_half : C.ρ ≤ 1 / 2 := by linarith [C.hρ_small]
  have hgap : C.ρ ^ 2 / 2 ≤ μ ^ 2 - Real.sqrt C.σ₀ := by
    have hρ2 : C.ρ ^ 2 ≤ μ ^ 2 := by nlinarith [C.hρ_pos]
    have hρsq : C.ρ ^ 2 ≤ 1 / 2 := by nlinarith [C.hρ_pos, C.hρ_small]
    have hρ4 : C.ρ ^ 4 ≤ C.ρ ^ 2 / 2 := by
      have h : C.ρ ^ 4 = C.ρ ^ 2 * C.ρ ^ 2 := by ring
      nlinarith [sq_nonneg C.ρ]
    linarith
  have hgap_pos : 0 < μ ^ 2 - Real.sqrt C.σ₀ :=
    lt_of_lt_of_le (div_pos (sq_pos_of_pos C.hρ_pos) two_pos) hgap
  have h4 : ss (star w * w) ≤ M / (μ ^ 2 - Real.sqrt C.σ₀) := by
    have h := C.fourth_moment_bound hw_block hw_ev
    rw [hw_ss] at h
    have hM2 : M ^ 2 / M = M := by field_simp [ne_of_gt hM_pos]
    rw [hM2] at h
    exact (le_div_iff₀ hgap_pos).2 (by linarith)
  let R : ℝ := 2 / Real.sqrt (μ ^ 2 - Real.sqrt C.σ₀)
  have hR_pos : 0 < R := div_pos two_pos (Real.sqrt_pos.2 hgap_pos)
  have hR_sq : R ^ 2 = 4 / (μ ^ 2 - Real.sqrt C.σ₀) := by
    simp only [R, div_pow, Real.sq_sqrt (le_of_lt hgap_pos)]
    norm_num
  obtain ⟨wR, hwR_block, hwR_op, hwR_diff⟩ :=
    exists_block_clip (C.he_sa i) (C.he_sq i) (C.he_sa j) (C.he_sq j) hw_block hR_pos
  have hdiff_le : ss (w - wR) ≤ M / 4 := by
    calc ss (w - wR) ≤ ss (star w * w) / R ^ 2 := hwR_diff
      _ ≤ (M / (μ ^ 2 - Real.sqrt C.σ₀)) / (4 / (μ ^ 2 - Real.sqrt C.σ₀)) := by
          rw [hR_sq]
          exact div_le_div_of_nonneg_right h4 (div_nonneg (by norm_num) (le_of_lt hgap_pos))
      _ = M / 4 := by field_simp [ne_of_gt hgap_pos]
  have hre_ge : M / 2 ≤ ((star w * wR).trace).re := by
    have hsub : ((star w * wR).trace).re = ss w - ((star w * (w - wR)).trace).re := by
      rw [mul_sub, Matrix.trace_sub, Complex.sub_re, ← ss_eq_re_trace]
      ring
    have hcs : ((star w * (w - wR)).trace).re ≤ M / 2 := by
      calc ((star w * (w - wR)).trace).re
          ≤ |((star w * (w - wR)).trace).re| := le_abs_self _
        _ ≤ Real.sqrt (ss w) * Real.sqrt (ss (w - wR)) := abs_re_trace_star_mul_le _ _
        _ ≤ Real.sqrt M * Real.sqrt (M / 4) := by
            rw [hw_ss]; gcongr
        _ = M / 2 := by
            rw [Real.sqrt_div (le_of_lt hM_pos),
              show Real.sqrt 4 = 2 by
                rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
              ← mul_div_assoc, Real.mul_self_sqrt (le_of_lt hM_pos)]
    linarith [hw_ss]
  have hinner_eq : ((star w * (C.F (C.F wR) - C.F wR)).trace).re =
      (μ ^ 2 - μ) * ((star w * wR).trace).re := by
    have h1 : (star w * C.F (C.F wR)).trace = ((μ ^ 2 : ℝ) : ℂ) * (star w * wR).trace := by
      rw [← C.F_sa, ← C.F_sa, hw_ev, C.F_smul, hw_ev, smul_smul, ← Complex.ofReal_mul,
        star_smul, Complex.star_def, Complex.conj_ofReal, smul_mul_assoc, Matrix.trace_smul,
        smul_eq_mul, sq]
    have h2 : (star w * C.F wR).trace = (μ : ℂ) * (star w * wR).trace := by
      rw [← C.F_sa, hw_ev, star_smul, Complex.star_def, Complex.conj_ofReal, smul_mul_assoc,
        Matrix.trace_smul, smul_eq_mul]
    rw [mul_sub, Matrix.trace_sub, h1, h2, Complex.sub_re, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul]
    ring
  have hμ_prod : C.ρ / 2 ≤ μ * (1 - μ) := by
    have h1 : C.ρ * (1 - C.ρ) ≤ μ * (1 - μ) := by nlinarith
    nlinarith [C.hρ_pos]
  have hdef_wR : ((C.ρ / 2) * (M / 2)) ^ 2 ≤ M * ss (C.F (C.F wR) - C.F wR) := by
    have habs : (C.ρ / 2) * (M / 2) ≤ |((star w * (C.F (C.F wR) - C.F wR)).trace).re| := by
      rw [hinner_eq, abs_mul, abs_of_nonpos (by nlinarith [C.hρ_pos]),
        abs_of_nonneg (by linarith)]
      have h1 : C.ρ / 2 ≤ -(μ ^ 2 - μ) := by linarith
      nlinarith [C.hρ_pos]
    have hcs : |((star w * (C.F (C.F wR) - C.F wR)).trace).re| ≤
        Real.sqrt M * Real.sqrt (ss (C.F (C.F wR) - C.F wR)) := by
      rw [← hw_ss]
      exact abs_re_trace_star_mul_le _ _
    have hnn : 0 ≤ (C.ρ / 2) * (M / 2) := mul_nonneg (div_nonneg (le_of_lt C.hρ_pos) (by norm_num))
      (div_nonneg (le_of_lt hM_pos) (by norm_num))
    calc ((C.ρ / 2) * (M / 2)) ^ 2
        ≤ (Real.sqrt M * Real.sqrt (ss (C.F (C.F wR) - C.F wR))) ^ 2 :=
          pow_le_pow_left₀ hnn (habs.trans hcs) 2
      _ = M * ss (C.F (C.F wR) - C.F wR) := by
          rw [mul_pow, Real.sq_sqrt (le_of_lt hM_pos), Real.sq_sqrt (ss_nonneg _)]
  let x : Mat k := ((R⁻¹ : ℝ) : ℂ) • wR
  have hx_block : C.e i * x * C.e j = x := by
    simp only [x, mul_smul_comm, smul_mul_assoc, hwR_block]
  have hx_op : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ≤ 1 := by
    rw [show x = ((R⁻¹ : ℝ) : ℂ) • wR from rfl, map_smul, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.2 (le_of_lt hR_pos))]
    calc R⁻¹ * ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) wR‖
        ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hwR_op (inv_nonneg.2 (le_of_lt hR_pos))
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hR_pos)
  have hx_def : C.ρ ^ 4 * M / 128 ≤ ss (C.F (C.F x) - C.F x) := by
    have hFx : C.F (C.F x) - C.F x = ((R⁻¹ : ℝ) : ℂ) • (C.F (C.F wR) - C.F wR) := by
      simp only [x, C.F_smul, smul_sub]
    rw [hFx, show ss (((R⁻¹ : ℝ) : ℂ) • _) = ‖((R⁻¹ : ℝ) : ℂ)‖ ^ 2 * ss _ from ss_smul _ _,
      Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (le_of_lt hR_pos)), inv_pow, hR_sq]
    have hss_wR : C.ρ ^ 2 * M / 16 ≤ ss (C.F (C.F wR) - C.F wR) := by
      nlinarith [hdef_wR]
    have hinv : (4 / (μ ^ 2 - Real.sqrt C.σ₀))⁻¹ = (μ ^ 2 - Real.sqrt C.σ₀) / 4 := by
      field_simp [ne_of_gt hgap_pos]
    rw [hinv]
    calc C.ρ ^ 4 * M / 128
        = (C.ρ ^ 2 / 2) / 4 * (C.ρ ^ 2 * M / 16) := by ring
      _ ≤ (μ ^ 2 - Real.sqrt C.σ₀) / 4 * ss (C.F (C.F wR) - C.F wR) := by
          exact mul_le_mul (div_le_div_of_nonneg_right hgap (by norm_num)) hss_wR
            (by positivity) (div_nonneg (le_of_lt hgap_pos) (by norm_num))
  exact ⟨x, hx_block, hx_op, hx_def⟩

/-- Dirichlet energy seminorm `E_F(x) = ss x - Re Tr(x^* F x) = (1/2) ∑ w_s ‖[V_s, x]‖_HS^2`. -/
noncomputable def energy (x : Mat k) : ℝ := ss x - ((star x * C.F x).trace).re

lemma energy_eq_comm_sum (x : Mat k) :
    C.energy x = (1 / 2 : ℝ) * ∑ s : Fin L, C.w s * ss ((C.V s : Mat k) * x - x * (C.V s : Mat k)) := by
  have h1 : ∀ s : Fin L,
      ((ss ((C.V s : Mat k) * x - x * (C.V s : Mat k)) : ℝ) : ℂ) =
        (star x * ((2 : ℂ) • x -
          (star (C.V s : Mat k) * x * (C.V s : Mat k) +
            (C.V s : Mat k) * x * star (C.V s : Mat k)))).trace :=
    fun s => ss_comm_unitary_eq (C.V s).2 x
  have h2 : ∑ s : Fin L, (C.w s : ℂ) * ((ss ((C.V s : Mat k) * x - x * (C.V s : Mat k)) : ℝ) : ℂ) =
      (2 : ℂ) * (star x * x).trace - (2 : ℂ) * (star x * C.F x).trace := by
    simp_rw [h1]
    have hsum : ∀ s : Fin L,
        (C.w s : ℂ) * (star x * ((2 : ℂ) • x -
          (star (C.V s : Mat k) * x * (C.V s : Mat k) +
            (C.V s : Mat k) * x * star (C.V s : Mat k)))).trace =
        (2 : ℂ) * (C.w s : ℂ) * (star x * x).trace -
        (star x * ((C.w s : ℂ) • (star (C.V s : Mat k) * x * (C.V s : Mat k)))).trace -
        (star x * ((C.w s : ℂ) • ((C.V s : Mat k) * x * star (C.V s : Mat k)))).trace := fun s => by
      rw [mul_sub, mul_add, mul_smul_comm, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul,
        smul_eq_mul, mul_smul_comm, mul_smul_comm, Matrix.trace_smul, Matrix.trace_smul,
        smul_eq_mul, smul_eq_mul]
      ring
    simp_rw [hsum, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      ← Complex.ofReal_sum, C.hw_sum, Complex.ofReal_one, mul_one, ← Matrix.trace_sum,
      ← Finset.mul_sum]
    have hF1 : ∑ s : Fin L, (C.w s : ℂ) • (star (C.V s : Mat k) * x * (C.V s : Mat k)) = C.F x := rfl
    have hF2 : ∑ s : Fin L, (C.w s : ℂ) • ((C.V s : Mat k) * x * star (C.V s : Mat k)) = C.F x :=
      (C.hF_sa x).symm
    rw [hF1, hF2]
    ring
  have hre := congrArg Complex.re h2
  simp only [Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.sub_re] at hre
  have hre2 : ∀ z : ℂ, ((2 : ℂ) * z).re = 2 * z.re := fun z => by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
  rw [hre2, hre2, re_trace_star_mul_self] at hre
  change _ = _ at hre
  unfold energy
  linarith [show ∑ a, ∑ b, ‖x a b‖ ^ 2 = ss x from rfl]

lemma energy_nonneg (x : Mat k) : 0 ≤ C.energy x := by
  rw [C.energy_eq_comm_sum]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun s _ => mul_nonneg (C.hw s) (ss_nonneg _))

lemma energy_le_ss (x : Mat k) : C.energy x ≤ ss x := by
  have h := C.hF_pos x
  change 0 ≤ ((star x * C.F x).trace).re at h
  unfold energy
  linarith

lemma energy_star (x : Mat k) : C.energy (star x) = C.energy x := by
  unfold energy
  rw [show ss (star x) = ss x from ss_star x, C.F_star, star_star]
  congr 1
  rw [Matrix.trace_mul_comm]
  exact re_trace_star_mul_comm (C.F x) x

lemma ss_F_sub_le_two_energy (x : Mat k) : ss (C.F x - x) ≤ 2 * C.energy x := by
  have hsub : ss (C.F x - x) = ss (C.F x) - 2 * ((star (C.F x) * x).trace).re + ss x :=
    ss_sub_eq (C.F x) x
  rw [C.F_sa] at hsub
  have hle := C.F_ss_le x
  unfold energy
  linarith

/-- Linear embedding realizing `√(energy x)` as an `ℓ²` norm. -/
noncomputable def energyVec (x : Mat k) : EuclideanSpace ℂ (Fin L × Fin k × Fin k) :=
  WithLp.toLp 2 (fun p : Fin L × Fin k × Fin k =>
    ((Real.sqrt (C.w p.1 / 2) : ℝ) : ℂ) *
      (((C.V p.1 : Mat k) * x - x * (C.V p.1 : Mat k)) p.2.1 p.2.2))

lemma energyVec_norm_sq (x : Mat k) : ‖C.energyVec x‖ ^ 2 = C.energy x := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, C.energy_eq_comm_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Fintype.sum_prod_type]
  have hterm : ∀ r c : Fin k,
      ‖(C.energyVec x).ofLp (s, r, c)‖ ^ 2 =
        (C.w s / 2) * ‖((C.V s : Mat k) * x - x * (C.V s : Mat k)) r c‖ ^ 2 := fun r c => by
    change ‖((Real.sqrt (C.w s / 2) : ℝ) : ℂ) *
      (((C.V s : Mat k) * x - x * (C.V s : Mat k)) r c)‖ ^ 2 = _
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (div_nonneg (C.hw s) (by norm_num))]
  simp_rw [hterm, ← Finset.mul_sum]
  change (C.w s / 2) * ss ((C.V s : Mat k) * x - x * (C.V s : Mat k)) = _
  ring

lemma energyVec_norm (x : Mat k) : ‖C.energyVec x‖ = Real.sqrt (C.energy x) := by
  rw [← Real.sqrt_sq (norm_nonneg _), C.energyVec_norm_sq]

lemma sqrt_energy_add_le (x y : Mat k) :
    Real.sqrt (C.energy (x + y)) ≤ Real.sqrt (C.energy x) + Real.sqrt (C.energy y) := by
  rw [← C.energyVec_norm, ← C.energyVec_norm, ← C.energyVec_norm]
  have hadd : C.energyVec (x + y) = C.energyVec x + C.energyVec y := by
    ext ⟨s, r, c⟩
    change ((Real.sqrt (C.w s / 2) : ℝ) : ℂ) *
      (((C.V s : Mat k) * (x + y) - (x + y) * (C.V s : Mat k)) r c) = _
    have hm : (C.V s : Mat k) * (x + y) - (x + y) * (C.V s : Mat k) =
        ((C.V s : Mat k) * x - x * (C.V s : Mat k)) +
        ((C.V s : Mat k) * y - y * (C.V s : Mat k)) := by noncomm_ring
    rw [hm, Matrix.add_apply, mul_add]
    rfl
  rw [hadd]
  exact norm_add_le _ _

lemma sqrt_energy_le_add_diff (u v : Mat k) :
    Real.sqrt (C.energy u) ≤ Real.sqrt (C.energy v) + Real.sqrt (ss (u - v)) := by
  have hu : u = v + (u - v) := by abel
  calc Real.sqrt (C.energy u)
      = Real.sqrt (C.energy (v + (u - v))) := by rw [← hu]
    _ ≤ Real.sqrt (C.energy v) + Real.sqrt (C.energy (u - v)) := C.sqrt_energy_add_le v (u - v)
    _ ≤ Real.sqrt (C.energy v) + Real.sqrt (ss (u - v)) := by
        gcongr; exact C.energy_le_ss _

/-- Leibniz energy inequality for products of contractions:
`√(energy (x * y)) ≤ √(energy x) + √(energy y)`. -/
lemma sqrt_energy_mul_le {x y : Mat k}
    (hx : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ≤ 1)
    (hy : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) y‖ ≤ 1) :
    Real.sqrt (C.energy (x * y)) ≤ Real.sqrt (C.energy x) + Real.sqrt (C.energy y) := by
  let ψ₁ : EuclideanSpace ℂ (Fin L × Fin k × Fin k) :=
    WithLp.toLp 2 (fun p : Fin L × Fin k × Fin k =>
      ((Real.sqrt (C.w p.1 / 2) : ℝ) : ℂ) *
        ((((C.V p.1 : Mat k) * x - x * (C.V p.1 : Mat k)) * y) p.2.1 p.2.2))
  let ψ₂ : EuclideanSpace ℂ (Fin L × Fin k × Fin k) :=
    WithLp.toLp 2 (fun p : Fin L × Fin k × Fin k =>
      ((Real.sqrt (C.w p.1 / 2) : ℝ) : ℂ) *
        ((x * ((C.V p.1 : Mat k) * y - y * (C.V p.1 : Mat k))) p.2.1 p.2.2))
  have hsum : C.energyVec (x * y) = ψ₁ + ψ₂ := by
    ext ⟨s, r, c⟩
    change ((Real.sqrt (C.w s / 2) : ℝ) : ℂ) *
      (((C.V s : Mat k) * (x * y) - (x * y) * (C.V s : Mat k)) r c) = _
    have hleib : (C.V s : Mat k) * (x * y) - (x * y) * (C.V s : Mat k) =
        ((C.V s : Mat k) * x - x * (C.V s : Mat k)) * y +
        x * ((C.V s : Mat k) * y - y * (C.V s : Mat k)) := by noncomm_ring
    rw [hleib, Matrix.add_apply, mul_add]
    rfl
  have hψ₁ : ‖ψ₁‖ ≤ Real.sqrt (C.energy x) := by
    have hsq : ‖ψ₁‖ ^ 2 ≤ C.energy x := by
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, C.energy_eq_comm_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      rw [Fintype.sum_prod_type]
      have hterm : ∀ r c : Fin k,
          ‖ψ₁.ofLp (s, r, c)‖ ^ 2 =
            (C.w s / 2) * ‖(((C.V s : Mat k) * x - x * (C.V s : Mat k)) * y) r c‖ ^ 2 :=
        fun r c => by
          change ‖((Real.sqrt (C.w s / 2) : ℝ) : ℂ) *
            ((((C.V s : Mat k) * x - x * (C.V s : Mat k)) * y) r c)‖ ^ 2 = _
          rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
            Real.sq_sqrt (div_nonneg (C.hw s) (by norm_num))]
      simp_rw [hterm, ← Finset.mul_sum]
      have hmul := ss_mul_right_le ((C.V s : Mat k) * x - x * (C.V s : Mat k)) y
      have hy2 : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) y‖ ^ 2 ≤ 1 := by
        nlinarith [norm_nonneg (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) y)]
      have hss_le : ss (((C.V s : Mat k) * x - x * (C.V s : Mat k)) * y) ≤
          ss ((C.V s : Mat k) * x - x * (C.V s : Mat k)) := by
        calc ss (((C.V s : Mat k) * x - x * (C.V s : Mat k)) * y)
            ≤ ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) y‖ ^ 2 *
                ss ((C.V s : Mat k) * x - x * (C.V s : Mat k)) := hmul
          _ ≤ 1 * ss ((C.V s : Mat k) * x - x * (C.V s : Mat k)) :=
              mul_le_mul_of_nonneg_right hy2 (ss_nonneg _)
          _ = ss ((C.V s : Mat k) * x - x * (C.V s : Mat k)) := one_mul _
      have hw2 : 0 ≤ C.w s / 2 := div_nonneg (C.hw s) (by norm_num)
      change C.w s / 2 * ss (((C.V s : Mat k) * x - x * (C.V s : Mat k)) * y) ≤
        1 / 2 * (C.w s * ss ((C.V s : Mat k) * x - x * (C.V s : Mat k)))
      nlinarith
    calc ‖ψ₁‖ = Real.sqrt (‖ψ₁‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (C.energy x) := Real.sqrt_le_sqrt hsq
  have hψ₂ : ‖ψ₂‖ ≤ Real.sqrt (C.energy y) := by
    have hsq : ‖ψ₂‖ ^ 2 ≤ C.energy y := by
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, C.energy_eq_comm_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      rw [Fintype.sum_prod_type]
      have hterm : ∀ r c : Fin k,
          ‖ψ₂.ofLp (s, r, c)‖ ^ 2 =
            (C.w s / 2) * ‖(x * ((C.V s : Mat k) * y - y * (C.V s : Mat k))) r c‖ ^ 2 :=
        fun r c => by
          change ‖((Real.sqrt (C.w s / 2) : ℝ) : ℂ) *
            ((x * ((C.V s : Mat k) * y - y * (C.V s : Mat k))) r c)‖ ^ 2 = _
          rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
            Real.sq_sqrt (div_nonneg (C.hw s) (by norm_num))]
      simp_rw [hterm, ← Finset.mul_sum]
      have hmul := ss_mul_left_le x ((C.V s : Mat k) * y - y * (C.V s : Mat k))
      have hx2 : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ^ 2 ≤ 1 := by
        nlinarith [norm_nonneg (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x)]
      have hss_le : ss (x * ((C.V s : Mat k) * y - y * (C.V s : Mat k))) ≤
          ss ((C.V s : Mat k) * y - y * (C.V s : Mat k)) := by
        calc ss (x * ((C.V s : Mat k) * y - y * (C.V s : Mat k)))
            ≤ ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ^ 2 *
                ss ((C.V s : Mat k) * y - y * (C.V s : Mat k)) := hmul
          _ ≤ 1 * ss ((C.V s : Mat k) * y - y * (C.V s : Mat k)) :=
              mul_le_mul_of_nonneg_right hx2 (ss_nonneg _)
          _ = ss ((C.V s : Mat k) * y - y * (C.V s : Mat k)) := one_mul _
      have hw2 : 0 ≤ C.w s / 2 := div_nonneg (C.hw s) (by norm_num)
      change C.w s / 2 * ss (x * ((C.V s : Mat k) * y - y * (C.V s : Mat k))) ≤
        1 / 2 * (C.w s * ss ((C.V s : Mat k) * y - y * (C.V s : Mat k)))
      nlinarith
    calc ‖ψ₂‖ = Real.sqrt (‖ψ₂‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (C.energy y) := Real.sqrt_le_sqrt hsq
  rw [← C.energyVec_norm, hsum]
  exact (norm_add_le ψ₁ ψ₂).trans (add_le_add hψ₁ hψ₂)

/- ### Section 3: Bad vertex removal, high-eigenvector rounding, uniqueness, and equivalence -/

/-- Pythagorean theorem for pairwise orthogonal finite sums in an inner product space. -/
lemma norm_sq_sum_of_pairwise_orth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {α : Type*} (S : Finset α) (f : α → E)
    (horth : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → @inner ℂ _ _ (f a) (f b) = 0) :
    ‖∑ a ∈ S, f a‖ ^ 2 = ∑ a ∈ S, ‖f a‖ ^ 2 := by
  classical
  have hre : (@inner ℂ _ _ (∑ a ∈ S, f a) (∑ a ∈ S, f a)).re = ∑ a ∈ S, ‖f a‖ ^ 2 := by
    rw [sum_inner, Complex.re_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [inner_sum]
    have hterm : ∀ b ∈ S, @inner ℂ _ _ (f a) (f b) =
        if b = a then @inner ℂ _ _ (f a) (f a) else 0 := fun b hb => by
      by_cases hba : b = a
      · subst hba; rw [if_pos rfl]
      · rw [if_neg hba]; exact horth a ha b hb (Ne.symm hba)
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' S a, if_pos ha]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (f a)
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm.trans hre

lemma diag_no_bad_eigenvalue {i : Fin m} {v : Mat k} {μ : ℝ}
    (hv : C.e i * v * C.e i = v) (hv_ne : v ≠ 0) (hev : C.F v = (μ : ℂ) • v) :
    μ = 1 ∨ μ ≤ C.ρ := by
  by_cases h1 : μ = 1
  · exact Or.inl h1
  · right
    have htr_eq : v.trace = (μ : ℂ) * v.trace := by
      have hev_l : C.e i * v = v := by
        calc C.e i * v = C.e i * (C.e i * v * C.e i) := by rw [hv]
          _ = (C.e i * C.e i) * v * C.e i := by noncomm_ring
          _ = v := by rw [C.he_sq i, hv]
      calc v.trace = (C.e i * v).trace := by rw [hev_l]
        _ = (star (C.e i) * v).trace := by rw [C.he_sa i]
        _ = (star (C.F (C.e i)) * v).trace := by rw [C.F_fix_e i]
        _ = (star (C.e i) * C.F v).trace := C.F_sa (C.e i) v
        _ = (C.e i * ((μ : ℂ) • v)).trace := by rw [C.he_sa i, hev]
        _ = (μ : ℂ) * (C.e i * v).trace := by
            rw [mul_smul_comm, Matrix.trace_smul, smul_eq_mul]
        _ = (μ : ℂ) * v.trace := by rw [hev_l]
    have htr0 : v.trace = 0 := by
      have hne : ((1 : ℂ) - (μ : ℂ)) ≠ 0 := by
        intro h
        apply h1
        have hre := congrArg Complex.re h
        simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.zero_re] at hre
        linarith
      have hmul : ((1 : ℂ) - (μ : ℂ)) * v.trace = 0 := by
        rw [sub_mul, one_mul, sub_eq_zero]
        exact htr_eq
      exact (mul_eq_zero.1 hmul).resolve_left hne
    have hσ : ss (C.F v - (v.trace / (C.e i).trace) • C.e i) ≤ C.σ₀ * ss v :=
      C.hσ_bound i v hv
    rw [htr0, zero_div, zero_smul, sub_zero, hev, ss_smul', Complex.norm_real,
      Real.norm_eq_abs, sq_abs] at hσ
    have hss_pos : 0 < ss v := ss_pos_of_ne_zero hv_ne
    have hμ_sq : μ ^ 2 ≤ C.σ₀ := by nlinarith
    have hμ_nn : 0 ≤ μ := (C.blockEnd_eigenvalue_bounds hv_ne hev).1
    have hρ8 : C.ρ ^ 8 ≤ C.ρ ^ 2 := by
      have hle1 : C.ρ ≤ 1 := by linarith [C.hρ_small]
      have hρ6 : C.ρ ^ 6 ≤ 1 := pow_le_one₀ (le_of_lt C.hρ_pos) hle1
      have h8 : C.ρ ^ 8 = C.ρ ^ 2 * C.ρ ^ 6 := by ring
      nlinarith [sq_nonneg C.ρ]
    nlinarith [C.hρ_pos, C.hσ₀_le]

def IsBadPair (i j : Fin m) : Prop :=
  ∃ v : Mat k, C.e i * v * C.e j = v ∧ v ≠ 0 ∧
    ∃ μ : ℝ, C.ρ < μ ∧ μ < 1 - C.ρ ∧ C.F v = (μ : ℂ) • v

lemma isBadPair_symm {i j : Fin m} (h : C.IsBadPair i j) : C.IsBadPair j i := by
  rcases h with ⟨v, hv, hv_ne, μ, hlo, hhi, hev⟩
  refine ⟨star v, ?_, ?_, μ, hlo, hhi, ?_⟩
  · conv_rhs => rw [← hv]
    rw [star_mul, star_mul, C.he_sa i, C.he_sa j, mul_assoc]
  · intro h0
    apply hv_ne
    rw [← star_star v, h0, star_zero]
  · rw [C.F_star, hev, star_smul, Complex.star_def, Complex.conj_ofReal]

lemma not_isBadPair_self (i : Fin m) : ¬ C.IsBadPair i i := by
  rintro ⟨v, hv, hv_ne, μ, hlo, hhi, hev⟩
  rcases C.diag_no_bad_eigenvalue hv hv_ne hev with rfl | hle
  · linarith [C.hρ_pos]
  · linarith

/-- Maximal matching elimination of bad vertices: returns `Ret ⊆ univ` with no bad pairs inside
`Ret` and total removed rank at most `256 * ρ^4 * k`. -/
lemma exists_good_partition :
    ∃ Ret : Finset (Fin m),
      (∀ i ∈ Ret, ∀ j ∈ Ret, ¬ C.IsBadPair i j) ∧
      ∑ i ∈ Finset.univ \ Ret, C.rkr i ≤ 256 * C.ρ ^ 4 * (k : ℝ) := by
  classical
  let IsValid : Finset (Fin m × Fin m) → Prop := fun S =>
    (∀ p ∈ S, C.IsBadPair p.1 p.2) ∧
    (∀ p ∈ S, ∀ q ∈ S, p ≠ q → p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2)
  let AllValid : Finset (Finset (Fin m × Fin m)) := Finset.univ.filter IsValid
  have hempty : (∅ : Finset (Fin m × Fin m)) ∈ AllValid := by
    simp [AllValid, IsValid]
  obtain ⟨S, hS_mem, hS_max⟩ := Finset.exists_max_image AllValid Finset.card ⟨∅, hempty⟩
  have hS_valid : IsValid S := (Finset.mem_filter.1 hS_mem).2
  let BadV : Finset (Fin m) := S.image Prod.fst ∪ S.image Prod.snd
  let Ret : Finset (Fin m) := Finset.univ \ BadV
  have hRet_nobad : ∀ i ∈ Ret, ∀ j ∈ Ret, ¬ C.IsBadPair i j := by
    intro i hi j hj hbad
    have hi_not : i ∉ BadV := (Finset.mem_sdiff.1 hi).2
    have hj_not : j ∉ BadV := (Finset.mem_sdiff.1 hj).2
    have hij : i ≠ j := by
      rintro rfl
      exact C.not_isBadPair_self i hbad
    have hnotS : (i, j) ∉ S := fun hmem =>
      hi_not (Finset.mem_union_left _ (Finset.mem_image.2 ⟨(i, j), hmem, rfl⟩))
    have hdisj : ∀ q ∈ S, i ≠ q.1 ∧ i ≠ q.2 ∧ j ≠ q.1 ∧ j ≠ q.2 := fun q hq => by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rintro rfl; exact hi_not (Finset.mem_union_left _ (Finset.mem_image.2 ⟨q, hq, rfl⟩))
      · rintro rfl; exact hi_not (Finset.mem_union_right _ (Finset.mem_image.2 ⟨q, hq, rfl⟩))
      · rintro rfl; exact hj_not (Finset.mem_union_left _ (Finset.mem_image.2 ⟨q, hq, rfl⟩))
      · rintro rfl; exact hj_not (Finset.mem_union_right _ (Finset.mem_image.2 ⟨q, hq, rfl⟩))
    have hS'_valid : IsValid (insert (i, j) S) := by
      refine ⟨?_, ?_⟩
      · intro p hp
        rcases Finset.mem_insert.1 hp with rfl | hpS
        · exact hbad
        · exact hS_valid.1 p hpS
      · intro p hp q hq hpq
        rcases Finset.mem_insert.1 hp with rfl | hpS <;>
          rcases Finset.mem_insert.1 hq with rfl | hqS
        · exact absurd rfl hpq
        · exact hdisj q hqS
        · have h := hdisj p hpS
          exact ⟨h.1.symm, h.2.2.1.symm, h.2.1.symm, h.2.2.2.symm⟩
        · exact hS_valid.2 p hpS q hqS hpq
    have hS'_mem : insert (i, j) S ∈ AllValid := Finset.mem_filter.2 ⟨Finset.mem_univ _, hS'_valid⟩
    have hle := hS_max (insert (i, j) S) hS'_mem
    rw [Finset.card_insert_of_notMem hnotS] at hle
    omega
  -- For each `p ∈ S`, pick contraction `x p ∈ B(p.1, p.2)` with large `(F^2 - F)` defect
  have hex : ∀ p : Fin m × Fin m, p ∈ S →
      ∃ x : Mat k,
        C.e p.1 * x * C.e p.2 = x ∧
        ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ≤ 1 ∧
        C.ρ ^ 4 * max (C.rkr p.1) (C.rkr p.2) / 128 ≤ ss (C.F (C.F x) - C.F x) := by
    intro p hp
    rcases hS_valid.1 p hp with ⟨v, hv, hv_ne, μ, hlo, hhi, hev⟩
    exact C.mid_eigenvalue_defect hv hv_ne hev hlo hhi
  let x : Fin m × Fin m → Mat k := fun p =>
    if hp : p ∈ S then Classical.choose (hex p hp) else 0
  have hx_block : ∀ p ∈ S, C.e p.1 * x p * C.e p.2 = x p := fun p hp => by
    simp only [x, dif_pos hp]
    exact (Classical.choose_spec (hex p hp)).1
  have hx_op : ∀ p ∈ S, ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (x p)‖ ≤ 1 := fun p hp => by
    simp only [x, dif_pos hp]
    exact (Classical.choose_spec (hex p hp)).2.1
  have hx_def : ∀ p ∈ S, C.ρ ^ 4 * max (C.rkr p.1) (C.rkr p.2) / 128 ≤
      ss (C.F (C.F (x p)) - C.F (x p)) := fun p hp => by
    simp only [x, dif_pos hp]
    exact (Classical.choose_spec (hex p hp)).2.2
  let X : Mat k := ∑ p ∈ S, x p
  have hX_op : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) X‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => ?_
    rw [one_mul]
    have hXξ : Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) X ξ =
        ∑ p ∈ S, Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (x p) ξ := by
      simp only [X, map_sum, _root_.sum_apply]
    have horth_out : ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
        @inner ℂ _ _ (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (x p) ξ)
          (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (x q) ξ) = 0 := by
      intro p hp q hq hpq
      have hp1 : C.e p.1 * x p = x p := by
        calc C.e p.1 * x p = C.e p.1 * (C.e p.1 * x p * C.e p.2) := by rw [hx_block p hp]
          _ = (C.e p.1 * C.e p.1) * x p * C.e p.2 := by noncomm_ring
          _ = x p := by rw [C.he_sq p.1, hx_block p hp]
      have hq1 : C.e q.1 * x q = x q := by
        calc C.e q.1 * x q = C.e q.1 * (C.e q.1 * x q * C.e q.2) := by rw [hx_block q hq]
          _ = (C.e q.1 * C.e q.1) * x q * C.e q.2 := by noncomm_ring
          _ = x q := by rw [C.he_sq q.1, hx_block q hq]
      rw [← hp1, ← hq1, toEuclideanCLM_mul_apply, toEuclideanCLM_mul_apply,
        inner_toEuclideanCLM, C.he_sa q.1, ← toEuclideanCLM_mul_apply,
        C.he_orth q.1 p.1 (Ne.symm (hS_valid.2 p hp q hq hpq).1), map_zero,
        _root_.zero_apply, inner_zero_left]
    have hterm_le : ∀ p ∈ S, ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (x p) ξ‖ ^ 2 ≤
        ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (C.e p.2) ξ‖ ^ 2 := by
      intro p hp
      have hp2 : x p * C.e p.2 = x p := by
        calc x p * C.e p.2 = (C.e p.1 * x p * C.e p.2) * C.e p.2 := by rw [hx_block p hp]
          _ = C.e p.1 * x p * (C.e p.2 * C.e p.2) := by noncomm_ring
          _ = x p := by rw [C.he_sq p.2, hx_block p hp]
      have hle : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (x p) ξ‖ ≤
          ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (C.e p.2) ξ‖ := by
        rw [← hp2, toEuclideanCLM_mul_apply]
        calc ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (x p)
                (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (C.e p.2) ξ)‖
            ≤ ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (x p)‖ *
                ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (C.e p.2) ξ‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (C.e p.2) ξ‖ :=
              mul_le_mul_of_nonneg_right (hx_op p hp) (norm_nonneg _)
          _ = _ := one_mul _
      exact pow_le_pow_left₀ (norm_nonneg _) hle 2
    have hsum_e : ∑ j : Fin m, ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (C.e j) ξ‖ ^ 2 =
        ‖ξ‖ ^ 2 := by
      have h1 : ξ = ∑ j : Fin m, Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (C.e j) ξ := by
        have := congrArg (fun M : Mat k => Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) M ξ) C.he_sum
        simpa [_root_.sum_apply] using this.symm
      conv_rhs => rw [h1]
      symm
      refine norm_sq_sum_of_pairwise_orth Finset.univ _ fun a _ b _ hab => ?_
      rw [inner_toEuclideanCLM, C.he_sa b, ← toEuclideanCLM_mul_apply,
        C.he_orth b a (Ne.symm hab), map_zero, _root_.zero_apply, inner_zero_left]
    have hsq : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) X ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
      rw [hXξ, norm_sq_sum_of_pairwise_orth S _ horth_out]
      calc ∑ p ∈ S, ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (x p) ξ‖ ^ 2
          ≤ ∑ p ∈ S, ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (C.e p.2) ξ‖ ^ 2 :=
            Finset.sum_le_sum hterm_le
        _ = ∑ j ∈ S.image Prod.snd, ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (C.e j) ξ‖ ^ 2 := by
            symm
            refine Finset.sum_image fun p hp q hq hpq => ?_
            by_contra hne
            exact (hS_valid.2 p hp q hq hne).2.2.2 hpq
        _ ≤ ∑ j : Fin m, ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (C.e j) ξ‖ ^ 2 :=
            Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
        _ = ‖ξ‖ ^ 2 := hsum_e
    nlinarith [norm_nonneg (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) X ξ), norm_nonneg ξ]
  have hFX : C.F (C.F X) - C.F X = ∑ p ∈ S, (C.F (C.F (x p)) - C.F (x p)) := by
    simp only [X, C.F_sum, Finset.sum_sub_distrib]
  have hFX_ss : ss (C.F (C.F X) - C.F X) = ∑ p ∈ S, ss (C.F (C.F (x p)) - C.F (x p)) := by
    rw [hFX]
    refine C.ss_sum_blocks _ fun p hp => ?_
    rw [mul_sub, sub_mul, ← C.F_block, ← C.F_block, hx_block p hp]
  have hsum_max : C.ρ ^ 4 / 128 * ∑ p ∈ S, max (C.rkr p.1) (C.rkr p.2) ≤ C.δ₀ * (k : ℝ) := by
    calc C.ρ ^ 4 / 128 * ∑ p ∈ S, max (C.rkr p.1) (C.rkr p.2)
        = ∑ p ∈ S, C.ρ ^ 4 * max (C.rkr p.1) (C.rkr p.2) / 128 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => by ring
      _ ≤ ∑ p ∈ S, ss (C.F (C.F (x p)) - C.F (x p)) := Finset.sum_le_sum hx_def
      _ = ss (C.F (C.F X) - C.F X) := hFX_ss.symm
      _ ≤ C.δ₀ * (k : ℝ) := C.hδ_bound X hX_op
  have hBadV_eq : Finset.univ \ Ret = BadV := by
    ext i
    simp [Ret]
  have hBadV_sum : ∑ i ∈ BadV, C.rkr i ≤ 2 * ∑ p ∈ S, max (C.rkr p.1) (C.rkr p.2) := by
    have h1 : ∑ i ∈ BadV, C.rkr i ≤
        (∑ i ∈ S.image Prod.fst, C.rkr i) + ∑ i ∈ S.image Prod.snd, C.rkr i := by
      have hu := Finset.sum_union_inter (s₁ := S.image Prod.fst) (s₂ := S.image Prod.snd) (f := C.rkr)
      have hnn : 0 ≤ ∑ i ∈ S.image Prod.fst ∩ S.image Prod.snd, C.rkr i :=
        Finset.sum_nonneg fun i _ => le_of_lt (C.rkr_pos i)
      linarith
    have h2 : ∑ i ∈ S.image Prod.fst, C.rkr i = ∑ p ∈ S, C.rkr p.1 := by
      refine Finset.sum_image fun p hp q hq hpq => ?_
      by_contra hne
      exact (hS_valid.2 p hp q hq hne).1 hpq
    have h3 : ∑ i ∈ S.image Prod.snd, C.rkr i = ∑ p ∈ S, C.rkr p.2 := by
      refine Finset.sum_image fun p hp q hq hpq => ?_
      by_contra hne
      exact (hS_valid.2 p hp q hq hne).2.2.2 hpq
    have h4 : (∑ p ∈ S, C.rkr p.1) + ∑ p ∈ S, C.rkr p.2 ≤
        2 * ∑ p ∈ S, max (C.rkr p.1) (C.rkr p.2) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_le_sum fun p _ => ?_
      linarith [le_max_left (C.rkr p.1) (C.rkr p.2), le_max_right (C.rkr p.1) (C.rkr p.2)]
    linarith
  have hfinal : ∑ i ∈ Finset.univ \ Ret, C.rkr i ≤ 256 * C.ρ ^ 4 * (k : ℝ) := by
    rw [hBadV_eq]
    have hρ4_pos : 0 < C.ρ ^ 4 := pow_pos C.hρ_pos 4
    have h8 : C.δ₀ * (k : ℝ) ≤ C.ρ ^ 8 * (k : ℝ) :=
      mul_le_mul_of_nonneg_right C.hδ₀_le (Nat.cast_nonneg k)
    have hmul : C.ρ ^ 4 * (∑ i ∈ BadV, C.rkr i) ≤ C.ρ ^ 4 * (256 * C.ρ ^ 4 * (k : ℝ)) := by
      have h8' : C.ρ ^ 4 * (256 * C.ρ ^ 4 * (k : ℝ)) = 256 * (C.ρ ^ 8 * (k : ℝ)) := by ring
      rw [h8']
      nlinarith [hsum_max, hBadV_sum, h8]
    nlinarith
  exact ⟨Ret, hRet_nobad, hfinal⟩

/-- Polar rounding of a high eigenvector (`1 - ρ ≤ μ`) normalized to `ss v = max (rkr i) (rkr j)`. -/
lemma high_eigenvector_polar {i j : Fin m} {v : Mat k} {μ : ℝ}
    (hv : C.e i * v * C.e j = v)
    (hss : ss v = max (C.rkr i) (C.rkr j))
    (hev : C.F v = (μ : ℂ) • v) (hμ : 1 - C.ρ ≤ μ) :
    (1 - 3 * C.ρ) * max (C.rkr i) (C.rkr j) ≤ min (C.rkr i) (C.rkr j) ∧
    ∃ u : Mat k,
      let t := min (C.rk i) (C.rk j)
      C.e i * u * C.e j = u ∧
      ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) u‖ ≤ 1 ∧
      star (star u * u) = star u * u ∧
      (star u * u) * (star u * u) = star u * u ∧
      C.e j * (star u * u) * C.e j = star u * u ∧
      (star u * u).trace = (t : ℂ) ∧
      star (u * star u) = u * star u ∧
      (u * star u) * (u * star u) = u * star u ∧
      C.e i * (u * star u) * C.e i = u * star u ∧
      (u * star u).trace = (t : ℂ) ∧
      ss (v - u) ≤ 4 * C.ρ * max (C.rkr i) (C.rkr j) ∧
      Real.sqrt (C.energy u) ≤ 3 * Real.sqrt C.ρ * Real.sqrt (max (C.rkr i) (C.rkr j)) := by
  let M : ℝ := max (C.rkr i) (C.rkr j)
  let tr : ℝ := min (C.rkr i) (C.rkr j)
  have hM_pos : 0 < M := lt_of_lt_of_le (C.rkr_pos i) (le_max_left _ _)
  have hv_ne : v ≠ 0 := by
    intro h0
    rw [h0, ss_zero] at hss
    linarith
  have hσ₁ : Real.sqrt C.σ₀ ≤ C.ρ ^ 4 := by
    have h1 : Real.sqrt C.σ₀ ≤ Real.sqrt (C.ρ ^ 8) := Real.sqrt_le_sqrt C.hσ₀_le
    have h2 : Real.sqrt (C.ρ ^ 8) = C.ρ ^ 4 := by
      rw [show C.ρ ^ 8 = (C.ρ ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    linarith
  have hlow : 1 - 3 * C.ρ ≤ μ ^ 2 - Real.sqrt C.σ₀ := by
    have hρ_le : C.ρ ≤ 1 / 10000 := C.hρ_small
    have hρ4 : C.ρ ^ 4 ≤ C.ρ := by
      have h1 : C.ρ ^ 3 ≤ 1 := pow_le_one₀ (le_of_lt C.hρ_pos) (by linarith)
      have h4 : C.ρ ^ 4 = C.ρ * C.ρ ^ 3 := by ring
      nlinarith [C.hρ_pos]
    have hμ2 : (1 - C.ρ) ^ 2 ≤ μ ^ 2 := by nlinarith [C.hρ_pos]
    nlinarith [sq_nonneg C.ρ]
  have hratio : (1 - 3 * C.ρ) * M ≤ tr := by
    have hr := C.eigval_sq_sub_sigma_le_ratio hv hv_ne hev
    have hle : 1 - 3 * C.ρ ≤ tr / M := hlow.trans hr
    exact (le_div_iff₀ hM_pos).1 hle
  have h4_le : ss (star v * v) ≤ (1 + 4 * C.ρ) * M := by
    have h4 := C.fourth_moment_bound hv hev
    rw [hss] at h4
    have hM2 : M ^ 2 / M = M := by field_simp [ne_of_gt hM_pos]
    rw [hM2] at h4
    have hpos1 : 0 < 1 - 3 * C.ρ := by linarith [C.hρ_small]
    have h13 : (1 - 3 * C.ρ) * ss (star v * v) ≤ M :=
      (mul_le_mul_of_nonneg_right hlow (ss_nonneg _)).trans h4
    have hprod : 1 ≤ (1 - 3 * C.ρ) * (1 + 4 * C.ρ) := by
      nlinarith [C.hρ_pos, C.hρ_small]
    nlinarith [hM_pos]
  obtain ⟨u, hu_block, hu_op, hsu_sa, hsu_sq, hsu_c, hsu_tr, hus_sa, hus_sq, hus_c, hus_tr, hdist⟩ :=
    exists_block_polar (C.he_sa i) (C.he_sq i) (C.he_sa j) (C.he_sq j) hv
  have ht_le_M : ((min (C.rk i) (C.rk j) : ℕ) : ℝ) ≤ M := by
    rw [Nat.cast_min]
    exact (min_le_left _ _).trans (le_max_left _ _)
  have hdiff : ss (v - u) ≤ 4 * C.ρ * M := by
    have h1 : ss (v - u) ≤ ss (star v * v) - 2 * M + ((min (C.rk i) (C.rk j) : ℕ) : ℝ) := by
      simpa [hss, rk] using hdist
    linarith
  have hEv : C.energy v ≤ C.ρ * M := by
    unfold energy
    rw [hev, mul_smul_comm, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
      ← ss_eq_re_trace, hss]
    nlinarith [hM_pos]
  have hEu : Real.sqrt (C.energy u) ≤ 3 * Real.sqrt C.ρ * Real.sqrt M := by
    have h1 := C.sqrt_energy_le_add_diff u v
    have hss_uv : ss (u - v) = ss (v - u) := by
      rw [← ss_neg_eq (v - u), neg_sub]
    rw [hss_uv] at h1
    have h2 : Real.sqrt (C.energy v) ≤ Real.sqrt C.ρ * Real.sqrt M := by
      calc Real.sqrt (C.energy v) ≤ Real.sqrt (C.ρ * M) := Real.sqrt_le_sqrt hEv
        _ = Real.sqrt C.ρ * Real.sqrt M := Real.sqrt_mul (le_of_lt C.hρ_pos) M
    have h3 : Real.sqrt (ss (v - u)) ≤ 2 * Real.sqrt C.ρ * Real.sqrt M := by
      calc Real.sqrt (ss (v - u)) ≤ Real.sqrt (4 * C.ρ * M) := Real.sqrt_le_sqrt hdiff
        _ = Real.sqrt 4 * Real.sqrt C.ρ * Real.sqrt M := by
            rw [Real.sqrt_mul (mul_nonneg (by norm_num) (le_of_lt C.hρ_pos)),
              Real.sqrt_mul (by norm_num)]
        _ = 2 * Real.sqrt C.ρ * Real.sqrt M := by
            rw [show Real.sqrt 4 = 2 by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    linarith
  exact ⟨hratio, u, hu_block, hu_op, hsu_sa, hsu_sq, hsu_c, hsu_tr, hus_sa, hus_sq, hus_c,
    hus_tr, hdiff, hEu⟩

/-- Helper: diagonal-corner contradiction for two orthogonal-trace polar completions in `B(i, j)`. -/
lemma high_polar_pair_contradiction {i j : Fin m} {w₁ w₂ u₁ u₂ : Mat k}
    (hw₁_ss : ss w₁ = max (C.rkr i) (C.rkr j))
    (hw_orth : (star w₁ * w₂).trace = 0)
    (hratio : (1 - 3 * C.ρ) * max (C.rkr i) (C.rkr j) ≤ min (C.rkr i) (C.rkr j))
    (hu₁_block : C.e i * u₁ * C.e j = u₁) (hu₁_op : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) u₁‖ ≤ 1)
    (hus₁_sa : star (u₁ * star u₁) = u₁ * star u₁)
    (hus₁_sq : (u₁ * star u₁) * (u₁ * star u₁) = u₁ * star u₁)
    (hus₁_c : C.e i * (u₁ * star u₁) * C.e i = u₁ * star u₁)
    (hus₁_tr : (u₁ * star u₁).trace = ((min (C.rk i) (C.rk j) : ℕ) : ℂ))
    (hdiff₁ : ss (w₁ - u₁) ≤ 4 * C.ρ * max (C.rkr i) (C.rkr j))
    (hEu₁ : Real.sqrt (C.energy u₁) ≤ 3 * Real.sqrt C.ρ * Real.sqrt (max (C.rkr i) (C.rkr j)))
    (hu₂_block : C.e i * u₂ * C.e j = u₂) (hu₂_op : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) u₂‖ ≤ 1)
    (hsu₂_tr : (star u₂ * u₂).trace = ((min (C.rk i) (C.rk j) : ℕ) : ℂ))
    (hus₂_sa : star (u₂ * star u₂) = u₂ * star u₂)
    (hus₂_sq : (u₂ * star u₂) * (u₂ * star u₂) = u₂ * star u₂)
    (hus₂_c : C.e i * (u₂ * star u₂) * C.e i = u₂ * star u₂)
    (hus₂_tr : (u₂ * star u₂).trace = ((min (C.rk i) (C.rk j) : ℕ) : ℂ))
    (hdiff₂ : ss (w₂ - u₂) ≤ 4 * C.ρ * max (C.rkr i) (C.rkr j))
    (hEu₂ : Real.sqrt (C.energy u₂) ≤ 3 * Real.sqrt C.ρ * Real.sqrt (max (C.rkr i) (C.rkr j))) :
    False := by
  let M : ℝ := max (C.rkr i) (C.rkr j)
  have hM_pos : 0 < M := lt_of_lt_of_le (C.rkr_pos i) (le_max_left _ _)
  let z : Mat k := star u₁ * u₂
  have hz_block : C.e j * z * C.e j = z := by
    have h1 : C.e j * star u₁ = star u₁ := by
      have hu₁r : u₁ * C.e j = u₁ := by
        calc u₁ * C.e j = (C.e i * u₁ * C.e j) * C.e j := by rw [hu₁_block]
          _ = C.e i * u₁ * (C.e j * C.e j) := by noncomm_ring
          _ = u₁ := by rw [C.he_sq j, hu₁_block]
      calc C.e j * star u₁ = star (u₁ * C.e j) := by rw [star_mul, C.he_sa j]
        _ = star u₁ := by rw [hu₁r]
    have hu₂r : u₂ * C.e j = u₂ := by
      calc u₂ * C.e j = (C.e i * u₂ * C.e j) * C.e j := by rw [hu₂_block]
        _ = C.e i * u₂ * (C.e j * C.e j) := by noncomm_ring
        _ = u₂ := by rw [C.he_sq j, hu₂_block]
    calc C.e j * z * C.e j = (C.e j * star u₁) * (u₂ * C.e j) := by simp only [z, mul_assoc]
      _ = z := by rw [h1, hu₂r]
  have hz_ss_eq : ss z = (((u₁ * star u₁) * (u₂ * star u₂)).trace).re := by
    rw [ss_eq_re_trace]
    congr 1
    simp only [z, star_mul, star_star]
    have h1 : star u₂ * u₁ * (star u₁ * u₂) = star u₂ * ((u₁ * star u₁) * u₂) := by
      simp only [mul_assoc]
    rw [h1, Matrix.trace_mul_comm]
    congr 1; simp only [mul_assoc]
  have hz_ss_lo : (1 - 6 * C.ρ) * M ≤ ss z := by
    rw [hz_ss_eq]
    have hinter := proj_mul_trace_ge hus₁_sa hus₁_sq hus₂_sa hus₂_sq (C.he_sa i) (C.he_sq i)
      hus₁_c hus₂_c
    rw [hus₁_tr, hus₂_tr, Complex.natCast_re, C.e_re_trace i] at hinter
    have htr_eq : ((min (C.rk i) (C.rk j) : ℕ) : ℝ) = min (C.rkr i) (C.rkr j) := by
      rw [Nat.cast_min]; rfl
    rw [htr_eq] at hinter
    have hri_le : C.rkr i ≤ M := le_max_left _ _
    linarith only [hinter, hratio, hri_le]
  have hu₁_star_op : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (star u₁)‖ ≤ 1 := by
    rw [map_star]
    have h := ContinuousLinearMap.adjoint.norm_map (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) u₁)
    change ‖ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) u₁)‖ ≤ 1
    rw [h]; exact hu₁_op
  have hu₂_ss : ss u₂ ≤ M := by
    rw [ss_eq_re_trace, hsu₂_tr, Complex.natCast_re, Nat.cast_min]
    exact (min_le_left _ _).trans (le_max_left _ _)
  have hz_ss_hi : ss z ≤ M := by
    have hmul := ss_mul_left_le (star u₁) u₂
    have h1 : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (star u₁)‖ ^ 2 ≤ 1 := by
      nlinarith only [hu₁_star_op, norm_nonneg (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (star u₁))]
    calc ss z ≤ ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (star u₁)‖ ^ 2 * ss u₂ := hmul
      _ ≤ 1 * M := mul_le_mul h1 hu₂_ss (ss_nonneg u₂) zero_le_one
      _ = M := one_mul M
  have htr_z : ‖z.trace‖ ≤ 4 * Real.sqrt C.ρ * M := by
    have hsplit : z.trace = (star (u₁ - w₁) * u₂).trace + (star w₁ * (u₂ - w₂)).trace := by
      have h1 : star u₁ * u₂ = star (u₁ - w₁) * u₂ + star w₁ * (u₂ - w₂) + star w₁ * w₂ := by
        rw [star_sub]; noncomm_ring
      rw [show z = star u₁ * u₂ from rfl, h1, Matrix.trace_add, Matrix.trace_add, hw_orth,
        add_zero]
    have hsq4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hd1 : Real.sqrt (ss (u₁ - w₁)) ≤ 2 * Real.sqrt C.ρ * Real.sqrt M := by
      rw [← ss_neg_eq (w₁ - u₁), neg_sub] at hdiff₁
      calc Real.sqrt (ss (u₁ - w₁)) ≤ Real.sqrt (4 * C.ρ * M) := Real.sqrt_le_sqrt hdiff₁
        _ = Real.sqrt 4 * Real.sqrt C.ρ * Real.sqrt M := by
            rw [Real.sqrt_mul (mul_nonneg (by norm_num) (le_of_lt C.hρ_pos)),
              Real.sqrt_mul (by norm_num)]
        _ = 2 * Real.sqrt C.ρ * Real.sqrt M := by rw [hsq4]
    have hd2 : Real.sqrt (ss (u₂ - w₂)) ≤ 2 * Real.sqrt C.ρ * Real.sqrt M := by
      rw [← ss_neg_eq (w₂ - u₂), neg_sub] at hdiff₂
      calc Real.sqrt (ss (u₂ - w₂)) ≤ Real.sqrt (4 * C.ρ * M) := Real.sqrt_le_sqrt hdiff₂
        _ = Real.sqrt 4 * Real.sqrt C.ρ * Real.sqrt M := by
            rw [Real.sqrt_mul (mul_nonneg (by norm_num) (le_of_lt C.hρ_pos)),
              Real.sqrt_mul (by norm_num)]
        _ = 2 * Real.sqrt C.ρ * Real.sqrt M := by rw [hsq4]
    rw [hsplit]
    calc ‖(star (u₁ - w₁) * u₂).trace + (star w₁ * (u₂ - w₂)).trace‖
        ≤ ‖(star (u₁ - w₁) * u₂).trace‖ + ‖(star w₁ * (u₂ - w₂)).trace‖ := norm_add_le _ _
      _ ≤ Real.sqrt (ss (u₁ - w₁)) * Real.sqrt (ss u₂) +
            Real.sqrt (ss w₁) * Real.sqrt (ss (u₂ - w₂)) :=
          add_le_add (norm_trace_star_mul_le _ _) (norm_trace_star_mul_le _ _)
      _ ≤ (2 * Real.sqrt C.ρ * Real.sqrt M) * Real.sqrt M +
            Real.sqrt M * (2 * Real.sqrt C.ρ * Real.sqrt M) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul hd1 (Real.sqrt_le_sqrt hu₂_ss) (Real.sqrt_nonneg _)
              (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
          · rw [hw₁_ss]
            exact mul_le_mul_of_nonneg_left hd2 (Real.sqrt_nonneg _)
      _ = 4 * Real.sqrt C.ρ * (Real.sqrt M * Real.sqrt M) := by ring
      _ = 4 * Real.sqrt C.ρ * M := by rw [Real.mul_self_sqrt (le_of_lt hM_pos)]
  let scal : Mat k := (z.trace / (C.e j).trace) • C.e j
  have h1_ss : Real.sqrt (ss (z - C.F z)) ≤ 9 * Real.sqrt C.ρ * Real.sqrt M := by
    have hEz : Real.sqrt (C.energy z) ≤ 6 * Real.sqrt C.ρ * Real.sqrt M := by
      calc Real.sqrt (C.energy z)
          ≤ Real.sqrt (C.energy (star u₁)) + Real.sqrt (C.energy u₂) :=
            C.sqrt_energy_mul_le hu₁_star_op hu₂_op
        _ = Real.sqrt (C.energy u₁) + Real.sqrt (C.energy u₂) := by rw [C.energy_star]
        _ ≤ 3 * Real.sqrt C.ρ * Real.sqrt M + 3 * Real.sqrt C.ρ * Real.sqrt M :=
            add_le_add hEu₁ hEu₂
        _ = 6 * Real.sqrt C.ρ * Real.sqrt M := by ring
    have hFz : ss (z - C.F z) ≤ 2 * C.energy z := by
      rw [← ss_neg_eq (z - C.F z), neg_sub]
      exact C.ss_F_sub_le_two_energy z
    calc Real.sqrt (ss (z - C.F z))
        ≤ Real.sqrt (2 * C.energy z) := Real.sqrt_le_sqrt hFz
      _ = Real.sqrt 2 * Real.sqrt (C.energy z) := Real.sqrt_mul (by norm_num) _
      _ ≤ 1.5 * (6 * Real.sqrt C.ρ * Real.sqrt M) := by
          have hsq2 : Real.sqrt 2 ≤ 1.5 := by
            rw [Real.sqrt_le_iff]; constructor <;> norm_num
          exact mul_le_mul hsq2 hEz (Real.sqrt_nonneg _) (by norm_num)
      _ = 9 * Real.sqrt C.ρ * Real.sqrt M := by ring
  have h2_ss : Real.sqrt (ss (C.F z - scal)) ≤ Real.sqrt C.ρ * Real.sqrt M := by
    have hσ : ss (C.F z - scal) ≤ C.σ₀ * ss z := C.hσ_bound j z hz_block
    have hσ₁ : Real.sqrt C.σ₀ ≤ Real.sqrt C.ρ := by
      have hle1 : C.ρ ≤ 1 := by linarith only [C.hρ_small]
      have h7 : C.ρ ^ 7 ≤ 1 := pow_le_one₀ (le_of_lt C.hρ_pos) hle1
      have h8 : C.ρ ^ 8 = C.ρ * C.ρ ^ 7 := by ring
      exact Real.sqrt_le_sqrt (by nlinarith only [C.hρ_pos, C.hσ₀_le, h7, h8])
    calc Real.sqrt (ss (C.F z - scal))
        ≤ Real.sqrt (C.σ₀ * ss z) := Real.sqrt_le_sqrt hσ
      _ = Real.sqrt C.σ₀ * Real.sqrt (ss z) := Real.sqrt_mul C.hσ₀_nn _
      _ ≤ Real.sqrt C.ρ * Real.sqrt M :=
          mul_le_mul hσ₁ (Real.sqrt_le_sqrt hz_ss_hi) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h3_ss : Real.sqrt (ss scal) ≤ 6 * Real.sqrt C.ρ * Real.sqrt M := by
    have hscal_ss : ss scal = ‖z.trace‖ ^ 2 / C.rkr j := by
      simp only [scal, ss_smul', norm_div, C.e_trace j, Complex.norm_natCast,
        proj_ss_eq_re_trace (C.he_sa j) (C.he_sq j), Complex.natCast_re, rkr]
      have hrj_pos : (0 : ℝ) < (C.rk j : ℝ) := C.rkr_pos j
      field_simp [ne_of_gt hrj_pos]
    have hrj_lo : (1 / 2 : ℝ) * M ≤ C.rkr j := by
      have h1 : (1 - 3 * C.ρ) * M ≤ C.rkr j := hratio.trans (min_le_right _ _)
      nlinarith only [C.hρ_small, hM_pos, h1]
    have hscal_le : ss scal ≤ 32 * C.ρ * M := by
      rw [hscal_ss, div_le_iff₀ (C.rkr_pos j)]
      have hsq : ‖z.trace‖ ^ 2 ≤ 16 * C.ρ * M ^ 2 := by
        calc ‖z.trace‖ ^ 2 ≤ (4 * Real.sqrt C.ρ * M) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) htr_z 2
          _ = 16 * (Real.sqrt C.ρ) ^ 2 * M ^ 2 := by ring
          _ = 16 * C.ρ * M ^ 2 := by rw [Real.sq_sqrt (le_of_lt C.hρ_pos)]
      nlinarith only [C.hρ_pos, hM_pos, hrj_lo, hsq]
    calc Real.sqrt (ss scal)
        ≤ Real.sqrt (36 * C.ρ * M) :=
          Real.sqrt_le_sqrt (by nlinarith only [C.hρ_pos, hM_pos, hscal_le])
      _ = Real.sqrt 36 * Real.sqrt C.ρ * Real.sqrt M := by
          rw [Real.sqrt_mul (mul_nonneg (by norm_num) (le_of_lt C.hρ_pos)),
            Real.sqrt_mul (by norm_num)]
      _ = 6 * Real.sqrt C.ρ * Real.sqrt M := by
          rw [show Real.sqrt 36 = 6 by
            rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have hz_tri : Real.sqrt (ss z) ≤ 16 * Real.sqrt C.ρ * Real.sqrt M := by
    have hz_eq : z = (z - C.F z) + ((C.F z - scal) + scal) := by abel
    have htri1 := sqrt_ss_add_le' (z - C.F z) ((C.F z - scal) + scal)
    have htri2 := sqrt_ss_add_le' (C.F z - scal) scal
    rw [← hz_eq] at htri1
    linarith only [htri1, htri2, h1_ss, h2_ss, h3_ss]
  have hsq : ss z ≤ 256 * C.ρ * M := by
    calc ss z = (Real.sqrt (ss z)) ^ 2 := (Real.sq_sqrt (ss_nonneg z)).symm
      _ ≤ (16 * Real.sqrt C.ρ * Real.sqrt M) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hz_tri 2
      _ = 256 * (Real.sqrt C.ρ) ^ 2 * (Real.sqrt M) ^ 2 := by ring
      _ = 256 * C.ρ * M := by
          rw [Real.sq_sqrt (le_of_lt C.hρ_pos), Real.sq_sqrt (le_of_lt hM_pos)]
  have hcontra : (1 - 6 * C.ρ) * M ≤ 256 * C.ρ * M := le_trans hz_ss_lo hsq
  have hcancel : 1 - 6 * C.ρ ≤ 256 * C.ρ :=
    le_of_mul_le_mul_right hcontra hM_pos
  linarith only [C.hρ_small, hcancel]

/-- Uniqueness of the high (`≥ 1 - ρ`) eigendirection in every block `B(i, j)`. -/
lemma high_eigendirection_unique {i j : Fin m} {v₁ v₂ : Mat k} {μ₁ μ₂ : ℝ}
    (hv₁ : C.e i * v₁ * C.e j = v₁) (hv₁_ne : v₁ ≠ 0) (hev₁ : C.F v₁ = (μ₁ : ℂ) • v₁)
    (hμ₁ : 1 - C.ρ ≤ μ₁)
    (hv₂ : C.e i * v₂ * C.e j = v₂) (hv₂_ne : v₂ ≠ 0) (hev₂ : C.F v₂ = (μ₂ : ℂ) • v₂)
    (hμ₂ : 1 - C.ρ ≤ μ₂)
    (horth : (star v₁ * v₂).trace = 0) : False := by
  let M : ℝ := max (C.rkr i) (C.rkr j)
  have hM_pos : 0 < M := lt_of_lt_of_le (C.rkr_pos i) (le_max_left _ _)
  let s₁ : ℝ := Real.sqrt (M / ss v₁)
  let s₂ : ℝ := Real.sqrt (M / ss v₂)
  have hs₁_pos : 0 < s₁ := Real.sqrt_pos.2 (div_pos hM_pos (ss_pos_of_ne_zero hv₁_ne))
  have hs₂_pos : 0 < s₂ := Real.sqrt_pos.2 (div_pos hM_pos (ss_pos_of_ne_zero hv₂_ne))
  let w₁ : Mat k := (s₁ : ℂ) • v₁
  let w₂ : Mat k := (s₂ : ℂ) • v₂
  have hw₁_block : C.e i * w₁ * C.e j = w₁ := by simp only [w₁, mul_smul_comm, smul_mul_assoc, hv₁]
  have hw₂_block : C.e i * w₂ * C.e j = w₂ := by simp only [w₂, mul_smul_comm, smul_mul_assoc, hv₂]
  have hw₁_ev : C.F w₁ = (μ₁ : ℂ) • w₁ := by
    change C.F ((s₁ : ℂ) • v₁) = (μ₁ : ℂ) • ((s₁ : ℂ) • v₁); rw [C.F_smul, hev₁, smul_comm]
  have hw₂_ev : C.F w₂ = (μ₂ : ℂ) • w₂ := by
    change C.F ((s₂ : ℂ) • v₂) = (μ₂ : ℂ) • ((s₂ : ℂ) • v₂); rw [C.F_smul, hev₂, smul_comm]
  have hw₁_ss : ss w₁ = M := by
    rw [ss_smul', Complex.norm_real, Real.norm_of_nonneg (le_of_lt hs₁_pos),
      Real.sq_sqrt (le_of_lt (div_pos hM_pos (ss_pos_of_ne_zero hv₁_ne))),
      div_mul_cancel₀ _ (ne_of_gt (ss_pos_of_ne_zero hv₁_ne))]
  have hw₂_ss : ss w₂ = M := by
    rw [ss_smul', Complex.norm_real, Real.norm_of_nonneg (le_of_lt hs₂_pos),
      Real.sq_sqrt (le_of_lt (div_pos hM_pos (ss_pos_of_ne_zero hv₂_ne))),
      div_mul_cancel₀ _ (ne_of_gt (ss_pos_of_ne_zero hv₂_ne))]
  have hw_orth : (star w₁ * w₂).trace = 0 := by
    simp only [w₁, w₂, star_smul, smul_mul_assoc, mul_smul_comm, Matrix.trace_smul, smul_eq_mul,
      horth, mul_zero]
  obtain ⟨hratio, u₁, hu₁_block, hu₁_op, _, _, _, _, hus₁_sa, hus₁_sq, hus₁_c, hus₁_tr,
    hdiff₁, hEu₁⟩ := C.high_eigenvector_polar hw₁_block hw₁_ss hw₁_ev hμ₁
  obtain ⟨_, u₂, hu₂_block, hu₂_op, _, _, _, hsu₂_tr, hus₂_sa, hus₂_sq, hus₂_c, hus₂_tr,
    hdiff₂, hEu₂⟩ := C.high_eigenvector_polar hw₂_block hw₂_ss hw₂_ev hμ₂
  exact C.high_polar_pair_contradiction hw₁_ss hw_orth hratio hu₁_block hu₁_op hus₁_sa hus₁_sq
    hus₁_c hus₁_tr hdiff₁ hEu₁ hu₂_block hu₂_op hsu₂_tr hus₂_sa hus₂_sq hus₂_c hus₂_tr hdiff₂ hEu₂

/-- Spectral bound on a block `B(i, j)` when all eigenvalues of `F` on `B(i, j)` are `≤ ρ`. -/
lemma block_low_spectrum_bounds {i j : Fin m}
    (hlow : ∀ v : Mat k, C.e i * v * C.e j = v → v ≠ 0 →
      ∀ μ : ℝ, C.F v = (μ : ℂ) • v → μ ≤ C.ρ)
    {x : Mat k} (hx : C.e i * x * C.e j = x) :
    ss (C.F x) ≤ C.ρ ^ 2 * ss x ∧ (1 - C.ρ) ^ 2 * ss x ≤ ss (C.F x - x) := by
  let S := C.blockSub i j
  let T := C.blockEnd i j
  have hTsymm := C.blockEnd_isSymmetric i j
  let r := Module.finrank ℂ S
  let b : OrthonormalBasis (Fin r) ℂ S := hTsymm.eigenvectorBasis rfl
  let μ : Fin r → ℝ := hTsymm.eigenvalues rfl
  have hμ_bounds : ∀ a : Fin r, 0 ≤ μ a ∧ μ a ≤ C.ρ := fun a => by
    have hev := hTsymm.hasEigenvector_eigenvectorBasis rfl a
    let va : Mat k := toHS.symm (b a).1
    have hva_block : C.e i * va * C.e j = va := (b a).2
    have hva_ne : va ≠ 0 := by
      intro h0
      apply hev.2
      apply Subtype.ext
      change (b a).1 = 0
      rw [← LinearEquiv.apply_symm_apply toHS (b a).1]
      change toHS va = 0
      rw [h0, map_zero]
    have hva_ev : C.F va = (μ a : ℂ) • va := by
      have h1 : T (b a) = (μ a : ℂ) • b a := Module.End.mem_eigenspace_iff.1 hev.1
      have h2 : toHS.symm (T (b a)).1 = toHS.symm ((μ a : ℂ) • (b a).1) :=
        congrArg (fun z : S => toHS.symm z.1) h1
      rw [map_smul] at h2
      simpa [T, blockEnd, va] using h2
    exact ⟨(C.blockEnd_eigenvalue_bounds hva_ne hva_ev).1, hlow va hva_block hva_ne (μ a) hva_ev⟩
  let vx : S := ⟨toHS x, by change C.e i * toHS.symm (toHS x) * C.e j = _; simpa using hx⟩
  have hsmul_orth : ∀ (α β : ℂ) (a c : Fin r), a ≠ c →
      @inner ℂ _ _ (α • b a) (β • b c) = 0 := fun α β a c hac => by
    change @inner ℂ _ _ (α • (b a).1) (β • (b c).1) = 0
    rw [inner_smul_left, inner_smul_right]
    have h0 : @inner ℂ _ _ (b a).1 (b c).1 = 0 := b.orthonormal.2 hac
    rw [h0, mul_zero, mul_zero]
  have hnorm_vx : ss x = ∑ a : Fin r, ‖@inner ℂ _ _ (b a) vx‖ ^ 2 := by
    have h1 : ‖vx‖ ^ 2 = ss x := by
      change ‖toHS x‖ ^ 2 = ss x; exact toHS_norm_sq x
    conv_lhs => rw [← h1, ← b.sum_repr' vx]
    rw [norm_sq_sum_of_pairwise_orth Finset.univ]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [norm_smul, b.orthonormal.1 a, mul_one]
    · intro a _ c _ hac; exact hsmul_orth _ _ a c hac
  have hFx_eq : T vx = ∑ a : Fin r, ((μ a : ℂ) * @inner ℂ _ _ (b a) vx) • b a := by
    conv_lhs => rw [← b.sum_repr' vx]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hev_a : T (b a) = (μ a : ℂ) • b a :=
      Module.End.mem_eigenspace_iff.1 (hTsymm.hasEigenvector_eigenvectorBasis rfl a).1
    rw [map_smul, hev_a, smul_smul, mul_comm]
  have hss_Fx : ss (C.F x) = ∑ a : Fin r, (μ a) ^ 2 * ‖@inner ℂ _ _ (b a) vx‖ ^ 2 := by
    have h1 : ‖T vx‖ ^ 2 = ss (C.F x) := by
      change ‖toHS (C.F (toHS.symm (toHS x)))‖ ^ 2 = ss (C.F x)
      rw [LinearEquiv.symm_apply_apply, toHS_norm_sq]
    rw [← h1, hFx_eq, norm_sq_sum_of_pairwise_orth Finset.univ]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [norm_smul, b.orthonormal.1 a, mul_one, norm_mul, mul_pow, Complex.norm_real,
        Real.norm_of_nonneg (hμ_bounds a).1]
    · intro a _ c _ hac; exact hsmul_orth _ _ a c hac
  have hdiff_eq : T vx - vx = ∑ a : Fin r, ((((μ a - 1 : ℝ) : ℂ)) * @inner ℂ _ _ (b a) vx) • b a := by
    rw [hFx_eq]
    conv_lhs => rhs; rw [← b.sum_repr' vx]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← sub_smul, Complex.ofReal_sub, Complex.ofReal_one, sub_mul, one_mul]
  have hss_diff : ss (C.F x - x) = ∑ a : Fin r, (1 - μ a) ^ 2 * ‖@inner ℂ _ _ (b a) vx‖ ^ 2 := by
    have h1 : ‖T vx - vx‖ ^ 2 = ss (C.F x - x) := by
      change ‖toHS (C.F (toHS.symm (toHS x))) - toHS x‖ ^ 2 = ss (C.F x - x)
      rw [LinearEquiv.symm_apply_apply, ← map_sub, toHS_norm_sq]
    rw [← h1, hdiff_eq, norm_sq_sum_of_pairwise_orth Finset.univ]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [norm_smul, b.orthonormal.1 a, mul_one, norm_mul, mul_pow, Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
      ring
    · intro a _ c _ hac; exact hsmul_orth _ _ a c hac
  constructor
  · rw [hss_Fx, hnorm_vx, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (hμ_bounds a).1 (hμ_bounds a).2 2) (sq_nonneg _)
  · rw [hss_diff, hnorm_vx, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have hle : 1 - C.ρ ≤ 1 - μ a := by linarith [(hμ_bounds a).2]
    have hnn : 0 ≤ 1 - C.ρ := by linarith [C.hρ_small]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnn hle 2) (sq_nonneg _)

/-- Block equivalence relation: `rel i j` holds iff `F` has an eigenvalue `≥ 1 - ρ` on `B(i, j)`. -/
def rel (i j : Fin m) : Prop :=
  ∃ v : Mat k, C.e i * v * C.e j = v ∧ v ≠ 0 ∧
    ∃ μ : ℝ, 1 - C.ρ ≤ μ ∧ C.F v = (μ : ℂ) • v

lemma rel_refl (i : Fin m) : C.rel i i :=
  ⟨C.e i, by rw [C.he_sq i, C.he_sq i], C.he_ne i, 1, by linarith [C.hρ_pos], by
    rw [C.F_fix_e i, Complex.ofReal_one, one_smul]⟩

lemma rel_symm {i j : Fin m} (h : C.rel i j) : C.rel j i := by
  rcases h with ⟨v, hv, hv_ne, μ, hμ, hev⟩
  refine ⟨star v, ?_, ?_, μ, hμ, ?_⟩
  · conv_rhs => rw [← hv]
    rw [star_mul, star_mul, C.he_sa i, C.he_sa j, mul_assoc]
  · intro h0
    apply hv_ne
    rw [← star_star v, h0, star_zero]
  · rw [C.F_star, hev, star_smul, Complex.star_def, Complex.conj_ofReal]

lemma rel_trans {i j l : Fin m} (hnobad : ¬ C.IsBadPair i l)
    (hij : C.rel i j) (hjl : C.rel j l) : C.rel i l := by
  by_contra hnot
  rcases hij with ⟨v₁, hv₁, hv₁_ne, μ₁, hμ₁, hev₁⟩
  rcases hjl with ⟨v₂, hv₂, hv₂_ne, μ₂, hμ₂, hev₂⟩
  let M₁ : ℝ := max (C.rkr i) (C.rkr j)
  let M₂ : ℝ := max (C.rkr j) (C.rkr l)
  have hM₁_pos : 0 < M₁ := lt_of_lt_of_le (C.rkr_pos i) (le_max_left _ _)
  have hM₂_pos : 0 < M₂ := lt_of_lt_of_le (C.rkr_pos j) (le_max_left _ _)
  let s₁ : ℝ := Real.sqrt (M₁ / ss v₁)
  let s₂ : ℝ := Real.sqrt (M₂ / ss v₂)
  let w₁ : Mat k := (s₁ : ℂ) • v₁
  let w₂ : Mat k := (s₂ : ℂ) • v₂
  have hw₁_block : C.e i * w₁ * C.e j = w₁ := by simp only [w₁, mul_smul_comm, smul_mul_assoc, hv₁]
  have hw₂_block : C.e j * w₂ * C.e l = w₂ := by simp only [w₂, mul_smul_comm, smul_mul_assoc, hv₂]
  have hw₁_ev : C.F w₁ = (μ₁ : ℂ) • w₁ := by
    change C.F ((s₁ : ℂ) • v₁) = (μ₁ : ℂ) • ((s₁ : ℂ) • v₁); rw [C.F_smul, hev₁, smul_comm]
  have hw₂_ev : C.F w₂ = (μ₂ : ℂ) • w₂ := by
    change C.F ((s₂ : ℂ) • v₂) = (μ₂ : ℂ) • ((s₂ : ℂ) • v₂); rw [C.F_smul, hev₂, smul_comm]
  have hw₁_ss : ss w₁ = M₁ := by
    have hs₁_nn : 0 ≤ s₁ := Real.sqrt_nonneg _
    rw [ss_smul', Complex.norm_real, Real.norm_of_nonneg hs₁_nn,
      Real.sq_sqrt (le_of_lt (div_pos hM₁_pos (ss_pos_of_ne_zero hv₁_ne))),
      div_mul_cancel₀ _ (ne_of_gt (ss_pos_of_ne_zero hv₁_ne))]
  have hw₂_ss : ss w₂ = M₂ := by
    have hs₂_nn : 0 ≤ s₂ := Real.sqrt_nonneg _
    rw [ss_smul', Complex.norm_real, Real.norm_of_nonneg hs₂_nn,
      Real.sq_sqrt (le_of_lt (div_pos hM₂_pos (ss_pos_of_ne_zero hv₂_ne))),
      div_mul_cancel₀ _ (ne_of_gt (ss_pos_of_ne_zero hv₂_ne))]
  obtain ⟨hrat₁, u₁, hu₁_block, hu₁_op, hsu₁_sa, hsu₁_sq, hsu₁_c, hsu₁_tr, _, _, _, _, _, hEu₁⟩ :=
    C.high_eigenvector_polar hw₁_block hw₁_ss hw₁_ev hμ₁
  obtain ⟨hrat₂, u₂, hu₂_block, hu₂_op, _, _, _, _, hus₂_sa, hus₂_sq, hus₂_c, hus₂_tr, _, hEu₂⟩ :=
    C.high_eigenvector_polar hw₂_block hw₂_ss hw₂_ev hμ₂
  let w : Mat k := u₁ * u₂
  have hw_block : C.e i * w * C.e l = w := by
    have hu₁l : C.e i * u₁ = u₁ := by
      calc C.e i * u₁ = C.e i * (C.e i * u₁ * C.e j) := by rw [hu₁_block]
        _ = (C.e i * C.e i) * u₁ * C.e j := by noncomm_ring
        _ = u₁ := by rw [C.he_sq i, hu₁_block]
    have hu₂r : u₂ * C.e l = u₂ := by
      calc u₂ * C.e l = (C.e j * u₂ * C.e l) * C.e l := by rw [hu₂_block]
        _ = C.e j * u₂ * (C.e l * C.e l) := by noncomm_ring
        _ = u₂ := by rw [C.he_sq l, hu₂_block]
    calc C.e i * w * C.e l = (C.e i * u₁) * (u₂ * C.e l) := by simp only [w, mul_assoc]
      _ = w := by rw [hu₁l, hu₂r]
  -- Lower bound on `ss w` via projection intersection in `e j`
  have hw_ss_lo : (1 - 6 * C.ρ) * C.rkr j ≤ ss w := by
    have heq : ss w = (((star u₁ * u₁) * (u₂ * star u₂)).trace).re := by
      rw [ss_eq_re_trace]
      congr 1
      simp only [w, star_mul]
      have h1 : star u₂ * star u₁ * (u₁ * u₂) = star u₂ * ((star u₁ * u₁) * u₂) := by
        simp only [mul_assoc]
      rw [h1, Matrix.trace_mul_comm]
      congr 1; simp only [mul_assoc]
    rw [heq]
    have hinter := proj_mul_trace_ge hsu₁_sa hsu₁_sq hus₂_sa hus₂_sq (C.he_sa j) (C.he_sq j)
      hsu₁_c hus₂_c
    rw [hsu₁_tr, hus₂_tr, Complex.natCast_re, Complex.natCast_re, C.e_re_trace j,
      Nat.cast_min, Nat.cast_min] at hinter
    have h1 : (1 - 3 * C.ρ) * C.rkr j ≤ min (C.rkr i) (C.rkr j) :=
      (mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith only [C.hρ_small])).trans hrat₁
    have h2 : (1 - 3 * C.ρ) * C.rkr j ≤ min (C.rkr j) (C.rkr l) :=
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith only [C.hρ_small])).trans hrat₂
    change min (C.rkr i) (C.rkr j) + min (C.rkr j) (C.rkr l) - C.rkr j ≤ _ at hinter
    linarith only [hinter, h1, h2]
  -- Upper bound on `ss (F w - w)` via Leibniz energy inequality
  have hM₁_le : M₁ ≤ 2 * C.rkr j := by
    have h1 : (1 - 3 * C.ρ) * M₁ ≤ C.rkr j := hrat₁.trans (min_le_right _ _)
    nlinarith [C.hρ_small, hM₁_pos]
  have hM₂_le : M₂ ≤ 2 * C.rkr j := by
    have h1 : (1 - 3 * C.ρ) * M₂ ≤ C.rkr j := hrat₂.trans (min_le_left _ _)
    nlinarith [C.hρ_small, hM₂_pos]
  have hFw_hi : ss (C.F w - w) ≤ 144 * C.ρ * C.rkr j := by
    have hEw : Real.sqrt (C.energy w) ≤ 6 * Real.sqrt C.ρ * Real.sqrt (2 * C.rkr j) := by
      calc Real.sqrt (C.energy w)
          ≤ Real.sqrt (C.energy u₁) + Real.sqrt (C.energy u₂) :=
            C.sqrt_energy_mul_le hu₁_op hu₂_op
        _ ≤ 3 * Real.sqrt C.ρ * Real.sqrt M₁ + 3 * Real.sqrt C.ρ * Real.sqrt M₂ :=
            add_le_add hEu₁ hEu₂
        _ ≤ 3 * Real.sqrt C.ρ * Real.sqrt (2 * C.rkr j) +
              3 * Real.sqrt C.ρ * Real.sqrt (2 * C.rkr j) := by
            gcongr
        _ = 6 * Real.sqrt C.ρ * Real.sqrt (2 * C.rkr j) := by ring
    have hEw_sq : C.energy w ≤ 72 * C.ρ * C.rkr j := by
      calc C.energy w = (Real.sqrt (C.energy w)) ^ 2 := (Real.sq_sqrt (C.energy_nonneg w)).symm
        _ ≤ (6 * Real.sqrt C.ρ * Real.sqrt (2 * C.rkr j)) ^ 2 :=
            pow_le_pow_left₀ (Real.sqrt_nonneg _) hEw 2
        _ = 36 * (Real.sqrt C.ρ) ^ 2 * (Real.sqrt (2 * C.rkr j)) ^ 2 := by ring
        _ = 72 * C.ρ * C.rkr j := by
            rw [Real.sq_sqrt (le_of_lt C.hρ_pos),
              Real.sq_sqrt (mul_nonneg (by norm_num) (le_of_lt (C.rkr_pos j)))]
            ring
    linarith [C.ss_F_sub_le_two_energy w]
  -- Lower bound on `ss (F w - w)` from `¬ rel i l` and `¬ IsBadPair i l`
  have hlow_il : ∀ v : Mat k, C.e i * v * C.e l = v → v ≠ 0 →
      ∀ μ : ℝ, C.F v = (μ : ℂ) • v → μ ≤ C.ρ := by
    intro v hv hv_ne μ hev
    by_contra hgt
    push Not at hgt
    by_cases hhi : 1 - C.ρ ≤ μ
    · exact hnot ⟨v, hv, hv_ne, μ, hhi, hev⟩
    · push Not at hhi
      exact hnobad ⟨v, hv, hv_ne, μ, hgt, hhi, hev⟩
  have hFw_lo : (1 - C.ρ) ^ 2 * ss w ≤ ss (C.F w - w) :=
    (C.block_low_spectrum_bounds hlow_il hw_block).2
  have hrj_pos := C.rkr_pos j
  have hcontra : (1 - C.ρ) ^ 2 * ((1 - 6 * C.ρ) * C.rkr j) ≤ 144 * C.ρ * C.rkr j := by
    have h1 : (1 - C.ρ) ^ 2 * ((1 - 6 * C.ρ) * C.rkr j) ≤ (1 - C.ρ) ^ 2 * ss w :=
      mul_le_mul_of_nonneg_left hw_ss_lo (sq_nonneg _)
    linarith
  have hρ_sm := C.hρ_small
  have h1 : (1 / 4 : ℝ) ≤ (1 - C.ρ) ^ 2 * (1 - 6 * C.ρ) := by nlinarith [C.hρ_pos]
  nlinarith

end ChannelCtx

/- ### Section 4: Clock-shift averaging, rank-one projection perturbation, matrix units, and `E_A` -/

/-- Root-of-unity orthogonality on `Fin t` (`0 < t`). -/
lemma root_of_unity_orth {t : ℕ} (ht : 0 < t) (a c : Fin t) :
    let ζ : ℂ := Complex.exp (((2 * Real.pi / (t : ℝ) : ℝ) : ℂ) * Complex.I)
    ∑ α : Fin t, ζ ^ (α.val * a.val) * star (ζ ^ (α.val * c.val)) =
      if a = c then (t : ℂ) else 0 := by
  intro ζ
  let θ : ℝ := 2 * Real.pi / (t : ℝ)
  have hζ_def : ζ = Complex.exp ((θ : ℂ) * Complex.I) := rfl
  have hζ_norm : ‖ζ‖ = 1 := by
    rw [hζ_def]
    exact Complex.norm_exp_ofReal_mul_I θ
  have hζ_pow_norm : ∀ n : ℕ, ‖ζ ^ n‖ = 1 := fun n => by rw [norm_pow, hζ_norm, one_pow]
  have hζ_t : ζ ^ t = 1 := by
    rw [hζ_def, ← Complex.exp_nat_mul]
    have ht0 : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (ne_of_gt ht)
    have hexp : (t : ℂ) * ((θ : ℂ) * Complex.I) = 2 * Real.pi * Complex.I := by
      simp only [θ, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
        Complex.ofReal_natCast]
      field_simp [ht0]
    rw [hexp]
    exact Complex.exp_two_pi_mul_I
  let ω : ℂ := ζ ^ a.val * star (ζ ^ c.val)
  have hterm : ∀ α : Fin t, ζ ^ (α.val * a.val) * star (ζ ^ (α.val * c.val)) = ω ^ α.val :=
    fun α => by
      simp only [ω, mul_pow, ← pow_mul, star_pow]
      rw [mul_comm α.val a.val, mul_comm α.val c.val]
  simp_rw [hterm]
  by_cases hac : a = c
  · subst hac
    rw [if_pos rfl]
    have hω1 : ω = 1 := by
      simp only [ω, Complex.star_def, Complex.mul_conj', hζ_pow_norm, one_pow, Complex.ofReal_one]
    simp [hω1]
  · rw [if_neg hac]
    have hω_t : ω ^ t = 1 := by
      simp only [ω, mul_pow]
      rw [← pow_mul, mul_comm a.val t, pow_mul, hζ_t, one_pow, one_mul,
        ← star_pow, ← pow_mul, mul_comm c.val t, pow_mul, hζ_t, one_pow, star_one]
    have hω_ne : ω ≠ 1 := by
      intro hω1
      have hstar_ζ : star ζ = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
        rw [hζ_def, Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
          Complex.conj_I, Complex.ofReal_neg]
        ring_nf
      have hω_exp : ω = Complex.exp
          (((((a.val : ℤ) - (c.val : ℤ) : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
        calc ω = ζ ^ a.val * (star ζ) ^ c.val := by dsimp only [ω]; rw [star_pow]
          _ = Complex.exp ((a.val : ℂ) * ((θ : ℂ) * Complex.I)) *
                Complex.exp ((c.val : ℂ) * (((-θ : ℝ) : ℂ) * Complex.I)) := by
              rw [hζ_def, hstar_ζ, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
          _ = Complex.exp ((a.val : ℂ) * ((θ : ℂ) * Complex.I) +
                (c.val : ℂ) * (((-θ : ℝ) : ℂ) * Complex.I)) := (Complex.exp_add _ _).symm
          _ = Complex.exp (((((a.val : ℤ) - (c.val : ℤ) : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
              congr 1
              push_cast
              ring
      rw [hω_exp, Complex.exp_eq_one_iff] at hω1
      rcases hω1 with ⟨n, hn⟩
      have him := congrArg Complex.im hn
      have hR : ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)).im = (n : ℝ) * (2 * Real.pi) := by
        have h1 : (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
            (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [h1, Complex.mul_I_im, Complex.ofReal_re]
      rw [Complex.mul_I_im, Complex.ofReal_re, hR] at him
      have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
      have ht_pos : (0 : ℝ) < (t : ℝ) := Nat.cast_pos.2 ht
      have heq_r : ((a.val : ℤ) - (c.val : ℤ) : ℝ) = (n : ℝ) * (t : ℝ) := by
        have h1 : (((a.val : ℤ) - (c.val : ℤ) : ℝ) / (t : ℝ)) * (2 * Real.pi) =
            (n : ℝ) * (2 * Real.pi) := by
          dsimp only [θ] at him
          rw [← him]; ring
        have h2 : ((a.val : ℤ) - (c.val : ℤ) : ℝ) / (t : ℝ) = (n : ℝ) :=
          mul_right_cancel₀ (ne_of_gt hpi) h1
        exact (div_eq_iff (ne_of_gt ht_pos)).1 h2
      have heq_z : (a.val : ℤ) - (c.val : ℤ) = n * (t : ℤ) := by exact_mod_cast heq_r
      have ha_lt : (a.val : ℤ) < (t : ℤ) := Int.ofNat_lt.2 a.2
      have hc_lt : (c.val : ℤ) < (t : ℤ) := Int.ofNat_lt.2 c.2
      have hn0 : n = 0 := by nlinarith
      subst hn0
      have hval : a.val = c.val := by omega
      exact hac (Fin.ext hval)
    have hgeom : (∑ α : Fin t, ω ^ α.val) * (ω - 1) = 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun i => ω ^ i), geom_sum_mul, hω_t, sub_self]
    exact (mul_eq_zero.1 hgeom).resolve_right (sub_ne_zero.2 hω_ne)

/-- Weyl clock-shift matrices on `projRange e`: partial-isometry and trace-averaging identities. -/
lemma clock_shift_core {k : ℕ} {e : Mat k} (he1 : star e = e) (he2 : e * e = e) (hne : e ≠ 0) :
    let t := Module.finrank ℂ (projRange e)
    ∃ D : Fin t → Fin t → Mat k,
      (∀ α β, e * D α β = D α β) ∧
      (∀ α β, star (D α β) * D α β = e) ∧
      (∀ M : Mat k, e * M * e = M →
        ∑ α : Fin t, ∑ β : Fin t, D α β * M * star (D α β) = ((t : ℂ) * M.trace) • e) := by
  classical
  intro t
  have ht : 0 < t := proj_finrank_pos he1 he2 hne
  let b : OrthonormalBasis (Fin t) ℂ (projRange e) := stdOrthonormalBasis ℂ (projRange e)
  have he_sum : e = ∑ a : Fin t, rankOne (b a : Vec k) (b a : Vec k) :=
    proj_eq_sum_rankOne_basis he1 he2 b
  let shift : Fin t → Fin t → Fin t := fun a β => ⟨(a.val + β.val) % t, Nat.mod_lt _ ht⟩
  have hmod_cancel : ∀ x y z : ℕ, x < t → y < t → z < t → (x + z) % t = (y + z) % t → x = y := by
    intro x y z hx hy hz hm
    have hred : ∀ u < t, (u + z) % t = if u + z < t then u + z else u + z - t := fun u hu => by
      split_ifs with hlt
      · exact Nat.mod_eq_of_lt hlt
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hred x hx, hred y hy] at hm
    split_ifs at hm <;> omega
  have hshift_bij_left : ∀ β : Fin t, Function.Bijective (fun a : Fin t => shift a β) := fun β => by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, rfl⟩
    intro a₁ a₂ h
    exact Fin.ext (hmod_cancel a₁.val a₂.val β.val a₁.2 a₂.2 β.2 (congrArg Fin.val h))
  have hshift_bij_right : ∀ a : Fin t, Function.Bijective (fun β : Fin t => shift a β) := fun a => by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, rfl⟩
    intro β₁ β₂ h
    have hm : (β₁.val + a.val) % t = (β₂.val + a.val) % t := by
      rw [add_comm β₁.val, add_comm β₂.val]; exact congrArg Fin.val h
    exact Fin.ext (hmod_cancel β₁.val β₂.val a.val β₁.2 β₂.2 a.2 hm)
  let ζ : ℂ := Complex.exp (((2 * Real.pi / (t : ℝ) : ℝ) : ℂ) * Complex.I)
  have hζ_norm : ‖ζ‖ = 1 := Complex.norm_exp_ofReal_mul_I (2 * Real.pi / (t : ℝ))
  let D : Fin t → Fin t → Mat k := fun α β =>
    ∑ a : Fin t, (ζ ^ (α.val * a.val)) • rankOne (b a : Vec k) (b (shift a β) : Vec k)
  have hb_orth : Orthonormal ℂ (fun a : Fin t => (b a : Vec k)) := b.orthonormal
  have hDe : ∀ α β : Fin t, e * D α β = D α β := fun α β => by
    simp only [D, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_smul_comm, mul_rankOne, (mem_projRange_iff he2 _).1 (b a).2]
  have hD_su : ∀ α β : Fin t, star (D α β) * D α β = e := fun α β => by
    rw [sum_rankOne_star_mul hb_orth]
    have hnorm : ∀ a : Fin t, ((‖ζ ^ (α.val * a.val)‖ ^ 2 : ℝ) : ℂ) = 1 := fun a => by
      rw [norm_pow, hζ_norm, one_pow, one_pow, Complex.ofReal_one]
    simp_rw [hnorm, one_smul]
    rw [Fintype.sum_bijective (fun a : Fin t => shift a β) (hshift_bij_left β)
      (fun a => rankOne (b (shift a β) : Vec k) (b (shift a β) : Vec k))
      (fun d => rankOne (b d : Vec k) (b d : Vec k)) (fun _ => rfl)]
    exact he_sum.symm
  have hD_avg : ∀ M : Mat k, e * M * e = M →
      ∑ α : Fin t, ∑ β : Fin t, D α β * M * star (D α β) = ((t : ℂ) * M.trace) • e := by
    intro M hM
    have hMe : e * M = M := by
      calc e * M = e * (e * M * e) := by rw [hM]
        _ = (e * e) * M * e := by noncomm_ring
        _ = M := by rw [he2, hM]
    have hexp : ∀ α β : Fin t,
        D α β * M * star (D α β) =
          ∑ a : Fin t, ∑ c : Fin t,
            (ζ ^ (α.val * a.val) * star (ζ ^ (α.val * c.val)) *
              @inner ℂ _ _ (b (shift a β) : Vec k)
                (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) M (b (shift c β) : Vec k))) •
              rankOne (b a : Vec k) (b c : Vec k) := fun α β => by
      dsimp only [D]
      rw [star_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [star_smul, star_rankOne, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_assoc,
        mul_rankOne, rankOne_mul_rankOne, smul_smul, smul_smul]
      congr 1
      ring
    simp_rw [hexp]
    rw [Finset.sum_comm]
    have hswap : ∀ β : Fin t,
        (∑ α : Fin t, ∑ a : Fin t, ∑ c : Fin t,
          (ζ ^ (α.val * a.val) * star (ζ ^ (α.val * c.val)) *
            @inner ℂ _ _ (b (shift a β) : Vec k)
              (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) M (b (shift c β) : Vec k))) •
            rankOne (b a : Vec k) (b c : Vec k)) =
        ∑ a : Fin t,
          ((t : ℂ) * @inner ℂ _ _ (b (shift a β) : Vec k)
            (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) M (b (shift a β) : Vec k))) •
            rankOne (b a : Vec k) (b a : Vec k) := fun β => by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      have hc : ∀ c : Fin t,
          (∑ α : Fin t,
            (ζ ^ (α.val * a.val) * star (ζ ^ (α.val * c.val)) *
              @inner ℂ _ _ (b (shift a β) : Vec k)
                (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) M (b (shift c β) : Vec k))) •
              rankOne (b a : Vec k) (b c : Vec k)) =
          if c = a then
            ((t : ℂ) * @inner ℂ _ _ (b (shift a β) : Vec k)
              (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) M (b (shift a β) : Vec k))) •
              rankOne (b a : Vec k) (b a : Vec k)
          else 0 := fun c => by
        rw [← Finset.sum_smul, ← Finset.sum_mul]
        have horth := root_of_unity_orth ht a c
        dsimp only at horth
        rw [horth]
        by_cases hca : c = a
        · subst hca; simp
        · rw [if_neg (Ne.symm hca), if_neg hca, zero_mul, zero_smul]
      simp_rw [hc, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp_rw [hswap]
    rw [Finset.sum_comm]
    have ha_sum : ∀ a : Fin t,
        (∑ β : Fin t,
          ((t : ℂ) * @inner ℂ _ _ (b (shift a β) : Vec k)
            (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) M (b (shift a β) : Vec k))) •
            rankOne (b a : Vec k) (b a : Vec k)) =
        ((t : ℂ) * M.trace) • rankOne (b a : Vec k) (b a : Vec k) := fun a => by
      rw [← Finset.sum_smul, ← Finset.mul_sum]
      congr 2
      rw [Fintype.sum_bijective (fun β : Fin t => shift a β) (hshift_bij_right a)
        (fun β => @inner ℂ _ _ (b (shift a β) : Vec k)
          (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) M (b (shift a β) : Vec k)))
        (fun d => @inner ℂ _ _ (b d : Vec k)
          (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) M (b d : Vec k))) (fun _ => rfl)]
      have htr : M.trace = ∑ d : Fin t,
          @inner ℂ _ _ (b d : Vec k)
            (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) M (b d : Vec k)) := by
        have hMe_eq : M * e = ∑ d : Fin t, M * rankOne (b d : Vec k) (b d : Vec k) := by
          conv_lhs => rw [he_sum]
          rw [Finset.mul_sum]
        calc M.trace = (M * e).trace := by rw [Matrix.trace_mul_comm, hMe]
          _ = (∑ d : Fin t, M * rankOne (b d : Vec k) (b d : Vec k)).trace := by rw [hMe_eq]
          _ = ∑ d : Fin t, (rankOne (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) M (b d : Vec k))
                (b d : Vec k)).trace := by
              rw [Matrix.trace_sum]
              refine Finset.sum_congr rfl fun d _ => by rw [mul_rankOne]
          _ = _ := Finset.sum_congr rfl fun d _ => trace_rankOne _ _
      exact htr.symm
    simp_rw [ha_sum, ← Finset.smul_sum, ← he_sum]
  exact ⟨D, hDe, hD_su, hD_avg⟩

/-- Clock-shift averaging operator-norm contraction for a single equivalence class of matrix units. -/
lemma clock_shift_opNorm_le {k m : ℕ} {e : Mat k}
    (he1 : star e = e) (he2 : e * e = e) (hne : e ≠ 0)
    (S : Finset (Fin m)) (U : Fin m → Mat k)
    (hU_iso : ∀ i ∈ S, star (U i) * U i = e)
    (hU_orth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → star (U i) * U j = 0)
    (x : Mat k) :
    let t := Module.finrank ℂ (projRange e)
    let G_K := ∑ i ∈ S, ∑ j ∈ S,
      ((star (U i * star (U j)) * x).trace / (t : ℂ)) • (U i * star (U j))
    ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) G_K‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ := by
  classical
  intro t G_K
  have ht : 0 < t := proj_finrank_pos he1 he2 hne
  have hUe : ∀ i ∈ S, U i * e = U i := fun i hi => by
    have h0 : ss (U i * (1 - e)) = 0 := by
      rw [ss_eq_re_trace, star_mul, star_sub, star_one, he1]
      have h1 : (1 - e) * star (U i) * (U i * (1 - e)) = (1 - e) * (star (U i) * U i) * (1 - e) := by
        simp only [mul_assoc]
      rw [h1, hU_iso i hi]
      have h2 : (1 - e) * e * (1 - e) = 0 := by
        calc (1 - e) * e * (1 - e) = (e - e * e) * (1 - e) := by noncomm_ring
          _ = 0 := by rw [he2, sub_self, zero_mul]
      rw [h2, Matrix.trace_zero, Complex.zero_re]
    have hdiff := (ss_eq_zero_iff' _).1 h0
    rw [mul_sub, mul_one, sub_eq_zero] at hdiff
    exact hdiff.symm
  obtain ⟨D, hDe, hD_su, hD_avg⟩ := clock_shift_core he1 he2 hne
  let Y : Fin t → Fin t → Mat k := fun α β => ∑ i ∈ S, U i * D α β * star (U i)
  let qK : Mat k := ∑ i ∈ S, U i * star (U i)
  have hqK_sa : star qK = qK := by simp only [qK, star_sum, star_mul, star_star]
  have hqK_sq : qK * qK = qK := by
    dsimp only [qK]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mul_sum]
    have hterm : ∀ j ∈ S, (U i * star (U i)) * (U j * star (U j)) =
        if j = i then U i * star (U i) else 0 := fun j hj => by
      have h1 : (U i * star (U i)) * (U j * star (U j)) = U i * (star (U i) * U j) * star (U j) := by
        simp only [mul_assoc]
      rw [h1]
      by_cases hji : j = i
      · subst hji; rw [if_pos rfl, hU_iso j hj, hUe j hj]
      · rw [if_neg hji, hU_orth i hi j hj (Ne.symm hji), mul_zero, zero_mul]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' S i, if_pos hi]
  have hY_op : ∀ α β : Fin t,
      ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (Y α β)‖ ≤ 1 := fun α β => by
    have hsu : star (Y α β) * Y α β = qK := by
      dsimp only [Y, qK]
      rw [star_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mul_sum]
      have hterm : ∀ j ∈ S, star (U i * D α β * star (U i)) * (U j * D α β * star (U j)) =
          if j = i then U i * star (U i) else 0 := fun j hj => by
        rw [star_mul, star_mul, star_star]
        have h1 : U i * (star (D α β) * star (U i)) * (U j * D α β * star (U j)) =
            U i * (star (D α β) * ((star (U i) * U j) * (D α β * star (U j)))) := by
          simp only [mul_assoc]
        rw [h1]
        by_cases hji : j = i
        · subst hji
          rw [if_pos rfl, hU_iso j hj]
          have h2 : U j * (star (D α β) * (e * (D α β * star (U j)))) =
              U j * ((star (D α β) * (e * D α β)) * star (U j)) := by simp only [mul_assoc]
          rw [h2, hDe α β, hD_su α β, ← mul_assoc, hUe j hj]
        · rw [if_neg hji, hU_orth i hi j hj (Ne.symm hji), zero_mul, mul_zero, mul_zero]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' S i, if_pos hi]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => ?_
    rw [one_mul]
    have hsq : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (Y α β) ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
      have h1 : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (Y α β) ξ‖ ^ 2 =
          ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) qK ξ‖ ^ 2 := by
        rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
        congr 1
        rw [inner_toEuclideanCLM, ← toEuclideanCLM_mul_apply, hsu, inner_toEuclideanCLM,
          ← toEuclideanCLM_mul_apply, hqK_sa, hqK_sq]
      rw [h1]
      have hle : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) qK ξ‖ ≤ ‖ξ‖ := by
        calc ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) qK ξ‖
            ≤ ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) qK‖ * ‖ξ‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * ‖ξ‖ := mul_le_mul_of_nonneg_right (proj_opNorm_le_one hqK_sa hqK_sq) (norm_nonneg ξ)
          _ = ‖ξ‖ := one_mul _
      exact pow_le_pow_left₀ (norm_nonneg _) hle 2
    nlinarith only [hsq, norm_nonneg (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (Y α β) ξ),
      norm_nonneg ξ]
  have hY_star_op : ∀ α β : Fin t,
      ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (star (Y α β))‖ ≤ 1 := fun α β => by
    rw [map_star]
    have h := ContinuousLinearMap.adjoint.norm_map
      (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (Y α β))
    change ‖ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (Y α β))‖ ≤ 1
    rw [h]; exact hY_op α β
  have havg_eq : ∑ α : Fin t, ∑ β : Fin t, Y α β * x * star (Y α β) =
      (((t : ℝ) ^ 2 : ℝ) : ℂ) • G_K := by
    have hexp : ∀ α β : Fin t,
        Y α β * x * star (Y α β) =
          ∑ i ∈ S, ∑ j ∈ S,
            U i * (D α β * (star (U i) * x * U j) * star (D α β)) * star (U j) := fun α β => by
      dsimp only [Y]
      rw [star_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [star_mul, star_mul, star_star]
      simp only [mul_assoc]
    simp_rw [hexp]
    rw [Finset.sum_comm]
    have hswap1 : ∀ β : Fin t,
        (∑ α : Fin t, ∑ i ∈ S, ∑ j ∈ S,
          U i * (D α β * (star (U i) * x * U j) * star (D α β)) * star (U j)) =
        ∑ i ∈ S, ∑ j ∈ S, ∑ α : Fin t,
          U i * (D α β * (star (U i) * x * U j) * star (D α β)) * star (U j) := fun β => by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
    simp_rw [hswap1]
    rw [Finset.sum_comm]
    simp only [G_K, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hpull : (∑ β : Fin t, ∑ α : Fin t,
        U i * (D α β * (star (U i) * x * U j) * star (D α β)) * star (U j)) =
        U i * (∑ α : Fin t, ∑ β : Fin t, D α β * (star (U i) * x * U j) * star (D α β)) *
          star (U j) := by
      rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [hpull]
    have hM_corner : e * (star (U i) * x * U j) * e = star (U i) * x * U j := by
      have hstar_e : e * star (U i) = star (U i) := by
        calc e * star (U i) = star (U i * e) := by rw [star_mul, he1]
          _ = star (U i) := by rw [hUe i hi]
      calc e * (star (U i) * x * U j) * e = (e * star (U i)) * x * (U j * e) := by
            simp only [mul_assoc]
        _ = star (U i) * x * U j := by rw [hstar_e, hUe j hj]
    rw [hD_avg _ hM_corner, mul_smul_comm, smul_mul_assoc, hUe i hi, smul_smul]
    congr 1
    have htr : (star (U i) * x * U j).trace = (star (U i * star (U j)) * x).trace := by
      rw [star_mul, star_star]
      have h1 : star (U i) * x * U j = (star (U i) * x) * U j := rfl
      rw [h1, Matrix.trace_mul_comm]
      congr 1; simp only [mul_assoc]
    rw [htr]
    have ht0 : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (ne_of_gt ht)
    push_cast
    field_simp [ht0]
    exact mul_comm _ _
  have ht2_pos : (0 : ℝ) < (t : ℝ) ^ 2 := sq_pos_of_pos (Nat.cast_pos.2 ht)
  have hnorm_le : (t : ℝ) ^ 2 * ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) G_K‖ ≤
      (t : ℝ) ^ 2 * ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ := by
    have hL : (t : ℝ) ^ 2 * ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) G_K‖ =
        ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ)
          (∑ α : Fin t, ∑ β : Fin t, Y α β * x * star (Y α β))‖ := by
      rw [havg_eq, map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt ht2_pos)]
    rw [hL, map_sum]
    calc ‖∑ α : Fin t, Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ)
            (∑ β : Fin t, Y α β * x * star (Y α β))‖
        ≤ ∑ α : Fin t, ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ)
            (∑ β : Fin t, Y α β * x * star (Y α β))‖ := norm_sum_le _ _
      _ ≤ ∑ α : Fin t, ∑ β : Fin t,
            ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (Y α β * x * star (Y α β))‖ := by
          refine Finset.sum_le_sum fun α _ => ?_
          rw [map_sum]
          exact norm_sum_le _ _
      _ ≤ ∑ _α : Fin t, ∑ _β : Fin t,
            ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ := by
          refine Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => ?_
          rw [map_mul, map_mul]
          have h1 := norm_mul_le (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (Y α β) *
            Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x)
            (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (star (Y α β)))
          have h2 := norm_mul_le (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (Y α β))
            (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x)
          have hY1 := hY_op α β
          have hY2 := hY_star_op α β
          have hx0 := norm_nonneg (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x)
          have hY20 := norm_nonneg (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (star (Y α β)))
          have hprod0 := norm_nonneg (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (Y α β) *
            Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x)
          nlinarith only [h1, h2, hY1, hY2, hx0, hY20, hprod0]
      _ = (t : ℝ) ^ 2 * ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ := by
          simp [sq, mul_assoc]
  exact le_of_mul_le_mul_left hnorm_le ht2_pos

/-- Rank-one orthogonal projection perturbation bound: for unit HS vectors `v₀, w₀`,
`‖P_{v₀} x - P_{w₀} x‖_HS ≤ 3 ‖w₀ - P_{v₀} w₀‖_HS ‖x‖_HS`. -/
lemma rank_one_proj_diff_le {k : ℕ} {v₀ w₀ : Mat k}
    (hv₀ : ss v₀ = 1) (hw₀ : ss w₀ = 1) (x : Mat k) :
    let Pv := (star v₀ * x).trace • v₀
    let Pw := (star w₀ * x).trace • w₀
    let wperp := w₀ - (star v₀ * w₀).trace • v₀
    Real.sqrt (ss (Pv - Pw)) ≤ 3 * Real.sqrt (ss wperp) * Real.sqrt (ss x) := by
  intro Pv Pw wperp
  let α : ℂ := (star v₀ * w₀).trace
  have hpyth : ‖α‖ ^ 2 + ss wperp = 1 := by
    have h1 : ss wperp = ss w₀ - 2 * ((star w₀ * (α • v₀)).trace).re + ss (α • v₀) :=
      ss_sub_eq w₀ (α • v₀)
    have h2 : (star w₀ * (α • v₀)).trace = ((‖α‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_smul_comm, Matrix.trace_smul, smul_eq_mul]
      have hc : (star w₀ * v₀).trace = star α := by
        dsimp only [α]
        rw [← toHS_inner, ← toHS_inner, ← inner_conj_symm, Complex.star_def]
      rw [hc, Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]
    rw [h2, Complex.ofReal_re, ss_smul', hv₀, mul_one, hw₀] at h1
    linarith
  let θ : ℂ := if α = 0 then 1 else α / (‖α‖ : ℂ)
  have hθ_norm : ‖θ‖ = 1 := by
    dsimp only [θ]
    split_ifs with h0
    · simp
    · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg α),
        div_self (norm_ne_zero_iff.2 h0)]
  have hθ_α : star θ * α = (‖α‖ : ℂ) := by
    dsimp only [θ]
    split_ifs with h0
    · simp [h0]
    · rw [star_div₀, Complex.star_def, Complex.conj_ofReal, div_mul_eq_mul_div,
        Complex.conj_mul']
      have hn0 : (‖α‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 h0)
      field_simp [hn0]
  let v₁ : Mat k := θ • v₀
  have hv₁_ss : ss v₁ = 1 := by rw [ss_smul', hθ_norm, one_pow, one_mul, hv₀]
  have hPv_eq : Pv = (star v₁ * x).trace • v₁ := by
    simp only [Pv, v₁, star_smul, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul, smul_smul]
    congr 1
    have h1 : star θ * θ = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hθ_norm, Complex.ofReal_one, one_pow]
    calc (star v₀ * x).trace = (star θ * θ) * (star v₀ * x).trace := by rw [h1, one_mul]
      _ = star θ * (star v₀ * x).trace * θ := by ring
  have hv₁w₀ : (star v₁ * w₀).trace = (‖α‖ : ℂ) := by
    simp only [v₁, star_smul, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul]
    exact hθ_α
  have hdiff_v₁w₀ : ss (v₁ - w₀) ≤ 2 * ss wperp := by
    have h1 : ss (v₁ - w₀) = ss v₁ - 2 * ((star v₁ * w₀).trace).re + ss w₀ := ss_sub_eq v₁ w₀
    rw [hv₁_ss, hw₀, hv₁w₀, Complex.ofReal_re] at h1
    have hα_le : ‖α‖ ≤ 1 := by nlinarith [ss_nonneg wperp, norm_nonneg α]
    have h2 : 1 - ‖α‖ ≤ 1 - ‖α‖ ^ 2 := by nlinarith [norm_nonneg α]
    linarith
  have hsplit : Pv - Pw = (star (v₁ - w₀) * x).trace • v₁ + (star w₀ * x).trace • (v₁ - w₀) := by
    rw [hPv_eq, star_sub, sub_mul, Matrix.trace_sub, sub_smul, smul_sub]
    simp only [Pw]; abel
  have htri : Real.sqrt (ss (Pv - Pw)) ≤ 2 * Real.sqrt (ss (v₁ - w₀)) * Real.sqrt (ss x) := by
    rw [hsplit]
    calc Real.sqrt (ss ((star (v₁ - w₀) * x).trace • v₁ + (star w₀ * x).trace • (v₁ - w₀)))
        ≤ Real.sqrt (ss ((star (v₁ - w₀) * x).trace • v₁)) +
            Real.sqrt (ss ((star w₀ * x).trace • (v₁ - w₀))) := sqrt_ss_add_le' _ _
      _ = ‖(star (v₁ - w₀) * x).trace‖ * Real.sqrt (ss v₁) +
            ‖(star w₀ * x).trace‖ * Real.sqrt (ss (v₁ - w₀)) := by
          rw [sqrt_ss_smul' _ v₁, sqrt_ss_smul' _ (v₁ - w₀)]
      _ ≤ (Real.sqrt (ss (v₁ - w₀)) * Real.sqrt (ss x)) * 1 +
            (Real.sqrt (ss w₀) * Real.sqrt (ss x)) * Real.sqrt (ss (v₁ - w₀)) := by
          rw [hv₁_ss, Real.sqrt_one]
          exact add_le_add
            (mul_le_mul_of_nonneg_right (norm_trace_star_mul_le _ _) zero_le_one)
            (mul_le_mul_of_nonneg_right (norm_trace_star_mul_le _ _) (Real.sqrt_nonneg _))
      _ = 2 * Real.sqrt (ss (v₁ - w₀)) * Real.sqrt (ss x) := by
          rw [hw₀, Real.sqrt_one, one_mul]; ring
  have hsq2 : 2 * Real.sqrt (ss (v₁ - w₀)) ≤ 3 * Real.sqrt (ss wperp) := by
    calc 2 * Real.sqrt (ss (v₁ - w₀))
        ≤ 2 * Real.sqrt (2 * ss wperp) := by gcongr
      _ = (2 * Real.sqrt 2) * Real.sqrt (ss wperp) := by
          rw [Real.sqrt_mul (by norm_num)]; ring
      _ ≤ 3 * Real.sqrt (ss wperp) := by
          have h2 : 2 * Real.sqrt 2 ≤ 3 := by
            have : Real.sqrt 2 ≤ 1.5 := by rw [Real.sqrt_le_iff]; constructor <;> norm_num
            linarith
          exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
  exact htri.trans (mul_le_mul_of_nonneg_right hsq2 (Real.sqrt_nonneg _))

namespace ChannelCtx

variable {k m L : ℕ} (C : ChannelCtx k m L)

/-- Blockwise `2 → 2` approximation bound (`≤ 40 √ρ`) on every retained block `B(i, j)`. -/
lemma block_approx_bound {i j : Fin m} [Decidable (C.rel i j)] (hnobad : ¬ C.IsBadPair i j)
    {W : Mat k} {t : ℝ} (ht : 0 < t)
    (hW : C.rel i j → C.e i * W * C.e j = W ∧ ss W = t ∧
      Real.sqrt (ss (C.F W - W)) ≤ 12 * Real.sqrt C.ρ * Real.sqrt t)
    {x : Mat k} (hx : C.e i * x * C.e j = x) :
    Real.sqrt (ss (C.F x - (if C.rel i j then ((star W * x).trace / (t : ℂ)) • W else 0))) ≤
      40 * Real.sqrt C.ρ * Real.sqrt (ss x) := by
  classical
  have hρ_le_sqrt : C.ρ ≤ Real.sqrt C.ρ := by
    have h1 : C.ρ ≤ 1 := by linarith only [C.hρ_small]
    have h2 : C.ρ ^ 2 ≤ C.ρ := by nlinarith only [C.hρ_pos, h1]
    calc C.ρ = Real.sqrt (C.ρ ^ 2) := (Real.sqrt_sq (le_of_lt C.hρ_pos)).symm
      _ ≤ Real.sqrt C.ρ := Real.sqrt_le_sqrt h2
  by_cases hrel : C.rel i j
  · rw [if_pos hrel]
    obtain ⟨hW_block, hW_ss, hW_fix⟩ := hW hrel
    let S := C.blockSub i j
    let T := C.blockEnd i j
    have hTsymm := C.blockEnd_isSymmetric i j
    let r := Module.finrank ℂ S
    let b : OrthonormalBasis (Fin r) ℂ S := hTsymm.eigenvectorBasis rfl
    let μ : Fin r → ℝ := hTsymm.eigenvalues rfl
    have hb_ev : ∀ a : Fin r, C.F (toHS.symm (b a).1) = (μ a : ℂ) • toHS.symm (b a).1 := fun a => by
      have h1 : T (b a) = (μ a : ℂ) • b a :=
        Module.End.mem_eigenspace_iff.1 (hTsymm.hasEigenvector_eigenvectorBasis rfl a).1
      have h2 := congrArg (fun z : S => toHS.symm z.1) h1
      rw [SetLike.val_smul, map_smul] at h2
      simpa [T, blockEnd] using h2
    have hb_ss : ∀ a : Fin r, ss (toHS.symm (b a).1) = 1 := fun a => by
      have h1 : ‖toHS (toHS.symm (b a).1)‖ = 1 := by
        rw [LinearEquiv.apply_symm_apply]; exact b.orthonormal.1 a
      rw [← toHS_norm_sq, h1, one_pow]
    have hb_ne : ∀ a : Fin r, toHS.symm (b a).1 ≠ 0 := fun a h0 => by
      have h1 := hb_ss a; rw [h0, ss_zero] at h1; norm_num at h1
    have hb_bounds : ∀ a : Fin r, 0 ≤ μ a ∧ μ a ≤ 1 := fun a =>
      C.blockEnd_eigenvalue_bounds (hb_ne a) (hb_ev a)
    have hb_dich : ∀ a : Fin r, μ a ≤ C.ρ ∨ 1 - C.ρ ≤ μ a := fun a => by
      by_contra h
      push Not at h
      exact hnobad ⟨toHS.symm (b a).1, (b a).2, hb_ne a, μ a, h.1, h.2, hb_ev a⟩
    have hsmul_orth : ∀ (α β : ℂ) (a c : Fin r), a ≠ c →
        @inner ℂ _ _ (α • b a) (β • b c) = 0 := fun α β a c hac => by
      change @inner ℂ _ _ (α • (b a).1) (β • (b c).1) = 0
      rw [inner_smul_left, inner_smul_right]
      have h0 : @inner ℂ _ _ (b a).1 (b c).1 = 0 := b.orthonormal.2 hac
      rw [h0, mul_zero, mul_zero]
    -- Existence of a high eigenvalue index `a₀`
    have hex_a₀ : ∃ a₀ : Fin r, 1 - C.ρ ≤ μ a₀ := by
      by_contra hnone
      push Not at hnone
      have hall_low : ∀ a : Fin r, μ a ≤ C.ρ := fun a => (hb_dich a).resolve_right (not_le.2 (hnone a))
      rcases hrel with ⟨v, hv_block, hv_ne, μ₀, hμ₀, hv_ev⟩
      let vv : S := ⟨toHS v, by change C.e i * toHS.symm (toHS v) * C.e j = _; simpa using hv_block⟩
      have hnorm_v : ss v = ∑ a : Fin r, ‖@inner ℂ _ _ (b a) vv‖ ^ 2 := by
        have h1 : ‖vv‖ ^ 2 = ss v := by change ‖toHS v‖ ^ 2 = ss v; exact toHS_norm_sq v
        conv_lhs => rw [← h1, ← b.sum_repr' vv]
        rw [norm_sq_sum_of_pairwise_orth Finset.univ]
        · refine Finset.sum_congr rfl fun a _ => by rw [norm_smul, b.orthonormal.1 a, mul_one]
        · intro a _ c _ hac; exact hsmul_orth _ _ a c hac
      have hFv_eq : T vv = ∑ a : Fin r, ((μ a : ℂ) * @inner ℂ _ _ (b a) vv) • b a := by
        conv_lhs => rw [← b.sum_repr' vv]
        rw [map_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        have h1 : T (b a) = (μ a : ℂ) • b a :=
          Module.End.mem_eigenspace_iff.1 (hTsymm.hasEigenvector_eigenvectorBasis rfl a).1
        rw [map_smul, h1, smul_smul, mul_comm]
      have hss_Fv : ss (C.F v) ≤ C.ρ ^ 2 * ss v := by
        have h1 : ‖T vv‖ ^ 2 = ss (C.F v) := by
          change ‖toHS (C.F (toHS.symm (toHS v)))‖ ^ 2 = ss (C.F v)
          rw [LinearEquiv.symm_apply_apply, toHS_norm_sq]
        rw [← h1, hFv_eq, norm_sq_sum_of_pairwise_orth Finset.univ, hnorm_v, Finset.mul_sum]
        · refine Finset.sum_le_sum fun a _ => ?_
          rw [norm_smul, b.orthonormal.1 a, mul_one, norm_mul, mul_pow, Complex.norm_real,
            Real.norm_of_nonneg (hb_bounds a).1]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (hb_bounds a).1 (hall_low a) 2) (sq_nonneg _)
        · intro a _ c _ hac; exact hsmul_orth _ _ a c hac
      have hss_Fv_lo : (1 - C.ρ) ^ 2 * ss v ≤ ss (C.F v) := by
        rw [hv_ev, ss_smul', Complex.norm_real, Real.norm_eq_abs, sq_abs]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by linarith only [C.hρ_small]) hμ₀ 2) (ss_nonneg v)
      have hpos : 0 < ss v := ss_pos_of_ne_zero hv_ne
      nlinarith only [hss_Fv, hss_Fv_lo, hpos, C.hρ_small, C.hρ_pos]
    obtain ⟨a₀, ha₀⟩ := hex_a₀
    have hother_low : ∀ a : Fin r, a ≠ a₀ → μ a ≤ C.ρ := fun a hne => by
      refine (hb_dich a).resolve_right fun hhi => ?_
      have horth_tr : (star (toHS.symm (b a₀).1) * toHS.symm (b a).1).trace = 0 := by
        rw [← toHS_inner, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
        exact b.orthonormal.2 (Ne.symm hne)
      exact C.high_eigendirection_unique (b a₀).2 (hb_ne a₀) (hb_ev a₀) ha₀
        (b a).2 (hb_ne a) (hb_ev a) hhi horth_tr
    let v₀ : Mat k := toHS.symm (b a₀).1
    have hv₀_ss : ss v₀ = 1 := hb_ss a₀
    -- Spectral approximation for `F y - P_{v₀} y` and `F y - y` on any `y ∈ B(i, j)`
    have hspec : ∀ y : Mat k, C.e i * y * C.e j = y →
        ss (C.F y - (star v₀ * y).trace • v₀) ≤ C.ρ ^ 2 * ss y ∧
        (1 - C.ρ) ^ 2 * ss (y - (star v₀ * y).trace • v₀) ≤ ss (C.F y - y) := by
      intro y hy
      let vy : S := ⟨toHS y, by change C.e i * toHS.symm (toHS y) * C.e j = _; simpa using hy⟩
      have hin_a₀ : (star v₀ * y).trace = @inner ℂ _ _ (b a₀) vy := by
        rw [← toHS_inner]; simp only [v₀, LinearEquiv.apply_symm_apply]; rfl
      have hnorm_vy : ss y = ∑ a : Fin r, ‖@inner ℂ _ _ (b a) vy‖ ^ 2 := by
        have h1 : ‖vy‖ ^ 2 = ss y := by change ‖toHS y‖ ^ 2 = ss y; exact toHS_norm_sq y
        conv_lhs => rw [← h1, ← b.sum_repr' vy]
        rw [norm_sq_sum_of_pairwise_orth Finset.univ]
        · refine Finset.sum_congr rfl fun a _ => by rw [norm_smul, b.orthonormal.1 a, mul_one]
        · intro a _ c _ hac; exact hsmul_orth _ _ a c hac
      have hFy_eq : T vy = ∑ a : Fin r, ((μ a : ℂ) * @inner ℂ _ _ (b a) vy) • b a := by
        conv_lhs => rw [← b.sum_repr' vy]
        rw [map_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        have h1 : T (b a) = (μ a : ℂ) • b a :=
          Module.End.mem_eigenspace_iff.1 (hTsymm.hasEigenvector_eigenvectorBasis rfl a).1
        rw [map_smul, h1, smul_smul, mul_comm]
      have hPv_sum : (star v₀ * y).trace • b a₀ =
          ∑ a : Fin r, (if a = a₀ then @inner ℂ _ _ (b a) vy else 0) • b a := by
        rw [hin_a₀]
        have hite : ∀ a : Fin r, (if a = a₀ then @inner ℂ _ _ (b a) vy else 0) • b a =
            if a = a₀ then (@inner ℂ _ _ (b a₀) vy) • b a₀ else 0 := fun a => by
          by_cases h : a = a₀
          · subst h; simp
          · simp [h]
        simp_rw [hite, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      constructor
      · have h1 : ‖T vy - (star v₀ * y).trace • b a₀‖ ^ 2 = ss (C.F y - (star v₀ * y).trace • v₀) := by
          change ‖toHS (C.F (toHS.symm (toHS y))) - (star v₀ * y).trace • (b a₀).1‖ ^ 2 = _
          have hb_eq : (b a₀).1 = toHS v₀ := (LinearEquiv.apply_symm_apply toHS _).symm
          rw [LinearEquiv.symm_apply_apply, hb_eq, ← map_smul, ← map_sub, toHS_norm_sq]
        have hdiff : T vy - (star v₀ * y).trace • b a₀ =
            ∑ a : Fin r,
              ((if a = a₀ then ((μ a₀ - 1 : ℝ) : ℂ) else (μ a : ℂ)) * @inner ℂ _ _ (b a) vy) • b a := by
          rw [hFy_eq, hPv_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun a _ => ?_
          by_cases h : a = a₀
          · subst h; simp [← sub_smul, Complex.ofReal_sub, sub_mul]
          · simp [h]
        rw [← h1, hdiff, norm_sq_sum_of_pairwise_orth Finset.univ, hnorm_vy, Finset.mul_sum]
        · refine Finset.sum_le_sum fun a _ => ?_
          rw [norm_smul, b.orthonormal.1 a, mul_one, norm_mul, mul_pow]
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          by_cases h : a = a₀
          · subst h
            rw [if_pos rfl, Complex.norm_real, Real.norm_eq_abs, sq_abs]
            have hle : |μ a - 1| ≤ C.ρ := by
              rw [abs_le]; constructor <;> linarith [(hb_bounds a).2, ha₀]
            have hsq : |μ a - 1| ^ 2 ≤ C.ρ ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) hle 2
            rwa [sq_abs] at hsq
          · rw [if_neg h, Complex.norm_real, Real.norm_of_nonneg (hb_bounds a).1]
            exact pow_le_pow_left₀ (hb_bounds a).1 (hother_low a h) 2
        · intro a _ c _ hac; exact hsmul_orth _ _ a c hac
      · have h1 : ‖vy - (star v₀ * y).trace • b a₀‖ ^ 2 = ss (y - (star v₀ * y).trace • v₀) := by
          change ‖toHS y - (star v₀ * y).trace • (b a₀).1‖ ^ 2 = _
          have hb_eq : (b a₀).1 = toHS v₀ := (LinearEquiv.apply_symm_apply toHS _).symm
          rw [hb_eq, ← map_smul, ← map_sub, toHS_norm_sq]
        have h2 : ‖T vy - vy‖ ^ 2 = ss (C.F y - y) := by
          change ‖toHS (C.F (toHS.symm (toHS y))) - toHS y‖ ^ 2 = _
          rw [LinearEquiv.symm_apply_apply, ← map_sub, toHS_norm_sq]
        have hperp_eq : vy - (star v₀ * y).trace • b a₀ =
            ∑ a : Fin r, (if a = a₀ then (0 : ℂ) else @inner ℂ _ _ (b a) vy) • b a := by
          conv_lhs => rw [← b.sum_repr' vy]
          rw [hPv_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun a _ => ?_
          by_cases h : a = a₀ <;> simp [h]
        have hFy_sub : T vy - vy =
            ∑ a : Fin r, ((((μ a - 1 : ℝ) : ℂ)) * @inner ℂ _ _ (b a) vy) • b a := by
          rw [hFy_eq]
          conv_lhs => rhs; rw [← b.sum_repr' vy]
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← sub_smul, Complex.ofReal_sub, Complex.ofReal_one, sub_mul, one_mul]
        rw [← h1, ← h2, hperp_eq, hFy_sub, norm_sq_sum_of_pairwise_orth Finset.univ,
          norm_sq_sum_of_pairwise_orth Finset.univ, Finset.mul_sum]
        · refine Finset.sum_le_sum fun a _ => ?_
          by_cases h : a = a₀
          · subst h; simp
          · rw [if_neg h, norm_smul, b.orthonormal.1 a, mul_one, norm_smul, b.orthonormal.1 a,
              mul_one, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
            have hle : 1 - C.ρ ≤ 1 - μ a := by linarith [hother_low a h]
            have hsq : (1 - C.ρ) ^ 2 ≤ (μ a - 1) ^ 2 := by
              rw [show (μ a - 1) ^ 2 = (1 - μ a) ^ 2 by ring]
              exact pow_le_pow_left₀ (by linarith only [C.hρ_small]) hle 2
            exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
        · intro a _ c _ hac; exact hsmul_orth _ _ a c hac
        · intro a _ c _ hac; exact hsmul_orth _ _ a c hac
    let w₀ : Mat k := (((Real.sqrt t)⁻¹ : ℝ) : ℂ) • W
    have hw₀_block : C.e i * w₀ * C.e j = w₀ := by
      simp only [w₀, mul_smul_comm, smul_mul_assoc, hW_block]
    have hw₀_ss : ss w₀ = 1 := by
      rw [ss_smul', Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg t)), inv_pow,
        Real.sq_sqrt (le_of_lt ht), hW_ss, inv_mul_cancel₀ (ne_of_gt ht)]
    have hw₀_fix : Real.sqrt (ss (C.F w₀ - w₀)) ≤ 12 * Real.sqrt C.ρ := by
      have h1 : C.F w₀ - w₀ = (((Real.sqrt t)⁻¹ : ℝ) : ℂ) • (C.F W - W) := by
        simp only [w₀, C.F_smul, smul_sub]
      rw [h1, sqrt_ss_smul', Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg t))]
      calc (Real.sqrt t)⁻¹ * Real.sqrt (ss (C.F W - W))
          ≤ (Real.sqrt t)⁻¹ * (12 * Real.sqrt C.ρ * Real.sqrt t) :=
            mul_le_mul_of_nonneg_left hW_fix (inv_nonneg.2 (Real.sqrt_nonneg t))
        _ = 12 * Real.sqrt C.ρ := by
            have hst : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
            field_simp [hst]
    have hwperp_le : Real.sqrt (ss (w₀ - (star v₀ * w₀).trace • v₀)) ≤ 13 * Real.sqrt C.ρ := by
      have hlo := (hspec w₀ hw₀_block).2
      have hsq : (1 - C.ρ) * Real.sqrt (ss (w₀ - (star v₀ * w₀).trace • v₀)) ≤ 12 * Real.sqrt C.ρ := by
        have h1 : (1 - C.ρ) * Real.sqrt (ss (w₀ - (star v₀ * w₀).trace • v₀)) =
            Real.sqrt ((1 - C.ρ) ^ 2 * ss (w₀ - (star v₀ * w₀).trace • v₀)) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith only [C.hρ_small])]
        rw [h1]
        exact (Real.sqrt_le_sqrt hlo).trans hw₀_fix
      have h13 : (12 : ℝ) ≤ (1 - C.ρ) * 13 := by linarith only [C.hρ_small]
      have hpos : 0 < 1 - C.ρ := by linarith only [C.hρ_small]
      nlinarith only [hsq, h13, hpos, Real.sqrt_nonneg C.ρ]
    have hPw_eq : (star w₀ * x).trace • w₀ = ((star W * x).trace / (t : ℂ)) • W := by
      simp only [w₀, star_smul, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul, smul_smul,
        Complex.star_def, Complex.conj_ofReal]
      congr 1
      have hinv : (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * (((Real.sqrt t)⁻¹ : ℝ) : ℂ) = (t : ℂ)⁻¹ := by
        rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (le_of_lt ht), Complex.ofReal_inv]
      calc (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * (star W * x).trace * (((Real.sqrt t)⁻¹ : ℝ) : ℂ)
          = (star W * x).trace * ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) * (((Real.sqrt t)⁻¹ : ℝ) : ℂ)) := by ring
        _ = (star W * x).trace / (t : ℂ) := by rw [hinv, div_eq_mul_inv]
    have hpart1 : Real.sqrt (ss (C.F x - (star v₀ * x).trace • v₀)) ≤
        Real.sqrt C.ρ * Real.sqrt (ss x) := by
      have h1 := (hspec x hx).1
      calc Real.sqrt (ss (C.F x - (star v₀ * x).trace • v₀))
          ≤ Real.sqrt (C.ρ ^ 2 * ss x) := Real.sqrt_le_sqrt h1
        _ = C.ρ * Real.sqrt (ss x) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt C.hρ_pos)]
        _ ≤ Real.sqrt C.ρ * Real.sqrt (ss x) :=
            mul_le_mul_of_nonneg_right hρ_le_sqrt (Real.sqrt_nonneg _)
    have hpart2 : Real.sqrt (ss ((star v₀ * x).trace • v₀ - (star w₀ * x).trace • w₀)) ≤
        39 * Real.sqrt C.ρ * Real.sqrt (ss x) := by
      have h1 := rank_one_proj_diff_le hv₀_ss hw₀_ss x
      dsimp only at h1
      calc Real.sqrt (ss ((star v₀ * x).trace • v₀ - (star w₀ * x).trace • w₀))
          ≤ 3 * Real.sqrt (ss (w₀ - (star v₀ * w₀).trace • v₀)) * Real.sqrt (ss x) := h1
        _ ≤ 3 * (13 * Real.sqrt C.ρ) * Real.sqrt (ss x) := by gcongr
        _ = 39 * Real.sqrt C.ρ * Real.sqrt (ss x) := by ring
    rw [← hPw_eq]
    have hsplit : C.F x - (star w₀ * x).trace • w₀ =
        (C.F x - (star v₀ * x).trace • v₀) + ((star v₀ * x).trace • v₀ - (star w₀ * x).trace • w₀) := by
      abel
    have htri := sqrt_ss_add_le' (C.F x - (star v₀ * x).trace • v₀)
      ((star v₀ * x).trace • v₀ - (star w₀ * x).trace • w₀)
    rw [← hsplit] at htri
    linarith only [htri, hpart1, hpart2]
  · rw [if_neg hrel, sub_zero]
    have hlow : ∀ v : Mat k, C.e i * v * C.e j = v → v ≠ 0 →
        ∀ μ : ℝ, C.F v = (μ : ℂ) • v → μ ≤ C.ρ := by
      intro v hv hv_ne μ hev
      by_contra hgt
      push Not at hgt
      by_cases hhi : 1 - C.ρ ≤ μ
      · exact hrel ⟨v, hv, hv_ne, μ, hhi, hev⟩
      · push Not at hhi
        exact hnobad ⟨v, hv, hv_ne, μ, hgt, hhi, hev⟩
    have hle := (C.block_low_spectrum_bounds hlow hx).1
    calc Real.sqrt (ss (C.F x)) ≤ Real.sqrt (C.ρ ^ 2 * ss x) := Real.sqrt_le_sqrt hle
      _ = C.ρ * Real.sqrt (ss x) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt C.hρ_pos)]
      _ ≤ 40 * Real.sqrt C.ρ * Real.sqrt (ss x) := by
          have h40 : C.ρ ≤ 40 * Real.sqrt C.ρ := by linarith only [hρ_le_sqrt, C.hρ_pos]
          exact mul_le_mul_of_nonneg_right h40 (Real.sqrt_nonneg _)

/-- Construct retained partition `Ret`, least-rank representatives `o`, partial isometries `U`,
matrix units `W i j = U i * star (U j)`, and projection `q = ∑_{i ∈ Ret} W i i`. -/
lemma exists_matrix_units :
    ∃ (Ret : Finset (Fin m)) (o : Fin m → Fin m) (U : Fin m → Mat k),
      (∀ i ∈ Ret, ∀ j ∈ Ret, ¬ C.IsBadPair i j) ∧
      (∑ i ∈ Finset.univ \ Ret, C.rkr i ≤ 256 * C.ρ ^ 4 * (k : ℝ)) ∧
      (∀ i ∈ Ret, o i ∈ Ret ∧ C.rel i (o i) ∧ C.rk (o i) ≤ C.rk i) ∧
      (∀ i ∈ Ret, ∀ j ∈ Ret, C.rel i j ↔ o i = o j) ∧
      (∀ i ∈ Ret, (1 - 3 * C.ρ) * C.rkr i ≤ C.rkr (o i)) ∧
      (∀ i ∈ Ret, C.e i * U i * C.e (o i) = U i ∧
        ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (U i)‖ ≤ 1 ∧
        star (U i) * U i = C.e (o i) ∧
        Real.sqrt (C.energy (U i)) ≤ 3 * Real.sqrt C.ρ * Real.sqrt (C.rkr i)) ∧
      (∀ i ∈ Ret, ∀ j ∈ Ret, C.rel i j →
        let W := U i * star (U j)
        C.e i * W * C.e j = W ∧
        ss W = C.rkr (o i) ∧
        Real.sqrt (ss (C.F W - W)) ≤ 12 * Real.sqrt C.ρ * Real.sqrt (C.rkr (o i))) := by
  classical
  obtain ⟨Ret, hRet_nobad, hBad_sum⟩ := C.exists_good_partition
  have hm_nonempty : Nonempty (Fin m) := by
    by_contra h
    have hempty : IsEmpty (Fin m) := not_nonempty_iff.1 h
    have h0 : (1 : Mat k) = 0 := by rw [← C.he_sum]; exact Finset.sum_eq_zero fun i _ => hempty.elim i
    have htr := congrArg Matrix.trace h0
    simp only [Matrix.trace_one, Fintype.card_fin, Matrix.trace_zero] at htr
    have hpos : (0 : ℕ) < k := C.hk
    exact (Nat.cast_ne_zero (R := ℂ).2 (ne_of_gt hpos)) htr
  let i₀ : Fin m := Classical.arbitrary (Fin m)
  let cls : Fin m → Finset (Fin m) := fun i => Ret.filter (fun j => C.rel i j)
  let pickRep : Finset (Fin m) → Fin m := fun S =>
    if hS : S.Nonempty then Classical.choose (Finset.exists_min_image S C.rk hS) else i₀
  let o : Fin m → Fin m := fun i => pickRep (cls i)
  have ho_mem : ∀ i ∈ Ret, o i ∈ cls i ∧ ∀ j ∈ cls i, C.rk (o i) ≤ C.rk j := fun i hi => by
    have hne : (cls i).Nonempty := ⟨i, Finset.mem_filter.2 ⟨hi, C.rel_refl i⟩⟩
    simpa only [o, pickRep, dif_pos hne] using
      Classical.choose_spec (Finset.exists_min_image (cls i) C.rk hne)
  have ho_prop : ∀ i ∈ Ret, o i ∈ Ret ∧ C.rel i (o i) ∧ C.rk (o i) ≤ C.rk i := fun i hi => by
    have h := ho_mem i hi
    have hmem := Finset.mem_filter.1 h.1
    exact ⟨hmem.1, hmem.2, h.2 i (Finset.mem_filter.2 ⟨hi, C.rel_refl i⟩)⟩
  have ho_iff : ∀ i ∈ Ret, ∀ j ∈ Ret, C.rel i j ↔ o i = o j := fun i hi j hj => by
    constructor
    · intro hij
      have hcls : cls i = cls j := by
        ext l
        simp only [cls, Finset.mem_filter]
        constructor
        · rintro ⟨hl, hil⟩
          exact ⟨hl, C.rel_trans (hRet_nobad j hj l hl) (C.rel_symm hij) hil⟩
        · rintro ⟨hl, hjl⟩
          exact ⟨hl, C.rel_trans (hRet_nobad i hi l hl) hij hjl⟩
      simp only [o, hcls]
    · intro heq
      have hi_rel := (ho_prop i hi).2.1
      have hj_rel := (ho_prop j hj).2.1
      rw [heq] at hi_rel
      exact C.rel_trans (hRet_nobad i hi j hj) hi_rel (C.rel_symm hj_rel)
  -- For every `i ∈ Ret`, extract partial isometry `U i ∈ B(i, o i)` with `star (U i) * U i = e (o i)`
  have hU_exists : ∀ i ∈ Ret,
      (1 - 3 * C.ρ) * C.rkr i ≤ C.rkr (o i) ∧
      ∃ u : Mat k,
        C.e i * u * C.e (o i) = u ∧
        ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) u‖ ≤ 1 ∧
        star u * u = C.e (o i) ∧
        Real.sqrt (C.energy u) ≤ 3 * Real.sqrt C.ρ * Real.sqrt (C.rkr i) := by
    intro i hi
    obtain ⟨ho_ret, hrel_io, ho_le⟩ := ho_prop i hi
    have hle_r : C.rkr (o i) ≤ C.rkr i := Nat.cast_le.2 ho_le
    have hmax : max (C.rkr i) (C.rkr (o i)) = C.rkr i := max_eq_left hle_r
    have hmin : min (C.rkr i) (C.rkr (o i)) = C.rkr (o i) := min_eq_right hle_r
    have hmin_nat : min (C.rk i) (C.rk (o i)) = C.rk (o i) := min_eq_right ho_le
    rcases hrel_io with ⟨v, hv, hv_ne, μ, hμ, hev⟩
    let s : ℝ := Real.sqrt (C.rkr i / ss v)
    let w : Mat k := (s : ℂ) • v
    have hw_block : C.e i * w * C.e (o i) = w := by simp only [w, mul_smul_comm, smul_mul_assoc, hv]
    have hw_ev : C.F w = (μ : ℂ) • w := by
      change C.F ((s : ℂ) • v) = (μ : ℂ) • ((s : ℂ) • v); rw [C.F_smul, hev, smul_comm]
    have hw_ss : ss w = max (C.rkr i) (C.rkr (o i)) := by
      rw [hmax, ss_smul', Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (le_of_lt (div_pos (C.rkr_pos i) (ss_pos_of_ne_zero hv_ne))),
        div_mul_cancel₀ _ (ne_of_gt (ss_pos_of_ne_zero hv_ne))]
    obtain ⟨hrat, u, hu_block, hu_op, hsu_sa, hsu_sq, hsu_c, hsu_tr, _, _, _, _, _, hEu⟩ :=
      C.high_eigenvector_polar hw_block hw_ss hw_ev hμ
    rw [hmax, hmin] at hrat
    rw [hmax] at hEu
    have hsu_eq : star u * u = C.e (o i) := by
      refine proj_eq_of_le_and_trace_eq hsu_sa hsu_sq (C.he_sa (o i)) (C.he_sq (o i)) hsu_c ?_
      rw [hsu_tr, hmin_nat, C.e_trace (o i)]
    exact ⟨hrat, u, hu_block, hu_op, hsu_eq, hEu⟩
  let U : Fin m → Mat k := fun i =>
    if hi : i ∈ Ret then Classical.choose (hU_exists i hi).2 else 0
  have hrat_all : ∀ i ∈ Ret, (1 - 3 * C.ρ) * C.rkr i ≤ C.rkr (o i) := fun i hi =>
    (hU_exists i hi).1
  have hU_prop : ∀ i ∈ Ret, C.e i * U i * C.e (o i) = U i ∧
      ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (U i)‖ ≤ 1 ∧
      star (U i) * U i = C.e (o i) ∧
      Real.sqrt (C.energy (U i)) ≤ 3 * Real.sqrt C.ρ * Real.sqrt (C.rkr i) := fun i hi => by
    simp only [U, dif_pos hi]
    exact Classical.choose_spec (hU_exists i hi).2
  have hW_prop : ∀ i ∈ Ret, ∀ j ∈ Ret, C.rel i j →
      let W := U i * star (U j)
      C.e i * W * C.e j = W ∧
      ss W = C.rkr (o i) ∧
      Real.sqrt (ss (C.F W - W)) ≤ 12 * Real.sqrt C.ρ * Real.sqrt (C.rkr (o i)) := by
    intro i hi j hj hij W
    have hoij : o i = o j := (ho_iff i hi j hj).1 hij
    obtain ⟨hUi_b, hUi_op, hUi_iso, hUi_E⟩ := hU_prop i hi
    obtain ⟨hUj_b, hUj_op, hUj_iso, hUj_E⟩ := hU_prop j hj
    have hUi_l : C.e i * U i = U i := by
      calc C.e i * U i = C.e i * (C.e i * U i * C.e (o i)) := by rw [hUi_b]
        _ = (C.e i * C.e i) * U i * C.e (o i) := by noncomm_ring
        _ = U i := by rw [C.he_sq i, hUi_b]
    have hUi_r : U i * C.e (o i) = U i := by
      calc U i * C.e (o i) = (C.e i * U i * C.e (o i)) * C.e (o i) := by rw [hUi_b]
        _ = C.e i * U i * (C.e (o i) * C.e (o i)) := by noncomm_ring
        _ = U i := by rw [C.he_sq (o i), hUi_b]
    have hUj_l : C.e j * U j = U j := by
      calc C.e j * U j = C.e j * (C.e j * U j * C.e (o j)) := by rw [hUj_b]
        _ = (C.e j * C.e j) * U j * C.e (o j) := by noncomm_ring
        _ = U j := by rw [C.he_sq j, hUj_b]
    have hW_block : C.e i * W * C.e j = W := by
      have h1 : star (U j) * C.e j = star (U j) := by
        calc star (U j) * C.e j = star (C.e j * U j) := by rw [star_mul, C.he_sa j]
          _ = star (U j) := by rw [hUj_l]
      calc C.e i * W * C.e j = (C.e i * U i) * (star (U j) * C.e j) := by simp only [W, mul_assoc]
        _ = W := by rw [hUi_l, h1]
    have hW_ss : ss W = C.rkr (o i) := by
      rw [ss_eq_re_trace]
      have h1 : (star W * W).trace = (C.e (o i)).trace := by
        simp only [W, star_mul, star_star]
        have ha : U j * star (U i) * (U i * star (U j)) =
            U j * ((star (U i) * U i) * star (U j)) := by simp only [mul_assoc]
        rw [ha, hUi_iso, Matrix.trace_mul_comm]
        have hb : C.e (o i) * star (U j) * U j = C.e (o i) * (star (U j) * U j) := by
          simp only [mul_assoc]
        rw [hb, hUj_iso, ← hoij, C.he_sq (o i)]
      rw [h1, C.e_re_trace (o i)]
    have hW_fix : Real.sqrt (ss (C.F W - W)) ≤ 12 * Real.sqrt C.ρ * Real.sqrt (C.rkr (o i)) := by
      have hUj_star_op : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (star (U j))‖ ≤ 1 := by
        rw [map_star]
        have h := ContinuousLinearMap.adjoint.norm_map
          (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (U j))
        change ‖ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (U j))‖ ≤ 1
        rw [h]; exact hUj_op
      have hrat_i : C.rkr i ≤ (25 / 16 : ℝ) * C.rkr (o i) := by
        have h := hrat_all i hi
        nlinarith only [h, C.hρ_small, C.rkr_pos i]
      have hrat_j : C.rkr j ≤ (25 / 16 : ℝ) * C.rkr (o i) := by
        have h := hrat_all j hj
        rw [← hoij] at h
        nlinarith only [h, C.hρ_small, C.rkr_pos j]
      have hsq25 : Real.sqrt (25 / 16 : ℝ) = 5 / 4 := by
        rw [show (25 / 16 : ℝ) = (5 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hsq_i : Real.sqrt (C.rkr i) ≤ (5 / 4 : ℝ) * Real.sqrt (C.rkr (o i)) := by
        calc Real.sqrt (C.rkr i) ≤ Real.sqrt ((25 / 16 : ℝ) * C.rkr (o i)) :=
              Real.sqrt_le_sqrt hrat_i
          _ = Real.sqrt (25 / 16 : ℝ) * Real.sqrt (C.rkr (o i)) := Real.sqrt_mul (by norm_num) _
          _ = (5 / 4 : ℝ) * Real.sqrt (C.rkr (o i)) := by rw [hsq25]
      have hsq_j : Real.sqrt (C.rkr j) ≤ (5 / 4 : ℝ) * Real.sqrt (C.rkr (o i)) := by
        calc Real.sqrt (C.rkr j) ≤ Real.sqrt ((25 / 16 : ℝ) * C.rkr (o i)) :=
              Real.sqrt_le_sqrt hrat_j
          _ = Real.sqrt (25 / 16 : ℝ) * Real.sqrt (C.rkr (o i)) := Real.sqrt_mul (by norm_num) _
          _ = (5 / 4 : ℝ) * Real.sqrt (C.rkr (o i)) := by rw [hsq25]
      have hEW : Real.sqrt (C.energy W) ≤ (15 / 2 : ℝ) * Real.sqrt C.ρ * Real.sqrt (C.rkr (o i)) := by
        calc Real.sqrt (C.energy W)
            ≤ Real.sqrt (C.energy (U i)) + Real.sqrt (C.energy (star (U j))) :=
              C.sqrt_energy_mul_le hUi_op hUj_star_op
          _ = Real.sqrt (C.energy (U i)) + Real.sqrt (C.energy (U j)) := by rw [C.energy_star]
          _ ≤ 3 * Real.sqrt C.ρ * Real.sqrt (C.rkr i) +
                3 * Real.sqrt C.ρ * Real.sqrt (C.rkr j) := add_le_add hUi_E hUj_E
          _ ≤ 3 * Real.sqrt C.ρ * ((5 / 4 : ℝ) * Real.sqrt (C.rkr (o i))) +
                3 * Real.sqrt C.ρ * ((5 / 4 : ℝ) * Real.sqrt (C.rkr (o i))) := by
              refine add_le_add ?_ ?_ <;>
                exact mul_le_mul_of_nonneg_left (by assumption)
                  (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
          _ = (15 / 2 : ℝ) * Real.sqrt C.ρ * Real.sqrt (C.rkr (o i)) := by ring
      calc Real.sqrt (ss (C.F W - W))
          ≤ Real.sqrt (2 * C.energy W) := Real.sqrt_le_sqrt (C.ss_F_sub_le_two_energy W)
        _ = Real.sqrt 2 * Real.sqrt (C.energy W) := Real.sqrt_mul (by norm_num) _
        _ ≤ 1.5 * ((15 / 2 : ℝ) * Real.sqrt C.ρ * Real.sqrt (C.rkr (o i))) := by
            have hsq2 : Real.sqrt 2 ≤ 1.5 := by rw [Real.sqrt_le_iff]; constructor <;> norm_num
            exact mul_le_mul hsq2 hEW (Real.sqrt_nonneg _) (by norm_num)
        _ ≤ 12 * Real.sqrt C.ρ * Real.sqrt (C.rkr (o i)) := by
            have hnn : 0 ≤ Real.sqrt C.ρ * Real.sqrt (C.rkr (o i)) :=
              mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
            linarith only [hnn]
    exact ⟨hW_block, hW_ss, hW_fix⟩
  exact ⟨Ret, o, U, hRet_nobad, hBad_sum, ho_prop, ho_iff, hrat_all, hU_prop, hW_prop⟩

/-- Single-coordinate Theorem 5.2 rounding: constructs an internal `StarSubalgebra` `A` and
a linear contraction `E : Mat k →ₗ[ℂ] Mat k` onto `A` with `ss (F x - E x) ≤ 1849 * ρ * k`
for every contraction `x`. -/
lemma coord_rounding :
    ∃ (A : StarSubalgebra ℂ (Mat k)) (E : Mat k →ₗ[ℂ] Mat k),
      (∀ x, E x ∈ A) ∧
      (∀ x ∈ A, E x = x) ∧
      (∀ x, ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (E x)‖ ≤
        ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖) ∧
      (∀ x, ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ≤ 1 →
        ss (C.F x - E x) ≤ 1849 * C.ρ * (k : ℝ)) := by
  classical
  obtain ⟨Ret, o, U, hRet_nobad, hBad_sum, ho_prop, ho_iff, hrat_all, hU_prop, hW_prop⟩ :=
    C.exists_matrix_units
  let W : Fin m → Fin m → Mat k := fun i j => U i * star (U j)
  let q : Mat k := ∑ i ∈ Ret, W i i
  -- Basic algebraic identities for `U`, `W`, `q`
  have hU_orth : ∀ i ∈ Ret, ∀ j ∈ Ret, i ≠ j → star (U i) * U j = 0 := fun i hi j hj hij => by
    have hUi : C.e i * U i = U i := by
      have hb := (hU_prop i hi).1
      calc C.e i * U i = C.e i * (C.e i * U i * C.e (o i)) := by rw [hb]
        _ = (C.e i * C.e i) * U i * C.e (o i) := by noncomm_ring
        _ = U i := by rw [C.he_sq i, hb]
    have hUj : C.e j * U j = U j := by
      have hb := (hU_prop j hj).1
      calc C.e j * U j = C.e j * (C.e j * U j * C.e (o j)) := by rw [hb]
        _ = (C.e j * C.e j) * U j * C.e (o j) := by noncomm_ring
        _ = U j := by rw [C.he_sq j, hb]
    have hUi_s : star (U i) * C.e i = star (U i) := by
      calc star (U i) * C.e i = star (C.e i * U i) := by rw [star_mul, C.he_sa i]
        _ = star (U i) := by rw [hUi]
    calc star (U i) * U j = (star (U i) * C.e i) * (C.e j * U j) := by rw [hUi_s, hUj]
      _ = star (U i) * (C.e i * C.e j) * U j := by simp only [mul_assoc]
      _ = 0 := by rw [C.he_orth i j hij, mul_zero, zero_mul]
  have hU_r : ∀ i ∈ Ret, U i * C.e (o i) = U i := fun i hi => by
    have hb := (hU_prop i hi).1
    calc U i * C.e (o i) = (C.e i * U i * C.e (o i)) * C.e (o i) := by rw [hb]
      _ = C.e i * U i * (C.e (o i) * C.e (o i)) := by noncomm_ring
      _ = U i := by rw [C.he_sq (o i), hb]
  have hW_star : ∀ i j, star (W i j) = W j i := fun i j => by
    simp only [W, star_mul, star_star]
  have hW_mul : ∀ i ∈ Ret, ∀ j ∈ Ret, ∀ l ∈ Ret, ∀ r ∈ Ret,
      C.rel i j → C.rel l r → W i j * W l r = if j = l then W i r else 0 := by
    intro i hi j hj l hl r hr hij _
    have h1 : W i j * W l r = U i * (star (U j) * U l) * star (U r) := by simp only [W, mul_assoc]
    rw [h1]
    by_cases hjl : j = l
    · subst hjl
      rw [if_pos rfl, (hU_prop j hj).2.2.1, ← (ho_iff i hi j hj).1 hij, hU_r i hi]
    · rw [if_neg hjl, hU_orth j hj l hl hjl, mul_zero, zero_mul]
  have hq_sa : star q = q := by
    simp only [q, star_sum, hW_star]
  have hq_W : ∀ i ∈ Ret, ∀ j ∈ Ret, C.rel i j → q * W i j = W i j := fun i hi j hj hij => by
    dsimp only [q]
    rw [Finset.sum_mul]
    have hterm : ∀ l ∈ Ret, W l l * W i j = if l = i then W i j else 0 := fun l hl => by
      rw [hW_mul l hl l hl i hi j hj (C.rel_refl l) hij]
      by_cases hli : l = i
      · subst hli; simp
      · rw [if_neg hli, if_neg hli]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' Ret i, if_pos hi]
  have hW_q : ∀ i ∈ Ret, ∀ j ∈ Ret, C.rel i j → W i j * q = W i j := fun i hi j hj hij => by
    calc W i j * q = star (q * star (W i j)) := by rw [star_mul, hq_sa, star_star]
      _ = star (q * W j i) := by rw [hW_star]
      _ = star (W j i) := by rw [hq_W j hj i hi (C.rel_symm hij)]
      _ = W i j := hW_star j i
  have hq_sq : q * q = q := by
    conv_lhs => rhs; dsimp only [q]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => hq_W i hi i hi (C.rel_refl i)
  have h1q_sa : star (1 - q) = 1 - q := by rw [star_sub, star_one, hq_sa]
  have h1q_sq : (1 - q) * (1 - q) = 1 - q := by
    calc (1 - q) * (1 - q) = 1 - q - q + q * q := by noncomm_ring
      _ = 1 - q := by rw [hq_sq]; abel
  -- Span `A₀` of matrix units and `StarSubalgebra` `A`
  let A₀ : Set (Mat k) := {y | ∃ c : Fin m → Fin m → ℂ,
    y = ∑ i ∈ Ret, ∑ j ∈ Ret, if C.rel i j then c i j • W i j else 0}
  have hA₀_q : ∀ y ∈ A₀, q * y = y ∧ y * q = y := by
    rintro y ⟨c, rfl⟩
    constructor
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      split_ifs with hij
      · rw [mul_smul_comm, hq_W i hi j hj hij]
      · rw [mul_zero]
    · rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j hj => ?_
      split_ifs with hij
      · rw [smul_mul_assoc, hW_q i hi j hj hij]
      · rw [zero_mul]
  have hA₀_add : ∀ x ∈ A₀, ∀ y ∈ A₀, x + y ∈ A₀ := by
    rintro x ⟨c, rfl⟩ y ⟨d, rfl⟩
    refine ⟨fun i j => c i j + d i j, ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp [add_smul]
  have hA₀_star : ∀ x ∈ A₀, star x ∈ A₀ := by
    rintro x ⟨c, rfl⟩
    refine ⟨fun i j => star (c j i), ?_⟩
    rw [star_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : C.rel j i
    · rw [if_pos h, if_pos (C.rel_symm h), star_smul, hW_star]
    · rw [if_neg h, if_neg (fun h' => h (C.rel_symm h')), star_zero]
  have hA₀_mul : ∀ x ∈ A₀, ∀ y ∈ A₀, x * y ∈ A₀ := by
    rintro x ⟨c, rfl⟩ y ⟨d, rfl⟩
    refine ⟨fun i r => ∑ j ∈ Ret, if C.rel i j then c i j * d j r else 0, ?_⟩
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_mul]
    have hstep : (∑ j ∈ Ret,
        (if C.rel i j then c i j • W i j else 0) *
          (∑ l ∈ Ret, ∑ r ∈ Ret, if C.rel l r then d l r • W l r else 0)) =
        ∑ r ∈ Ret, ∑ j ∈ Ret,
          if C.rel i j then
            if C.rel j r then (c i j * d j r) • W i r else 0
          else 0 := by
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j hj => ?_
      by_cases hij : C.rel i j
      · rw [if_pos hij, Finset.mul_sum]
        have hinner : ∀ l ∈ Ret,
            (c i j • W i j) * (∑ r ∈ Ret, if C.rel l r then d l r • W l r else 0) =
              if l = j then ∑ r ∈ Ret, if C.rel j r then (c i j * d j r) • W i r else 0 else 0 :=
          fun l hl => by
            rw [Finset.mul_sum]
            by_cases hlj : l = j
            · subst hlj
              rw [if_pos rfl]
              refine Finset.sum_congr rfl fun r hr => ?_
              by_cases hjr : C.rel l r
              · rw [if_pos hjr, if_pos hjr, smul_mul_assoc, mul_smul_comm, smul_smul,
                  hW_mul i hi l hl l hl r hr hij hjr, if_pos rfl]
              · rw [if_neg hjr, if_neg hjr, mul_zero]
            · rw [if_neg hlj]
              refine Finset.sum_eq_zero fun r hr => ?_
              split_ifs with hlr
              · rw [smul_mul_assoc, mul_smul_comm, hW_mul i hi j hj l hl r hr hij hlr,
                  if_neg (Ne.symm hlj), smul_zero, smul_zero]
              · rw [mul_zero]
        rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq' Ret j, if_pos hj]
        refine Finset.sum_congr rfl fun r _ => by rw [if_pos hij]
      · simp [hij]
    rw [hstep]
    refine Finset.sum_congr rfl fun r hr => ?_
    by_cases hir : C.rel i r
    · rw [if_pos hir, Finset.sum_smul]
      refine Finset.sum_congr rfl fun j hj => ?_
      by_cases hij : C.rel i j
      · have hjr : C.rel j r := C.rel_trans (hRet_nobad j hj r hr) (C.rel_symm hij) hir
        rw [if_pos hij, if_pos hjr, if_pos hij]
      · rw [if_neg hij, if_neg hij, zero_smul]
    · rw [if_neg hir]
      refine Finset.sum_eq_zero fun j hj => ?_
      by_cases hij : C.rel i j
      · have hnjr : ¬ C.rel j r := fun hjr => hir (C.rel_trans (hRet_nobad i hi r hr) hij hjr)
        rw [if_pos hij, if_neg hnjr]
      · rw [if_neg hij]
  let A : StarSubalgebra ℂ (Mat k) :=
    { carrier := {x | q * x * (1 - q) = 0 ∧ (1 - q) * x * q = 0 ∧ q * x * q ∈ A₀}
      mul_mem' := by
        rintro x y ⟨hx1, hx2, hx0⟩ ⟨hy1, hy2, hy0⟩
        have hxd : x = q * x * q + (1 - q) * x * (1 - q) := by
          have h := hx1; have h' := hx2
          calc x = (q + (1 - q)) * x * (q + (1 - q)) := by rw [add_sub_cancel, one_mul, mul_one]
            _ = q * x * q + q * x * (1 - q) + (1 - q) * x * q + (1 - q) * x * (1 - q) := by
                noncomm_ring
            _ = q * x * q + (1 - q) * x * (1 - q) := by rw [h, h']; abel
        have hyd : y = q * y * q + (1 - q) * y * (1 - q) := by
          have h := hy1; have h' := hy2
          calc y = (q + (1 - q)) * y * (q + (1 - q)) := by rw [add_sub_cancel, one_mul, mul_one]
            _ = q * y * q + q * y * (1 - q) + (1 - q) * y * q + (1 - q) * y * (1 - q) := by
                noncomm_ring
            _ = q * y * q + (1 - q) * y * (1 - q) := by rw [h, h']; abel
        have hq1q : q * (1 - q) = 0 := by rw [mul_sub, mul_one, hq_sq, sub_self]
        have h1qq : (1 - q) * q = 0 := by rw [sub_mul, one_mul, hq_sq, sub_self]
        have hxy : x * y = (q * x * q) * (q * y * q) + ((1 - q) * x * (1 - q)) * ((1 - q) * y * (1 - q)) := by
          conv_lhs => rw [hxd, hyd]
          have h1 : (q * x * q) * ((1 - q) * y * (1 - q)) = 0 := by
            have : (q * x * q) * ((1 - q) * y * (1 - q)) = q * x * (q * (1 - q)) * y * (1 - q) := by
              simp only [mul_assoc]
            rw [this, hq1q, mul_zero, zero_mul, zero_mul]
          have h2 : ((1 - q) * x * (1 - q)) * (q * y * q) = 0 := by
            have : ((1 - q) * x * (1 - q)) * (q * y * q) = (1 - q) * x * ((1 - q) * q) * y * q := by
              simp only [mul_assoc]
            rw [this, h1qq, mul_zero, zero_mul, zero_mul]
          rw [add_mul, mul_add, mul_add, h1, h2, add_zero, zero_add]
        refine ⟨?_, ?_, ?_⟩
        · rw [hxy, mul_add, add_mul]
          have h1 : q * ((q * x * q) * (q * y * q)) * (1 - q) = 0 := by
            have : q * ((q * x * q) * (q * y * q)) * (1 - q) =
                q * q * x * q * q * y * (q * (1 - q)) := by simp only [mul_assoc]
            rw [this, hq1q, mul_zero]
          have h2 : q * (((1 - q) * x * (1 - q)) * ((1 - q) * y * (1 - q))) * (1 - q) = 0 := by
            have : q * (((1 - q) * x * (1 - q)) * ((1 - q) * y * (1 - q))) * (1 - q) =
                (q * (1 - q)) * (x * ((1 - q) * ((1 - q) * (y * ((1 - q) * (1 - q)))))) := by
              simp only [mul_assoc]
            rw [this, hq1q, zero_mul]
          rw [h1, h2, add_zero]
        · rw [hxy, mul_add, add_mul]
          have h1 : (1 - q) * ((q * x * q) * (q * y * q)) * q = 0 := by
            have : (1 - q) * ((q * x * q) * (q * y * q)) * q =
                ((1 - q) * q) * (x * (q * (q * (y * (q * q))))) := by simp only [mul_assoc]
            rw [this, h1qq, zero_mul]
          have h2 : (1 - q) * (((1 - q) * x * (1 - q)) * ((1 - q) * y * (1 - q))) * q = 0 := by
            have : (1 - q) * (((1 - q) * x * (1 - q)) * ((1 - q) * y * (1 - q))) * q =
                (1 - q) * (1 - q) * x * (1 - q) * (1 - q) * y * ((1 - q) * q) := by
              simp only [mul_assoc]
            rw [this, h1qq, mul_zero]
          rw [h1, h2, add_zero]
        · have heq : q * (x * y) * q = (q * x * q) * (q * y * q) := by
            rw [hxy, mul_add, add_mul]
            have h1 : q * ((q * x * q) * (q * y * q)) * q = (q * x * q) * (q * y * q) := by
              have hql := (hA₀_q _ hx0).1; have hqr := (hA₀_q _ hy0).2
              calc q * ((q * x * q) * (q * y * q)) * q = (q * (q * x * q)) * ((q * y * q) * q) := by
                    simp only [mul_assoc]
                _ = (q * x * q) * (q * y * q) := by rw [hql, hqr]
            have h2 : q * (((1 - q) * x * (1 - q)) * ((1 - q) * y * (1 - q))) * q = 0 := by
              have : q * (((1 - q) * x * (1 - q)) * ((1 - q) * y * (1 - q))) * q =
                  (q * (1 - q)) * (x * ((1 - q) * ((1 - q) * (y * ((1 - q) * q))))) := by
                simp only [mul_assoc]
              rw [this, hq1q, zero_mul]
            rw [h1, h2, add_zero]
          rw [heq]
          exact hA₀_mul _ hx0 _ hy0
      add_mem' := by
        rintro x y ⟨hx1, hx2, hx0⟩ ⟨hy1, hy2, hy0⟩
        refine ⟨by rw [mul_add, add_mul, hx1, hy1, add_zero],
          by rw [mul_add, add_mul, hx2, hy2, add_zero],
          by rw [mul_add, add_mul]; exact hA₀_add _ hx0 _ hy0⟩
      algebraMap_mem' := fun z => by
        have hz : algebraMap ℂ (Mat k) z = z • (1 : Mat k) := by
          rw [Algebra.algebraMap_eq_smul_one]
        rw [hz]
        have hq1q : q * (1 - q) = 0 := by rw [mul_sub, mul_one, hq_sq, sub_self]
        have h1qq : (1 - q) * q = 0 := by rw [sub_mul, one_mul, hq_sq, sub_self]
        refine ⟨by rw [mul_smul_comm, smul_mul_assoc, mul_one, hq1q, smul_zero],
          by rw [mul_smul_comm, smul_mul_assoc, mul_one, h1qq, smul_zero], ?_⟩
        rw [mul_smul_comm, smul_mul_assoc, mul_one, hq_sq]
        refine ⟨fun i j => if i = j then z else 0, ?_⟩
        dsimp only [q]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hterm : ∀ j ∈ Ret, (if C.rel i j then (if i = j then z else 0) • W i j else 0) =
            if j = i then z • W i i else 0 := fun j _ => by
          by_cases hji : j = i
          · subst hji; rw [if_pos (C.rel_refl j), if_pos rfl, if_pos rfl]
          · rw [if_neg hji]
            split_ifs with h1 h2
            · exact absurd h2.symm hji
            · exact zero_smul _ _
            · rfl
        rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' Ret i, if_pos hi]
      star_mem' := by
        rintro x ⟨hx1, hx2, hx0⟩
        refine ⟨?_, ?_, ?_⟩
        · have h := congrArg star hx2
          simp only [star_mul, h1q_sa, hq_sa, star_zero, mul_assoc] at h ⊢
          exact h
        · have h := congrArg star hx1
          simp only [star_mul, h1q_sa, hq_sa, star_zero, mul_assoc] at h ⊢
          exact h
        · have h : q * star x * q = star (q * x * q) := by
            simp only [star_mul, hq_sa, mul_assoc]
          rw [h]
          exact hA₀_star _ hx0 }
  -- Define linear conditional expectation `E`
  let G : Mat k → Mat k := fun x =>
    ∑ i ∈ Ret, ∑ j ∈ Ret,
      if C.rel i j then ((star (W i j) * x).trace / (C.rkr (o i) : ℂ)) • W i j else 0
  let E : Mat k →ₗ[ℂ] Mat k :=
    { toFun := fun x => G x + (1 - q) * x * (1 - q)
      map_add' := fun x y => by
        dsimp only [G]
        have hG : (∑ i ∈ Ret, ∑ j ∈ Ret,
              if C.rel i j then ((star (W i j) * (x + y)).trace / (C.rkr (o i) : ℂ)) • W i j else 0) =
            (∑ i ∈ Ret, ∑ j ∈ Ret,
              if C.rel i j then ((star (W i j) * x).trace / (C.rkr (o i) : ℂ)) • W i j else 0) +
            (∑ i ∈ Ret, ∑ j ∈ Ret,
              if C.rel i j then ((star (W i j) * y).trace / (C.rkr (o i) : ℂ)) • W i j else 0) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs
          · rw [mul_add, Matrix.trace_add, add_div, add_smul]
          · rw [add_zero]
        rw [hG, mul_add, add_mul]; abel
      map_smul' := fun c x => by
        dsimp only [G, RingHom.id_apply]
        have hG : (∑ i ∈ Ret, ∑ j ∈ Ret,
              if C.rel i j then ((star (W i j) * (c • x)).trace / (C.rkr (o i) : ℂ)) • W i j else 0) =
            c • (∑ i ∈ Ret, ∑ j ∈ Ret,
              if C.rel i j then ((star (W i j) * x).trace / (C.rkr (o i) : ℂ)) • W i j else 0) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs
          · rw [mul_smul_comm, Matrix.trace_smul, smul_eq_mul, mul_div_assoc, smul_smul]
          · rw [smul_zero]
        rw [hG, mul_smul_comm, smul_mul_assoc, smul_add] }
  have hG_mem_A₀ : ∀ x, G x ∈ A₀ := fun x =>
    ⟨fun i j => (star (W i j) * x).trace / (C.rkr (o i) : ℂ), rfl⟩
  have hq1q : q * (1 - q) = 0 := by rw [mul_sub, mul_one, hq_sq, sub_self]
  have h1qq : (1 - q) * q = 0 := by rw [sub_mul, one_mul, hq_sq, sub_self]
  -- Property 1: `E x ∈ A`
  have hE_mem : ∀ x, E x ∈ A := fun x => by
    change q * (G x + (1 - q) * x * (1 - q)) * (1 - q) = 0 ∧
      (1 - q) * (G x + (1 - q) * x * (1 - q)) * q = 0 ∧
      q * (G x + (1 - q) * x * (1 - q)) * q ∈ A₀
    have hqG := hA₀_q (G x) (hG_mem_A₀ x)
    refine ⟨?_, ?_, ?_⟩
    · rw [mul_add, add_mul, hqG.1, ← hqG.2]
      have h1 : G x * q * (1 - q) = 0 := by rw [mul_assoc, hq1q, mul_zero]
      have h2 : q * ((1 - q) * x * (1 - q)) * (1 - q) = 0 := by
        have : q * ((1 - q) * x * (1 - q)) * (1 - q) = (q * (1 - q)) * (x * ((1 - q) * (1 - q))) := by
          simp only [mul_assoc]
        rw [this, hq1q, zero_mul]
      rw [h1, h2, add_zero]
    · rw [mul_add, add_mul, ← hqG.1]
      have h1 : (1 - q) * (q * G x) * q = 0 := by
        have : (1 - q) * (q * G x) * q = ((1 - q) * q) * (G x * q) := by simp only [mul_assoc]
        rw [this, h1qq, zero_mul]
      have h2 : (1 - q) * ((1 - q) * x * (1 - q)) * q = 0 := by
        have : (1 - q) * ((1 - q) * x * (1 - q)) * q = (1 - q) * (1 - q) * x * ((1 - q) * q) := by
          simp only [mul_assoc]
        rw [this, h1qq, mul_zero]
      rw [h1, h2, add_zero]
    · have h1 : q * ((1 - q) * x * (1 - q)) * q = 0 := by
        have : q * ((1 - q) * x * (1 - q)) * q = (q * (1 - q)) * (x * ((1 - q) * q)) := by
          simp only [mul_assoc]
        rw [this, hq1q, zero_mul]
      rw [mul_add, add_mul, hqG.1, hqG.2, h1, add_zero]
      exact hG_mem_A₀ x
  -- Property 2: `x ∈ A → E x = x`
  have hE_fix : ∀ x ∈ A, E x = x := by
    rintro x ⟨hx1, hx2, c, hc⟩
    have hxd : x = q * x * q + (1 - q) * x * (1 - q) := by
      calc x = (q + (1 - q)) * x * (q + (1 - q)) := by rw [add_sub_cancel, one_mul, mul_one]
        _ = q * x * q + q * x * (1 - q) + (1 - q) * x * q + (1 - q) * x * (1 - q) := by
            noncomm_ring
        _ = q * x * q + (1 - q) * x * (1 - q) := by rw [hx1, hx2]; abel
    change G x + (1 - q) * x * (1 - q) = x
    suffices hGx : G x = q * x * q by rw [hGx, ← hxd]
    rw [hc]
    dsimp only [G]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    by_cases hij : C.rel i j
    · rw [if_pos hij, if_pos hij]
      congr 1
      have htr_x : (star (W i j) * x).trace = (star (W i j) * (q * x * q)).trace := by
        have hWq := hW_q j hj i hi (C.rel_symm hij)
        have hqW := hq_W j hj i hi (C.rel_symm hij)
        calc (star (W i j) * x).trace = (W j i * x).trace := by rw [hW_star]
          _ = ((q * W j i * q) * x).trace := by rw [hqW, hWq]
          _ = (q * (W j i * q * x)).trace := by simp only [mul_assoc]
          _ = (W j i * q * x * q).trace := Matrix.trace_mul_comm _ _
          _ = (star (W i j) * (q * x * q)).trace := by rw [hW_star]; simp only [mul_assoc]
      rw [htr_x, hc, Finset.mul_sum, Matrix.trace_sum]
      have houter : ∀ a ∈ Ret,
          (star (W i j) * ∑ b ∈ Ret, if C.rel a b then c a b • W a b else 0).trace =
            if a = i then c i j * (C.rkr (o i) : ℂ) else 0 := fun a ha => by
        rw [Finset.mul_sum, Matrix.trace_sum, hW_star]
        by_cases hai : a = i
        · subst hai
          rw [if_pos rfl]
          have hinner : ∀ b ∈ Ret,
              (W j a * if C.rel a b then c a b • W a b else 0).trace =
                if b = j then c a j * (C.rkr (o a) : ℂ) else 0 := fun b hb => by
            by_cases hbj : b = j
            · subst hbj
              rw [if_pos rfl, if_pos hij, mul_smul_comm, Matrix.trace_smul, smul_eq_mul,
                hW_mul b hb a ha a ha b hb (C.rel_symm hij) hij, if_pos rfl]
              congr 1
              have hss := (hW_prop b hb b hb (C.rel_refl b)).2.1
              have htr_Wjj : (W b b).trace = (C.rkr (o a) : ℂ) := by
                have h1 : (W b b).trace = (star (W b b) * W b b).trace := by
                  rw [hW_star, hW_mul b hb b hb b hb b hb (C.rel_refl b) (C.rel_refl b), if_pos rfl]
                rw [h1, trace_star_mul_self_eq_ss, hss, (ho_iff a ha b hb).1 hij]
              exact htr_Wjj
            · rw [if_neg hbj]
              split_ifs with hab
              · rw [mul_smul_comm, Matrix.trace_smul, smul_eq_mul,
                  hW_mul j hj a ha a ha b hb (C.rel_symm hij) hab, if_pos rfl]
                have htr0 : (W j b).trace = 0 := by
                  have hWb := (hW_prop j hj b hb (C.rel_trans (hRet_nobad j hj b hb)
                    (C.rel_symm hij) hab)).1
                  calc (W j b).trace = (C.e j * W j b * C.e b).trace := by rw [hWb]
                    _ = (C.e j * (W j b * C.e b)).trace := by simp only [mul_assoc]
                    _ = (W j b * C.e b * C.e j).trace := Matrix.trace_mul_comm _ _
                    _ = (W j b * (C.e b * C.e j)).trace := by simp only [mul_assoc]
                    _ = 0 := by rw [C.he_orth b j hbj, mul_zero, Matrix.trace_zero]
                rw [htr0, mul_zero]
              · rw [mul_zero, Matrix.trace_zero]
          rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq' Ret j, if_pos hj]
        · rw [if_neg hai]
          refine Finset.sum_eq_zero fun b hb => ?_
          split_ifs with hab
          · rw [mul_smul_comm, Matrix.trace_smul, smul_eq_mul,
              hW_mul j hj i hi a ha b hb (C.rel_symm hij) hab, if_neg (Ne.symm hai),
              Matrix.trace_zero, mul_zero]
          · rw [mul_zero, Matrix.trace_zero]
      rw [Finset.sum_congr rfl houter, Finset.sum_ite_eq' Ret i, if_pos hi]
      have hr_ne : (C.rkr (o i) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt (C.rkr_pos (o i)))
      field_simp [hr_ne]
    · rw [if_neg hij, if_neg hij]
  -- Property 3: Operator-norm contraction `‖toEuclideanCLM (E x)‖ ≤ ‖toEuclideanCLM x‖`
  have hE_op : ∀ x, ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (E x)‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ := by
    intro x
    let Reps : Finset (Fin m) := Ret.image o
    let clsOf : Fin m → Finset (Fin m) := fun r => Ret.filter (fun i => o i = r)
    let qK : Fin m → Mat k := fun r => ∑ i ∈ clsOf r, W i i
    let GK : Fin m → Mat k := fun r =>
      ∑ i ∈ clsOf r, ∑ j ∈ clsOf r,
        ((star (W i j) * x).trace / (C.rk r : ℂ)) • W i j
    have hGK_op : ∀ r ∈ Reps, ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (GK r)‖ ≤
        ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ := fun r hr => by
      rcases Finset.mem_image.1 hr with ⟨i₀, hi₀, rfl⟩
      refine clock_shift_opNorm_le (C.he_sa (o i₀)) (C.he_sq (o i₀)) (C.he_ne (o i₀))
        (clsOf (o i₀)) U ?_ ?_ x
      · intro i hi
        have hi_ret := (Finset.mem_filter.1 hi).1
        have hi_o := (Finset.mem_filter.1 hi).2
        rw [← hi_o]
        exact (hU_prop i hi_ret).2.2.1
      · intro i hi j hj hij
        exact hU_orth i (Finset.mem_filter.1 hi).1 j (Finset.mem_filter.1 hj).1 hij
    have hG_decomp : G x = ∑ r ∈ Reps, GK r := by
      dsimp only [G, GK]
      have hpart : ∀ i ∈ Ret,
          (∑ j ∈ Ret, if C.rel i j then ((star (W i j) * x).trace / (C.rkr (o i) : ℂ)) • W i j else 0) =
          ∑ j ∈ clsOf (o i), ((star (W i j) * x).trace / (C.rk (o i) : ℂ)) • W i j := fun i hi => by
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun j hj => ?_
        · ext j
          simp only [clsOf, Finset.mem_filter]
          constructor
          · rintro ⟨hj, hij⟩; exact ⟨hj, ((ho_iff i hi j hj).1 hij).symm⟩
          · rintro ⟨hj, hoj⟩; exact ⟨hj, (ho_iff i hi j hj).2 hoj.symm⟩
        · simp [rkr]
      rw [Finset.sum_congr rfl hpart]
      have hfiber := Finset.sum_fiberwise_of_maps_to (s := Ret) (t := Reps) (g := o)
        (f := fun i => ∑ j ∈ clsOf (o i), ((star (W i j) * x).trace / (C.rk (o i) : ℂ)) • W i j)
        (fun i hi => Finset.mem_image.2 ⟨i, hi, rfl⟩)
      rw [← hfiber]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.1 hi).2]
    have hq_decomp : q = ∑ r ∈ Reps, qK r := by
      dsimp only [q, qK]
      exact (Finset.sum_fiberwise_of_maps_to (s := Ret) (t := Reps) (g := o)
        (f := fun i => W i i) (fun i hi => Finset.mem_image.2 ⟨i, hi, rfl⟩)).symm
    have hqK_sa : ∀ r, star (qK r) = qK r := fun r => by simp only [qK, star_sum, hW_star]
    have hqK_orth : ∀ r₁ ∈ Reps, ∀ r₂ ∈ Reps, r₁ ≠ r₂ → qK r₁ * qK r₂ = 0 := by
      intro r₁ _ r₂ _ hne
      dsimp only [qK]
      rw [Finset.sum_mul]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hij : i ≠ j := by
        rintro rfl
        exact hne ((Finset.mem_filter.1 hi).2.symm.trans (Finset.mem_filter.1 hj).2)
      rw [hW_mul i (Finset.mem_filter.1 hi).1 i (Finset.mem_filter.1 hi).1
        j (Finset.mem_filter.1 hj).1 j (Finset.mem_filter.1 hj).1 (C.rel_refl i) (C.rel_refl j),
        if_neg hij]
    have hGK_corner : ∀ r ∈ Reps, qK r * GK r = GK r ∧ GK r * qK r = GK r := by
      intro r _
      have hqKW : ∀ i ∈ clsOf r, ∀ j ∈ clsOf r, qK r * W i j = W i j ∧ W i j * qK r = W i j := by
        intro i hi j hj
        have hi_ret := (Finset.mem_filter.1 hi).1
        have hj_ret := (Finset.mem_filter.1 hj).1
        have hij : C.rel i j := (ho_iff i hi_ret j hj_ret).2
          ((Finset.mem_filter.1 hi).2.trans (Finset.mem_filter.1 hj).2.symm)
        constructor
        · dsimp only [qK]
          rw [Finset.sum_mul]
          have ht : ∀ l ∈ clsOf r, W l l * W i j = if l = i then W i j else 0 := fun l hl => by
            rw [hW_mul l (Finset.mem_filter.1 hl).1 l (Finset.mem_filter.1 hl).1 i hi_ret j hj_ret
              (C.rel_refl l) hij]
            by_cases hli : l = i
            · subst hli; simp
            · rw [if_neg hli, if_neg hli]
          rw [Finset.sum_congr rfl ht, Finset.sum_ite_eq' (clsOf r) i, if_pos hi]
        · dsimp only [qK]
          rw [Finset.mul_sum]
          have ht : ∀ l ∈ clsOf r, W i j * W l l = if l = j then W i j else 0 := fun l hl => by
            rw [hW_mul i hi_ret j hj_ret l (Finset.mem_filter.1 hl).1 l (Finset.mem_filter.1 hl).1
              hij (C.rel_refl l)]
            by_cases hlj : l = j
            · subst hlj; simp
            · rw [if_neg (Ne.symm hlj), if_neg hlj]
          rw [Finset.sum_congr rfl ht, Finset.sum_ite_eq' (clsOf r) j, if_pos hj]
      constructor
      · dsimp only [GK]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [mul_smul_comm, (hqKW i hi j hj).1]
      · dsimp only [GK]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [smul_mul_assoc, (hqKW i hi j hj).2]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun ξ => ?_
    have hEξ : Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (E x) ξ =
        Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (G x) ξ +
          Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) ((1 - q) * x * (1 - q)) ξ := by
      change Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (G x + (1 - q) * x * (1 - q)) ξ = _
      rw [map_add, _root_.add_apply]
    have hGξ_sq : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (G x) ξ‖ ^ 2 ≤
        ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ^ 2 *
          ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) q ξ‖ ^ 2 := by
      have hGsum : Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (G x) ξ =
          ∑ r ∈ Reps, Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (GK r) ξ := by
        rw [hG_decomp, map_sum, _root_.sum_apply]
      have hqsum : Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) q ξ =
          ∑ r ∈ Reps, Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (qK r) ξ := by
        rw [hq_decomp, map_sum, _root_.sum_apply]
      rw [hGsum, hqsum, norm_sq_sum_of_pairwise_orth Reps, norm_sq_sum_of_pairwise_orth Reps,
        Finset.mul_sum]
      · refine Finset.sum_le_sum fun r hr => ?_
        have hle : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (GK r) ξ‖ ≤
            ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ *
              ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (qK r) ξ‖ := by
          rw [← (hGK_corner r hr).2, toEuclideanCLM_mul_apply]
          exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (hGK_op r hr) (norm_nonneg _))
        calc ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (GK r) ξ‖ ^ 2
            ≤ (‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ *
                ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (qK r) ξ‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hle 2
          _ = _ := mul_pow _ _ 2
      · intro r₁ hr₁ r₂ hr₂ hne
        rw [inner_toEuclideanCLM, hqK_sa r₂, ← toEuclideanCLM_mul_apply,
          hqK_orth r₂ hr₂ r₁ hr₁ (Ne.symm hne), map_zero, _root_.zero_apply, inner_zero_left]
      · intro r₁ hr₁ r₂ hr₂ hne
        rw [← (hGK_corner r₁ hr₁).1, ← (hGK_corner r₂ hr₂).1, toEuclideanCLM_mul_apply,
          toEuclideanCLM_mul_apply, inner_toEuclideanCLM, hqK_sa r₂, ← toEuclideanCLM_mul_apply,
          hqK_orth r₂ hr₂ r₁ hr₁ (Ne.symm hne), map_zero, _root_.zero_apply, inner_zero_left]
    have h1qξ_sq : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) ((1 - q) * x * (1 - q)) ξ‖ ^ 2 ≤
        ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ^ 2 *
          ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (1 - q) ξ‖ ^ 2 := by
      have hle : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) ((1 - q) * x * (1 - q)) ξ‖ ≤
          ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ *
            ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (1 - q) ξ‖ := by
        rw [toEuclideanCLM_mul_apply, toEuclideanCLM_mul_apply]
        calc ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (1 - q)
                (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x
                  (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (1 - q) ξ))‖
            ≤ 1 * ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x
                (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (1 - q) ξ)‖ :=
              (ContinuousLinearMap.le_opNorm _ _).trans
                (mul_le_mul_of_nonneg_right (proj_opNorm_le_one h1q_sa h1q_sq) (norm_nonneg _))
          _ ≤ ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ *
                ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (1 - q) ξ‖ := by
              rw [one_mul]; exact ContinuousLinearMap.le_opNorm _ _
      calc _ ≤ (‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ *
              ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (1 - q) ξ‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hle 2
        _ = _ := mul_pow _ _ 2
    have horth_E : @inner ℂ _ _ (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (G x) ξ)
        (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) ((1 - q) * x * (1 - q)) ξ) = 0 := by
      have hqGx := (hA₀_q (G x) (hG_mem_A₀ x)).1
      rw [← hqGx, toEuclideanCLM_mul_apply, mul_assoc, toEuclideanCLM_mul_apply,
        inner_toEuclideanCLM, h1q_sa, ← toEuclideanCLM_mul_apply, h1qq, map_zero,
        _root_.zero_apply, inner_zero_left]
    have horth_q : @inner ℂ _ _ (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) q ξ)
        (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (1 - q) ξ) = 0 := by
      rw [inner_toEuclideanCLM, h1q_sa, ← toEuclideanCLM_mul_apply, h1qq, map_zero,
        _root_.zero_apply, inner_zero_left]
    have hpyth_pair : ∀ u v : Vec k, @inner ℂ _ _ u v = 0 → ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
      intro u v huv
      have hvu : @inner ℂ _ _ v u = 0 := by rw [← inner_conj_symm, huv, map_zero]
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_add_left, inner_add_right, inner_add_right,
        huv, hvu, add_zero, zero_add, map_add, inner_self_eq_norm_sq (𝕜 := ℂ) u,
        inner_self_eq_norm_sq (𝕜 := ℂ) v]
    have hq_pyth : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) q ξ‖ ^ 2 +
        ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (1 - q) ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
      have h1 : Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) q ξ +
          Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (1 - q) ξ = ξ := by
        rw [← _root_.add_apply, ← map_add, add_sub_cancel, map_one]
        rfl
      conv_rhs => rw [← h1]
      exact (hpyth_pair _ _ horth_q).symm
    have hEsq : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (E x) ξ‖ ^ 2 ≤
        (‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ * ‖ξ‖) ^ 2 := by
      rw [hEξ, hpyth_pair _ _ horth_E, mul_pow, ← hq_pyth, mul_add]
      exact add_le_add hGξ_sq h1qξ_sq
    nlinarith [norm_nonneg (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (E x) ξ),
      mul_nonneg (norm_nonneg (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x)) (norm_nonneg ξ)]
  -- Property 4: `∞ → 2` approximation `ss (F x - E x) ≤ 1849 * ρ * k`
  have hE_approx : ∀ x, ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ≤ 1 →
      ss (C.F x - E x) ≤ 1849 * C.ρ * (k : ℝ) := by
    intro x hx_op
    let p : Mat k := ∑ i ∈ Ret, C.e i
    have hp_sa : star p = p := by simp only [p, star_sum, C.he_sa]
    have hp_sq : p * p = p := by
      dsimp only [p]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mul_sum]
      have ht : ∀ j ∈ Ret, C.e i * C.e j = if j = i then C.e i else 0 := fun j _ => by
        by_cases h : j = i
        · subst h; rw [if_pos rfl, C.he_sq j]
        · rw [if_neg h, C.he_orth i j (Ne.symm h)]
      rw [Finset.sum_congr rfl ht, Finset.sum_ite_eq' Ret i, if_pos hi]
    have h1p_eq : 1 - p = ∑ i ∈ Finset.univ \ Ret, C.e i := by
      have hsum : ∑ i ∈ Finset.univ \ Ret, C.e i + ∑ i ∈ Ret, C.e i = 1 := by
        rw [Finset.sum_sdiff (Finset.subset_univ Ret), C.he_sum]
      dsimp only [p]
      exact (eq_sub_of_add_eq hsum).symm
    have h1p_ss : ss (1 - p) ≤ 256 * C.ρ ^ 4 * (k : ℝ) := by
      have h1p_sa : star (1 - p) = 1 - p := by rw [star_sub, star_one, hp_sa]
      have h1p_sq : (1 - p) * (1 - p) = 1 - p := by
        calc (1 - p) * (1 - p) = 1 - p - p + p * p := by noncomm_ring
          _ = 1 - p := by rw [hp_sq]; abel
      rw [proj_ss_eq_re_trace h1p_sa h1p_sq, h1p_eq, Matrix.trace_sum, Complex.re_sum]
      simp_rw [C.e_re_trace]
      exact hBad_sum
    have h1q_ss : ss (1 - q) ≤ 4 * C.ρ * (k : ℝ) := by
      rw [proj_ss_eq_re_trace h1q_sa h1q_sq, Matrix.trace_sub, Complex.sub_re]
      have h1tr : ((1 : Mat k).trace).re = (k : ℝ) := by simp [Matrix.trace]
      have hqtr : (q.trace).re = ∑ i ∈ Ret, C.rkr (o i) := by
        dsimp only [q]
        rw [Matrix.trace_sum, Complex.re_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have h1 : (W i i).trace = (star (W i i) * W i i).trace := by
          rw [hW_star, hW_mul i hi i hi i hi i hi (C.rel_refl i) (C.rel_refl i), if_pos rfl]
        rw [h1, re_trace_star_mul_self]
        exact (hW_prop i hi i hi (C.rel_refl i)).2.1
      rw [h1tr, hqtr, ← C.sum_rkr]
      have hsplit_sum : ∑ i : Fin m, C.rkr i =
          (∑ i ∈ Ret, C.rkr i) + ∑ i ∈ Finset.univ \ Ret, C.rkr i := by
        rw [add_comm, Finset.sum_sdiff (Finset.subset_univ Ret)]
      have hdiff_Ret : ∑ i ∈ Ret, C.rkr i - ∑ i ∈ Ret, C.rkr (o i) ≤ 3 * C.ρ * (k : ℝ) := by
        rw [← Finset.sum_sub_distrib]
        calc ∑ i ∈ Ret, (C.rkr i - C.rkr (o i))
            ≤ ∑ i ∈ Ret, 3 * C.ρ * C.rkr i := by
              refine Finset.sum_le_sum fun i hi => ?_
              linarith only [hrat_all i hi]
          _ = 3 * C.ρ * ∑ i ∈ Ret, C.rkr i := (Finset.mul_sum _ _ _).symm
          _ ≤ 3 * C.ρ * ∑ i : Fin m, C.rkr i :=
              mul_le_mul_of_nonneg_left
                (Finset.sum_le_univ_sum_of_nonneg fun i => le_of_lt (C.rkr_pos i))
                (by linarith only [C.hρ_pos])
          _ = 3 * C.ρ * (k : ℝ) := by rw [C.sum_rkr]
      have h256 : 256 * C.ρ ^ 4 * (k : ℝ) ≤ C.ρ * (k : ℝ) := by
        have h3 : 256 * C.ρ ^ 3 ≤ 1 := by
          have hle := C.hρ_small; have hpos := C.hρ_pos
          have h2 : C.ρ ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ (le_of_lt hpos) hle 2
          nlinarith only [hpos, hle, h2]
        calc 256 * C.ρ ^ 4 * (k : ℝ) = (256 * C.ρ ^ 3) * (C.ρ * (k : ℝ)) := by ring
          _ ≤ 1 * (C.ρ * (k : ℝ)) :=
              mul_le_mul_of_nonneg_right h3 (mul_nonneg (le_of_lt C.hρ_pos) (Nat.cast_nonneg k))
          _ = C.ρ * (k : ℝ) := one_mul _
      rw [C.sum_rkr]
      linarith only [hsplit_sum, hdiff_Ret, hBad_sum, h256, C.sum_rkr]
    -- Term 1: `F (p * x * p) - G x`
    have hpxp : p * x * p = ∑ a ∈ Ret ×ˢ Ret, C.e a.1 * x * C.e a.2 := by
      rw [Finset.sum_product]
      dsimp only [p]
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    have hG_prod : G x = ∑ a ∈ Ret ×ˢ Ret,
        if C.rel a.1 a.2 then ((star (W a.1 a.2) * (C.e a.1 * x * C.e a.2)).trace /
          (C.rkr (o a.1) : ℂ)) • W a.1 a.2 else 0 := by
      rw [Finset.sum_product]
      dsimp only [G]
      refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
      by_cases hij : C.rel i j
      · rw [if_pos hij, if_pos hij]
        congr 2
        have hWb : C.e i * W i j * C.e j = W i j := (hW_prop i hi j hj hij).1
        have hWs : star (W i j) = C.e j * star (W i j) * C.e i := by
          conv_lhs => rw [← hWb]
          rw [star_mul, star_mul, C.he_sa i, C.he_sa j, mul_assoc]
        calc (star (W i j) * x).trace = ((C.e j * star (W i j) * C.e i) * x).trace := by rw [← hWs]
          _ = (C.e j * (star (W i j) * C.e i * x)).trace := by simp only [mul_assoc]
          _ = (star (W i j) * C.e i * x * C.e j).trace := Matrix.trace_mul_comm _ _
          _ = (star (W i j) * (C.e i * x * C.e j)).trace := by simp only [mul_assoc]
      · rw [if_neg hij, if_neg hij]
    have hTerm1 : Real.sqrt (ss (C.F (p * x * p) - G x)) ≤ 40 * Real.sqrt C.ρ * Real.sqrt (k : ℝ) := by
      have hdiff_sum : C.F (p * x * p) - G x = ∑ a ∈ Ret ×ˢ Ret,
          (C.F (C.e a.1 * x * C.e a.2) -
            if C.rel a.1 a.2 then ((star (W a.1 a.2) * (C.e a.1 * x * C.e a.2)).trace /
              (C.rkr (o a.1) : ℂ)) • W a.1 a.2 else 0) := by
        rw [hpxp, C.F_sum, hG_prod, ← Finset.sum_sub_distrib]
      have hss_eq : ss (C.F (p * x * p) - G x) = ∑ a ∈ Ret ×ˢ Ret,
          ss (C.F (C.e a.1 * x * C.e a.2) -
            if C.rel a.1 a.2 then ((star (W a.1 a.2) * (C.e a.1 * x * C.e a.2)).trace /
              (C.rkr (o a.1) : ℂ)) • W a.1 a.2 else 0) := by
        rw [hdiff_sum]
        refine C.ss_sum_blocks _ fun a ha => ?_
        rcases Finset.mem_product.1 ha with ⟨ha1, ha2⟩
        rw [mul_sub, sub_mul, ← C.F_block]
        have hblock_x : C.e a.1 * (C.e a.1 * x * C.e a.2) * C.e a.2 = C.e a.1 * x * C.e a.2 := by
          calc C.e a.1 * (C.e a.1 * x * C.e a.2) * C.e a.2
              = (C.e a.1 * C.e a.1) * x * (C.e a.2 * C.e a.2) := by simp only [mul_assoc]
            _ = C.e a.1 * x * C.e a.2 := by rw [C.he_sq a.1, C.he_sq a.2]
        rw [hblock_x]
        congr 1
        split_ifs with hrel
        · rw [mul_smul_comm, smul_mul_assoc, (hW_prop a.1 ha1 a.2 ha2 hrel).1]
        · rw [mul_zero, zero_mul]
      have hss_le : ss (C.F (p * x * p) - G x) ≤ 1600 * C.ρ * (k : ℝ) := by
        rw [hss_eq]
        calc ∑ a ∈ Ret ×ˢ Ret,
              ss (C.F (C.e a.1 * x * C.e a.2) -
                if C.rel a.1 a.2 then ((star (W a.1 a.2) * (C.e a.1 * x * C.e a.2)).trace /
                  (C.rkr (o a.1) : ℂ)) • W a.1 a.2 else 0)
            ≤ ∑ a ∈ Ret ×ˢ Ret, 1600 * C.ρ * ss (C.e a.1 * x * C.e a.2) := by
              refine Finset.sum_le_sum fun a ha => ?_
              rcases Finset.mem_product.1 ha with ⟨ha1, ha2⟩
              have hblock_x : C.e a.1 * (C.e a.1 * x * C.e a.2) * C.e a.2 = C.e a.1 * x * C.e a.2 := by
                calc C.e a.1 * (C.e a.1 * x * C.e a.2) * C.e a.2
                    = (C.e a.1 * C.e a.1) * x * (C.e a.2 * C.e a.2) := by simp only [mul_assoc]
                  _ = C.e a.1 * x * C.e a.2 := by rw [C.he_sq a.1, C.he_sq a.2]
              have hbd := C.block_approx_bound (hRet_nobad a.1 ha1 a.2 ha2) (C.rkr_pos (o a.1))
                (hW_prop a.1 ha1 a.2 ha2) hblock_x
              calc ss _ = (Real.sqrt (ss _)) ^ 2 := (Real.sq_sqrt (ss_nonneg _)).symm
                _ ≤ (40 * Real.sqrt C.ρ * Real.sqrt (ss (C.e a.1 * x * C.e a.2))) ^ 2 :=
                    pow_le_pow_left₀ (Real.sqrt_nonneg _) hbd 2
                _ = 1600 * (Real.sqrt C.ρ) ^ 2 * (Real.sqrt (ss (C.e a.1 * x * C.e a.2))) ^ 2 := by ring
                _ = 1600 * C.ρ * ss (C.e a.1 * x * C.e a.2) := by
                    rw [Real.sq_sqrt (le_of_lt C.hρ_pos), Real.sq_sqrt (ss_nonneg _)]
          _ = 1600 * C.ρ * ∑ a ∈ Ret ×ˢ Ret, ss (C.e a.1 * x * C.e a.2) := (Finset.mul_sum _ _ _).symm
          _ = 1600 * C.ρ * ss (p * x * p) := by
              rw [hpxp, C.ss_sum_blocks]
              intro a _
              calc C.e a.1 * (C.e a.1 * x * C.e a.2) * C.e a.2
                  = (C.e a.1 * C.e a.1) * x * (C.e a.2 * C.e a.2) := by simp only [mul_assoc]
                _ = C.e a.1 * x * C.e a.2 := by rw [C.he_sq a.1, C.he_sq a.2]
          _ ≤ 1600 * C.ρ * (k : ℝ) := by
              have hpxp_ss : ss (p * x * p) ≤ (k : ℝ) := by
                have hp_op2 : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) p‖ ^ 2 ≤ 1 := by
                  have h := proj_opNorm_le_one hp_sa hp_sq
                  nlinarith only [h, norm_nonneg (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) p)]
                have hx_ss : ss x ≤ (k : ℝ) := by
                  have hx2 : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ^ 2 ≤ 1 := by
                    nlinarith only [hx_op, norm_nonneg (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x)]
                  calc ss x ≤ (k : ℝ) * ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ^ 2 :=
                        ss_le_card_mul_opNorm_sq x
                    _ ≤ (k : ℝ) * 1 := mul_le_mul_of_nonneg_left hx2 (Nat.cast_nonneg k)
                    _ = (k : ℝ) := mul_one _
                calc ss (p * x * p) ≤ ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) p‖ ^ 2 * ss (p * x) :=
                      ss_mul_right_le (p * x) p
                  _ ≤ 1 * ss (p * x) := mul_le_mul_of_nonneg_right hp_op2 (ss_nonneg _)
                  _ = ss (p * x) := one_mul _
                  _ ≤ ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) p‖ ^ 2 * ss x := ss_mul_left_le p x
                  _ ≤ 1 * (k : ℝ) := mul_le_mul hp_op2 hx_ss (ss_nonneg x) zero_le_one
                  _ = (k : ℝ) := one_mul _
              exact mul_le_mul_of_nonneg_left hpxp_ss (by linarith only [C.hρ_pos])
      calc Real.sqrt (ss (C.F (p * x * p) - G x))
          ≤ Real.sqrt (1600 * C.ρ * (k : ℝ)) := Real.sqrt_le_sqrt hss_le
        _ = Real.sqrt 1600 * Real.sqrt C.ρ * Real.sqrt (k : ℝ) := by
            rw [Real.sqrt_mul (mul_nonneg (by norm_num) (le_of_lt C.hρ_pos)),
              Real.sqrt_mul (by norm_num)]
        _ = 40 * Real.sqrt C.ρ * Real.sqrt (k : ℝ) := by
            rw [show Real.sqrt 1600 = 40 by
              rw [show (1600 : ℝ) = 40 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    -- Term 2: `F (x - p * x * p)`
    have hx_op2 : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ^ 2 ≤ 1 := by
      nlinarith only [hx_op, norm_nonneg (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x)]
    have hTerm2 : Real.sqrt (ss (C.F (x - p * x * p))) ≤ Real.sqrt C.ρ * Real.sqrt (k : ℝ) := by
      have hdecomp : x - p * x * p = (1 - p) * x + p * x * (1 - p) := by noncomm_ring
      have h1 : ss ((1 - p) * x) ≤ 256 * C.ρ ^ 4 * (k : ℝ) := by
        calc ss ((1 - p) * x) ≤ ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ^ 2 * ss (1 - p) :=
              ss_mul_right_le (1 - p) x
          _ ≤ 1 * ss (1 - p) := mul_le_mul_of_nonneg_right hx_op2 (ss_nonneg _)
          _ = ss (1 - p) := one_mul _
          _ ≤ 256 * C.ρ ^ 4 * (k : ℝ) := h1p_ss
      have h2 : ss (p * x * (1 - p)) ≤ 256 * C.ρ ^ 4 * (k : ℝ) := by
        have hp2 : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) p‖ ^ 2 ≤ 1 := by
          have h := proj_opNorm_le_one hp_sa hp_sq
          nlinarith only [h, norm_nonneg (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) p)]
        calc ss (p * x * (1 - p)) = ss (p * (x * (1 - p))) := by rw [mul_assoc]
          _ ≤ ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) p‖ ^ 2 * ss (x * (1 - p)) :=
              ss_mul_left_le p (x * (1 - p))
          _ ≤ 1 * ss (x * (1 - p)) := mul_le_mul_of_nonneg_right hp2 (ss_nonneg _)
          _ = ss (x * (1 - p)) := one_mul _
          _ ≤ ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ^ 2 * ss (1 - p) :=
              ss_mul_left_le x (1 - p)
          _ ≤ 1 * ss (1 - p) := mul_le_mul_of_nonneg_right hx_op2 (ss_nonneg _)
          _ = ss (1 - p) := one_mul _
          _ ≤ 256 * C.ρ ^ 4 * (k : ℝ) := h1p_ss
      have hsq16 : Real.sqrt (256 * C.ρ ^ 4 * (k : ℝ)) = 16 * C.ρ ^ 2 * Real.sqrt (k : ℝ) := by
        rw [Real.sqrt_mul (mul_nonneg (by norm_num) (pow_nonneg (le_of_lt C.hρ_pos) 4)),
          Real.sqrt_mul (by norm_num),
          show Real.sqrt 256 = 16 by
            rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
          show C.ρ ^ 4 = (C.ρ ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg C.ρ)]
      have h32 : 32 * C.ρ ^ 2 ≤ Real.sqrt C.ρ := by
        have h1 : (32 * C.ρ ^ 2) ^ 2 ≤ C.ρ := by
          have hle := C.hρ_small; have hpos := C.hρ_pos
          have h2 : C.ρ ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ (le_of_lt hpos) hle 2
          have h3 : C.ρ ^ 3 ≤ (1 / 10000 : ℝ) ^ 3 := pow_le_pow_left₀ (le_of_lt hpos) hle 3
          have h4 : (32 * C.ρ ^ 2) ^ 2 = 1024 * C.ρ ^ 3 * C.ρ := by ring
          nlinarith only [hpos, h3, h4]
        calc 32 * C.ρ ^ 2 = Real.sqrt ((32 * C.ρ ^ 2) ^ 2) :=
              (Real.sqrt_sq (by positivity)).symm
          _ ≤ Real.sqrt C.ρ := Real.sqrt_le_sqrt h1
      calc Real.sqrt (ss (C.F (x - p * x * p)))
          ≤ Real.sqrt (ss (x - p * x * p)) := Real.sqrt_le_sqrt (C.F_ss_le _)
        _ = Real.sqrt (ss ((1 - p) * x + p * x * (1 - p))) := by rw [hdecomp]
        _ ≤ Real.sqrt (ss ((1 - p) * x)) + Real.sqrt (ss (p * x * (1 - p))) :=
            sqrt_ss_add_le' _ _
        _ ≤ 16 * C.ρ ^ 2 * Real.sqrt (k : ℝ) + 16 * C.ρ ^ 2 * Real.sqrt (k : ℝ) := by
            rw [← hsq16]; exact add_le_add (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2)
        _ = (32 * C.ρ ^ 2) * Real.sqrt (k : ℝ) := by ring
        _ ≤ Real.sqrt C.ρ * Real.sqrt (k : ℝ) := mul_le_mul_of_nonneg_right h32 (Real.sqrt_nonneg _)
    -- Term 3: `-((1 - q) * x * (1 - q))`
    have hTerm3 : Real.sqrt (ss (-((1 - q) * x * (1 - q)))) ≤ 2 * Real.sqrt C.ρ * Real.sqrt (k : ℝ) := by
      rw [ss_neg_eq]
      have h1q2 : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (1 - q)‖ ^ 2 ≤ 1 := by
        have h := proj_opNorm_le_one h1q_sa h1q_sq
        nlinarith only [h, norm_nonneg (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (1 - q))]
      have hle : ss ((1 - q) * x * (1 - q)) ≤ 4 * C.ρ * (k : ℝ) := by
        calc ss ((1 - q) * x * (1 - q)) = ss ((1 - q) * (x * (1 - q))) := by rw [mul_assoc]
          _ ≤ ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (1 - q)‖ ^ 2 * ss (x * (1 - q)) :=
              ss_mul_left_le (1 - q) (x * (1 - q))
          _ ≤ 1 * ss (x * (1 - q)) := mul_le_mul_of_nonneg_right h1q2 (ss_nonneg _)
          _ = ss (x * (1 - q)) := one_mul _
          _ ≤ ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ^ 2 * ss (1 - q) :=
              ss_mul_left_le x (1 - q)
          _ ≤ 1 * ss (1 - q) := mul_le_mul_of_nonneg_right hx_op2 (ss_nonneg _)
          _ = ss (1 - q) := one_mul _
          _ ≤ 4 * C.ρ * (k : ℝ) := h1q_ss
      calc Real.sqrt (ss ((1 - q) * x * (1 - q)))
          ≤ Real.sqrt (4 * C.ρ * (k : ℝ)) := Real.sqrt_le_sqrt hle
        _ = Real.sqrt 4 * Real.sqrt C.ρ * Real.sqrt (k : ℝ) := by
            rw [Real.sqrt_mul (mul_nonneg (by norm_num) (le_of_lt C.hρ_pos)),
              Real.sqrt_mul (by norm_num)]
        _ = 2 * Real.sqrt C.ρ * Real.sqrt (k : ℝ) := by
            rw [show Real.sqrt 4 = 2 by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    -- Combine all three terms
    have hsplit : C.F x - E x =
        (C.F (p * x * p) - G x) + (C.F (x - p * x * p) + -((1 - q) * x * (1 - q))) := by
      change C.F x - (G x + (1 - q) * x * (1 - q)) = _
      have hFx : C.F x = C.F (p * x * p) + C.F (x - p * x * p) := by
        rw [← C.F_add, add_sub_cancel]
      rw [hFx]; abel
    have htot : Real.sqrt (ss (C.F x - E x)) ≤ 43 * Real.sqrt C.ρ * Real.sqrt (k : ℝ) := by
      have htri1 := sqrt_ss_add_le' (C.F (p * x * p) - G x)
        (C.F (x - p * x * p) + -((1 - q) * x * (1 - q)))
      have htri2 := sqrt_ss_add_le' (C.F (x - p * x * p)) (-((1 - q) * x * (1 - q)))
      rw [← hsplit] at htri1
      linarith only [htri1, htri2, hTerm1, hTerm2, hTerm3]
    calc ss (C.F x - E x) = (Real.sqrt (ss (C.F x - E x))) ^ 2 := (Real.sq_sqrt (ss_nonneg _)).symm
      _ ≤ (43 * Real.sqrt C.ρ * Real.sqrt (k : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) htot 2
      _ = 1849 * (Real.sqrt C.ρ) ^ 2 * (Real.sqrt (k : ℝ)) ^ 2 := by ring
      _ = 1849 * C.ρ * (k : ℝ) := by
          rw [Real.sq_sqrt (le_of_lt C.hρ_pos), Real.sq_sqrt (Nat.cast_nonneg k)]
  exact ⟨A, E, hE_mem, hE_fix, hE_op, hE_approx⟩

end ChannelCtx

end OMA.H3R1H2Proof

/- ### Section 5: Ultrafilter assembly and final proof of `OMA.solution` -/

open Filter
open scoped Topology
open OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1
open OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1_H3_R1
open OMA.H3R1H2Proof

theorem OMA.solution : OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1_H3_R1.H2 := by
  classical
  intro d hd m e he_proj he_orth he_sum L w V hw hw_sum hV_comm q B F hF_sa hF_pos hδ hσ
  rcases hδ with ⟨δ, hδ_tend, hδ_le⟩
  rcases hσ with ⟨σ, hσ_tend, hσ_le⟩
  let δ₀ : ℕ → ℝ := fun n => max 0 (δ n)
  let σ₀ : ℕ → ℝ := fun n => max 0 (σ n)
  let ρ : ℕ → ℝ := fun n =>
    Real.sqrt (Real.sqrt (Real.sqrt (δ₀ n) + Real.sqrt (σ₀ n) + 1 / ((n : ℝ) + 1)))
  have hρ_pos : ∀ n, 0 < ρ n := fun n => by
    refine Real.sqrt_pos.2 (Real.sqrt_pos.2 ?_)
    have h1 : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith [Real.sqrt_nonneg (δ₀ n), Real.sqrt_nonneg (σ₀ n)]
  have hρ_tend : Tendsto ρ (hyperfilter ℕ) (𝓝 0) := by
    have hδ₀ : Tendsto δ₀ (hyperfilter ℕ) (𝓝 0) := by
      have h := (tendsto_const_nhds (x := (0 : ℝ))).max hδ_tend
      simpa [δ₀] using h
    have hσ₀ : Tendsto σ₀ (hyperfilter ℕ) (𝓝 0) := by
      have h := (tendsto_const_nhds (x := (0 : ℝ))).max hσ_tend
      simpa [σ₀] using h
    have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) (hyperfilter ℕ) (𝓝 0) := by
      have hat : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact hat.mono_left hyperfilter_le_atTop
    have hsum : Tendsto (fun n => Real.sqrt (δ₀ n) + Real.sqrt (σ₀ n) + 1 / ((n : ℝ) + 1))
        (hyperfilter ℕ) (𝓝 0) := by
      have h1 : Tendsto (fun n => Real.sqrt (δ₀ n)) (hyperfilter ℕ) (𝓝 0) := by
        simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hδ₀
      have h2 : Tendsto (fun n => Real.sqrt (σ₀ n)) (hyperfilter ℕ) (𝓝 0) := by
        simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hσ₀
      simpa using (h1.add h2).add hinv
    have hsq1 : Tendsto (fun n => Real.sqrt (Real.sqrt (δ₀ n) + Real.sqrt (σ₀ n) +
        1 / ((n : ℝ) + 1))) (hyperfilter ℕ) (𝓝 0) := by
      simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hsum
    simpa [ρ, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hsq1
  have hδ₀_le_ρ8 : ∀ n, δ₀ n ≤ (ρ n) ^ 8 := fun n => by
    have harg_nn : 0 ≤ Real.sqrt (δ₀ n) + Real.sqrt (σ₀ n) + 1 / ((n : ℝ) + 1) := by
      have h1 : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
      linarith [Real.sqrt_nonneg (δ₀ n), Real.sqrt_nonneg (σ₀ n)]
    have hρ4 : (ρ n) ^ 4 = Real.sqrt (δ₀ n) + Real.sqrt (σ₀ n) + 1 / ((n : ℝ) + 1) := by
      calc (ρ n) ^ 4 = ((ρ n) ^ 2) ^ 2 := by ring
        _ = (Real.sqrt (Real.sqrt (δ₀ n) + Real.sqrt (σ₀ n) + 1 / ((n : ℝ) + 1))) ^ 2 := by
            rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
        _ = _ := Real.sq_sqrt harg_nn
    have hsq_le : Real.sqrt (δ₀ n) ≤ (ρ n) ^ 4 := by
      rw [hρ4]
      have h1 : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
      linarith [Real.sqrt_nonneg (σ₀ n)]
    calc δ₀ n = (Real.sqrt (δ₀ n)) ^ 2 := (Real.sq_sqrt (le_max_left 0 (δ n))).symm
      _ ≤ ((ρ n) ^ 4) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq_le 2
      _ = (ρ n) ^ 8 := by ring
  have hσ₀_le_ρ8 : ∀ n, σ₀ n ≤ (ρ n) ^ 8 := fun n => by
    have harg_nn : 0 ≤ Real.sqrt (δ₀ n) + Real.sqrt (σ₀ n) + 1 / ((n : ℝ) + 1) := by
      have h1 : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
      linarith [Real.sqrt_nonneg (δ₀ n), Real.sqrt_nonneg (σ₀ n)]
    have hρ4 : (ρ n) ^ 4 = Real.sqrt (δ₀ n) + Real.sqrt (σ₀ n) + 1 / ((n : ℝ) + 1) := by
      calc (ρ n) ^ 4 = ((ρ n) ^ 2) ^ 2 := by ring
        _ = (Real.sqrt (Real.sqrt (δ₀ n) + Real.sqrt (σ₀ n) + 1 / ((n : ℝ) + 1))) ^ 2 := by
            rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
        _ = _ := Real.sq_sqrt harg_nn
    have hsq_le : Real.sqrt (σ₀ n) ≤ (ρ n) ^ 4 := by
      rw [hρ4]
      have h1 : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
      linarith [Real.sqrt_nonneg (δ₀ n)]
    calc σ₀ n = (Real.sqrt (σ₀ n)) ^ 2 := (Real.sq_sqrt (le_max_left 0 (σ n))).symm
      _ ≤ ((ρ n) ^ 4) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq_le 2
      _ = (ρ n) ^ 8 := by ring
  -- Build `(A n, E n)` coordinatewise
  have hcoord : ∀ n, ∃ (An : StarSubalgebra ℂ (Mat (d n))) (En : Mat (d n) →ₗ[ℂ] Mat (d n)),
      (∀ x, En x ∈ An) ∧
      (∀ x ∈ An, En x = x) ∧
      (∀ x, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (En x)‖ ≤
        ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) x‖) ∧
      (ρ n ≤ 1 / 10000 → ∀ x, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) x‖ ≤ 1 →
        q n (F n x - En x) ≤ 1849 * ρ n) := by
    intro n
    by_cases hsm : ρ n ≤ 1 / 10000
    · let ctx : ChannelCtx (d n) (m n) (L n) :=
        { hk := hd n
          e := e n
          he_sa := fun i => (he_proj n i).1
          he_sq := fun i => (he_proj n i).2.1
          he_ne := fun i => (he_proj n i).2.2
          he_orth := he_orth n
          he_sum := he_sum n
          w := w n
          V := V n
          hw := hw n
          hw_sum := hw_sum n
          hV_comm := hV_comm n
          hF_sa := hF_sa n
          hF_pos := hF_pos n
          δ₀ := δ₀ n
          σ₀ := σ₀ n
          ρ := ρ n
          hδ₀_nn := le_max_left _ _
          hσ₀_nn := le_max_left _ _
          hρ_pos := hρ_pos n
          hρ_small := hsm
          hδ₀_le := hδ₀_le_ρ8 n
          hσ₀_le := hσ₀_le_ρ8 n
          hδ_bound := fun x hx => by
            have h1 := hδ_le n x hx
            have hd_pos : (0 : ℝ) < (d n : ℝ) := Nat.cast_pos.2 (hd n)
            have h2 : ss (F n (F n x) - F n x) / (d n : ℝ) ≤ δ₀ n := h1.trans (le_max_right 0 _)
            exact (div_le_iff₀ hd_pos).1 h2
          hσ_bound := fun i x hx => by
            have h1 := hσ_le n i x hx
            have hd_pos : (0 : ℝ) < (d n : ℝ) := Nat.cast_pos.2 (hd n)
            have h2 : ss (F n x - (x.trace / (e n i).trace) • e n i) / (d n : ℝ) ≤
                σ₀ n * (ss x / (d n : ℝ)) :=
              h1.trans (mul_le_mul_of_nonneg_right (le_max_right 0 _)
                (div_nonneg (ss_nonneg x) (le_of_lt hd_pos)))
            rw [mul_div_assoc', div_le_div_iff_of_pos_right hd_pos] at h2
            exact h2 }
      obtain ⟨An, En, hmem, hfix, hop, happrox⟩ := ctx.coord_rounding
      refine ⟨An, En, hmem, hfix, hop, fun _ x hx => ?_⟩
      have hd_pos : (0 : ℝ) < (d n : ℝ) := Nat.cast_pos.2 (hd n)
      exact (div_le_iff₀ hd_pos).2 (happrox x hx)
    · refine ⟨⊤, LinearMap.id, fun _ => trivial, fun _ _ => rfl, fun _ => le_rfl,
        fun h => absurd h hsm⟩
  let A : (n : ℕ) → StarSubalgebra ℂ (Mat (d n)) := fun n => Classical.choose (hcoord n)
  let E : (n : ℕ) → Mat (d n) →ₗ[ℂ] Mat (d n) := fun n => Classical.choose (Classical.choose_spec (hcoord n))
  have hE_mem : ∀ n x, E n x ∈ A n := fun n => (Classical.choose_spec (Classical.choose_spec (hcoord n))).1
  have hE_fix : ∀ n x, x ∈ A n → E n x = x := fun n => (Classical.choose_spec (Classical.choose_spec (hcoord n))).2.1
  have hE_op : ∀ n x, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (E n x)‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) x‖ :=
    fun n => (Classical.choose_spec (Classical.choose_spec (hcoord n))).2.2.1
  have hE_approx : ∀ n, ρ n ≤ 1 / 10000 → ∀ x,
      ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) x‖ ≤ 1 →
      q n (F n x - E n x) ≤ 1849 * ρ n :=
    fun n => (Classical.choose_spec (Classical.choose_spec (hcoord n))).2.2.2
  -- Key consequence: for every bounded sequence `z`, `q n (F n (z n) - E n (z n)) →_ω 0`
  have hFE_zero : ∀ z, B z → Tendsto (fun n => q n (F n (z n) - E n (z n))) (hyperfilter ℕ) (𝓝 0) := by
    rintro z ⟨C₀, hC₀⟩
    let C₁ : ℝ := max 1 C₀
    have hC₁_pos : 0 < C₁ := lt_of_lt_of_le zero_lt_one (le_max_left 1 C₀)
    have hgood : ∀ᶠ n in hyperfilter ℕ, ρ n ≤ 1 / 10000 :=
      hρ_tend.eventually (Iic_mem_nhds (by norm_num))
    have hbound : ∀ᶠ n in hyperfilter ℕ,
        q n (F n (z n) - E n (z n)) ≤ C₁ ^ 2 * (1849 * ρ n) := by
      filter_upwards [hgood] with n hn
      let zn : Mat (d n) := ((C₁⁻¹ : ℝ) : ℂ) • z n
      have hzn_op : ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) zn‖ ≤ 1 := by
        rw [show zn = ((C₁⁻¹ : ℝ) : ℂ) • z n from rfl, map_smul, norm_smul, Complex.norm_real,
          Real.norm_of_nonneg (inv_nonneg.2 (le_of_lt hC₁_pos))]
        calc C₁⁻¹ * ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (z n)‖
            ≤ C₁⁻¹ * C₁ := mul_le_mul_of_nonneg_left ((hC₀ n).trans (le_max_right 1 C₀))
              (inv_nonneg.2 (le_of_lt hC₁_pos))
          _ = 1 := inv_mul_cancel₀ (ne_of_gt hC₁_pos)
      have hlin : F n (z n) - E n (z n) = (C₁ : ℂ) • (F n zn - E n zn) := by
        have hF_lin : F n zn = ((C₁⁻¹ : ℝ) : ℂ) • F n (z n) := by
          simp only [F, zn, Finset.smul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [mul_smul_comm, smul_mul_assoc, smul_comm]
        have hE_lin : E n zn = ((C₁⁻¹ : ℝ) : ℂ) • E n (z n) := map_smul (E n) _ _
        rw [hF_lin, hE_lin, ← smul_sub, smul_smul, ← Complex.ofReal_mul,
          mul_inv_cancel₀ (ne_of_gt hC₁_pos), Complex.ofReal_one, one_smul]
      have hq_sc : q n (F n (z n) - E n (z n)) = C₁ ^ 2 * q n (F n zn - E n zn) := by
        rw [hlin]
        change ss ((C₁ : ℂ) • (F n zn - E n zn)) / (d n : ℝ) =
          C₁ ^ 2 * (ss (F n zn - E n zn) / (d n : ℝ))
        rw [ss_smul', Complex.norm_real, Real.norm_of_nonneg (le_of_lt hC₁_pos), mul_div_assoc]
      rw [hq_sc]
      exact mul_le_mul_of_nonneg_left (hE_approx n hn zn hzn_op) (sq_nonneg C₁)
    refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg (ss_nonneg _) (Nat.cast_nonneg _))
      hbound ?_
    have h0 : Tendsto (fun n => C₁ ^ 2 * (1849 * ρ n)) (hyperfilter ℕ) (𝓝 (C₁ ^ 2 * (1849 * 0))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.mul hρ_tend)
    simpa using h0
  refine ⟨A, fun y hy => ⟨?_, ?_⟩⟩
  · intro hFy
    refine ⟨fun n => E n (y n), ?_, fun n => hE_mem n (y n), ?_⟩
    · rcases hy with ⟨C₀, hC₀⟩
      exact ⟨C₀, fun n => (hE_op n (y n)).trans (hC₀ n)⟩
    · have hadd := tendsto_q_add hFy (hFE_zero y hy)
      have heq : ∀ n, (y n - F n (y n)) + (F n (y n) - E n (y n)) = y n - E n (y n) := fun n => by
        abel
      simpa only [heq] using hadd
  · rintro ⟨a, haB, haA, hya⟩
    have hFa_zero : Tendsto (fun n => q n (F n (a n) - a n)) (hyperfilter ℕ) (𝓝 0) := by
      have heq : ∀ n, F n (a n) - E n (a n) = F n (a n) - a n := fun n => by
        rw [hE_fix n (a n) (haA n)]
      simpa only [heq] using hFE_zero a haB
    have hFya_zero : Tendsto (fun n => q n (F n (y n) - F n (a n))) (hyperfilter ℕ) (𝓝 0) := by
      refine squeeze_zero (fun n => div_nonneg (ss_nonneg _) (Nat.cast_nonneg _)) (fun n => ?_) hya
      have hFsub : F n (y n) - F n (a n) = F n (y n - a n) := by
        simp only [F, mul_sub, sub_mul, smul_sub, Finset.sum_sub_distrib]
      rw [hFsub]
      exact div_le_div_of_nonneg_right (unitary_mix_ss_le (w n) (V n) (hw n) (hw_sum n) _)
        (Nat.cast_nonneg _)
    have h1 := tendsto_q_sub hya hFa_zero
    have h2 := tendsto_q_sub h1 hFya_zero
    have heq : ∀ n, (y n - a n - (F n (a n) - a n)) - (F n (y n) - F n (a n)) = y n - F n (y n) :=
      fun n => by abel
    simpa only [heq] using h2

