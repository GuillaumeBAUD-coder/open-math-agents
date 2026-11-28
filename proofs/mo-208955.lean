import OMAStatements.S_mo_208955

open Matrix Finset WithLp
open scoped BigOperators Matrix.Norms.L2Operator OMA.S_mo_208955

namespace OMA.P_mo_208955

private lemma sum_sub_right {n : ℕ} [NeZero n] (a : Fin n → ℝ) (i : Fin n) :
    ∑ j : Fin n, a (j - i) = ∑ j : Fin n, a j :=
  Equiv.sum_comp (Equiv.subRight i) a

private lemma sum_sub_left {n : ℕ} [NeZero n] (a : Fin n → ℝ) (j : Fin n) :
    ∑ i : Fin n, a (j - i) = ∑ i : Fin n, a i :=
  Equiv.sum_comp (Equiv.subLeft j) a

end OMA.P_mo_208955

open OMA.P_mo_208955 OMA.S_mo_208955 in
theorem OMA.solution : type_of% @OMA.S_mo_208955.main := by
  intro n hn a ha
  haveI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  set S : ℝ := ∑ j : Fin n, a j
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun j _ => ha j
  set A : Matrix (Fin n) (Fin n) ℂ := RowCirculant a
  set T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A
  rw [← l2_opNorm_toEuclideanCLM A]
  apply le_antisymm
  · -- Upper bound: ‖T‖ ≤ S via Cauchy-Schwarz (Schur's test)
    refine ContinuousLinearMap.opNorm_le_bound T hS_nn fun x => ?_
    have hsq : ‖T x‖ ^ 2 ≤ (S * ‖x‖) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq (T x), mul_pow, EuclideanSpace.norm_sq_eq x]
      have hrow : ∀ i : Fin n,
          ‖(T x).ofLp i‖ ^ 2 ≤ S * ∑ j : Fin n, a (j - i) * ‖x.ofLp j‖ ^ 2 := by
        intro i
        have hval : (T x).ofLp i = ∑ j : Fin n, (a (j - i) : ℂ) * x.ofLp j := by
          change (A *ᵥ x.ofLp) i = _
          simp [A, RowCirculant, Matrix.mulVec, dotProduct]
        rw [hval]
        have htri : ‖∑ j : Fin n, (a (j - i) : ℂ) * x.ofLp j‖ ≤
            ∑ j : Fin n, a (j - i) * ‖x.ofLp j‖ := by
          calc
            ‖∑ j : Fin n, (a (j - i) : ℂ) * x.ofLp j‖
                ≤ ∑ j : Fin n, ‖(a (j - i) : ℂ) * x.ofLp j‖ := norm_sum_le _ _
            _ = ∑ j : Fin n, a (j - i) * ‖x.ofLp j‖ := by
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha (j - i))]
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := univ)
          (f := fun j : Fin n => Real.sqrt (a (j - i)))
          (g := fun j : Fin n => Real.sqrt (a (j - i)) * ‖x.ofLp j‖)
        have hcs_lhs :
            ∑ j : Fin n, Real.sqrt (a (j - i)) * (Real.sqrt (a (j - i)) * ‖x.ofLp j‖) =
            ∑ j : Fin n, a (j - i) * ‖x.ofLp j‖ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← mul_assoc, Real.mul_self_sqrt (ha (j - i))]
        have hcs_rhs1 : ∑ j : Fin n, Real.sqrt (a (j - i)) ^ 2 = S := by
          have : ∑ j : Fin n, Real.sqrt (a (j - i)) ^ 2 = ∑ j : Fin n, a (j - i) :=
            Finset.sum_congr rfl fun j _ => Real.sq_sqrt (ha (j - i))
          rw [this, sum_sub_right]
        have hcs_rhs2 : ∑ j : Fin n, (Real.sqrt (a (j - i)) * ‖x.ofLp j‖) ^ 2 =
            ∑ j : Fin n, a (j - i) * ‖x.ofLp j‖ ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_pow, Real.sq_sqrt (ha (j - i))]
        rw [hcs_lhs, hcs_rhs1, hcs_rhs2] at hcs
        calc
          ‖∑ j : Fin n, (a (j - i) : ℂ) * x.ofLp j‖ ^ 2
              ≤ (∑ j : Fin n, a (j - i) * ‖x.ofLp j‖) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) htri 2
          _ ≤ S * ∑ j : Fin n, a (j - i) * ‖x.ofLp j‖ ^ 2 := hcs
      calc
        ∑ i : Fin n, ‖(T x).ofLp i‖ ^ 2
            ≤ ∑ i : Fin n, S * ∑ j : Fin n, a (j - i) * ‖x.ofLp j‖ ^ 2 :=
              Finset.sum_le_sum fun i _ => hrow i
        _ = S * ∑ i : Fin n, ∑ j : Fin n, a (j - i) * ‖x.ofLp j‖ ^ 2 := by
              rw [← Finset.mul_sum]
        _ = S * ∑ j : Fin n, (∑ i : Fin n, a (j - i)) * ‖x.ofLp j‖ ^ 2 := by
              congr 1
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_mul]
        _ = S * ∑ j : Fin n, S * ‖x.ofLp j‖ ^ 2 := by
              congr 1
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [sum_sub_left]
        _ = S ^ 2 * ∑ j : Fin n, ‖x.ofLp j‖ ^ 2 := by
              rw [← Finset.mul_sum]; ring
    exact le_of_sq_le_sq hsq (mul_nonneg hS_nn (norm_nonneg x))
  · -- Lower bound: S ≤ ‖T‖ via the all-ones eigenvector
    set v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (fun _ : Fin n => (1 : ℂ))
    have hTv : T v = (S : ℂ) • v := by
      ext i
      change (A *ᵥ (fun _ : Fin n => (1 : ℂ))) i = (S : ℂ) * 1
      simp only [A, RowCirculant, Matrix.mulVec, dotProduct, mul_one]
      rw [← Complex.ofReal_sum, sum_sub_right]
    have hv_pos : 0 < ‖v‖ := by
      have hsq : 0 < ‖v‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq v]
        simp only [v, norm_one, one_pow, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_one]
        exact Nat.cast_pos.mpr hn
      nlinarith [norm_nonneg v]
    have hle := T.le_opNorm v
    rw [hTv, norm_smul, Complex.norm_real, Real.norm_of_nonneg hS_nn] at hle
    exact le_of_mul_le_mul_right hle hv_pos
