import OMAStatements.S_mo_285463

-- Problem: Inner Product on tensor product of Hilbert spaces is unique?
-- Upstream: statements/mo-285463.lean (declaration OMA.S_mo_285463.main)
-- Credit: @FrancoisCharroin
-- Complex uniqueness by two-step complex polarization; real counterexample on R^2 tensor R^2.

namespace OMA.Mo285463

open Matrix OMA.S_mo_285463
open scoped TensorProduct

lemma sesq_eq_zero_of_diag_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : V → V → ℂ)
    (haddL : ∀ u v w, F (u + v) w = F u w + F v w)
    (haddR : ∀ u v w, F u (v + w) = F u v + F u w)
    (hsmulL : ∀ (c : ℂ) u v, F (c • u) v = starRingEnd ℂ c * F u v)
    (hsmulR : ∀ (c : ℂ) u v, F u (c • v) = c * F u v)
    (hdiag : ∀ u, F u u = 0) : ∀ u v, F u v = 0 := by
  intro u v
  have h1 : F u v + F v u = 0 := by
    have h := hdiag (u + v)
    rw [haddL, haddR, haddR, hdiag u, hdiag v] at h
    simpa using h
  have h2 : Complex.I * F u v - Complex.I * F v u = 0 := by
    have h := hdiag (u + Complex.I • v)
    rw [haddL, haddR, haddR, hsmulL, hsmulR, hsmulL, hsmulR, hdiag u, hdiag v] at h
    simp only [Complex.conj_I, mul_zero, zero_add, add_zero] at h
    linear_combination h
  have h3 : (2 * Complex.I) * F u v = 0 := by
    linear_combination Complex.I * h1 + h2
  rcases mul_eq_zero.mp h3 with h2i | huv
  · exfalso
    have hne : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
    exact hne h2i
  · exact huv

lemma complex_part
    (H K : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (B : (H ⊗[ℂ] K) →ₗ⋆[ℂ] (H ⊗[ℂ] K) →ₗ[ℂ] ℂ)
    (hB : ∀ h k, B (h ⊗ₜ[ℂ] k) (h ⊗ₜ[ℂ] k) = inner ℂ h h * inner ℂ k k) :
    B = innerₛₗ ℂ := by
  let D : (H ⊗[ℂ] K) →ₗ⋆[ℂ] (H ⊗[ℂ] K) →ₗ[ℂ] ℂ := B - innerₛₗ ℂ
  have hdiag : ∀ h k, D (h ⊗ₜ[ℂ] k) (h ⊗ₜ[ℂ] k) = 0 := by
    intro h k
    change B (h ⊗ₜ[ℂ] k) (h ⊗ₜ[ℂ] k) - innerₛₗ ℂ (h ⊗ₜ[ℂ] k) (h ⊗ₜ[ℂ] k) = 0
    rw [hB h k]
    simp
    ring
  have hstep1 : ∀ (k : K) (h₁ h₂ : H), D (h₁ ⊗ₜ[ℂ] k) (h₂ ⊗ₜ[ℂ] k) = 0 := by
    intro k
    exact sesq_eq_zero_of_diag_eq_zero (fun h₁ h₂ => D (h₁ ⊗ₜ[ℂ] k) (h₂ ⊗ₜ[ℂ] k))
      (fun u v w => by rw [TensorProduct.add_tmul, map_add, LinearMap.add_apply])
      (fun u v w => by rw [TensorProduct.add_tmul, map_add])
      (fun c u v => by
        rw [← TensorProduct.smul_tmul', map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul])
      (fun c u v => by
        rw [← TensorProduct.smul_tmul', map_smul, smul_eq_mul])
      (fun h => hdiag h k)
  have hstep2 : ∀ (h₁ h₂ : H) (k₁ k₂ : K), D (h₁ ⊗ₜ[ℂ] k₁) (h₂ ⊗ₜ[ℂ] k₂) = 0 := by
    intro h₁ h₂
    exact sesq_eq_zero_of_diag_eq_zero (fun k₁ k₂ => D (h₁ ⊗ₜ[ℂ] k₁) (h₂ ⊗ₜ[ℂ] k₂))
      (fun u v w => by rw [TensorProduct.tmul_add, map_add, LinearMap.add_apply])
      (fun u v w => by rw [TensorProduct.tmul_add, map_add])
      (fun c u v => by
        rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul', map_smulₛₗ,
          LinearMap.smul_apply, smul_eq_mul])
      (fun c u v => by
        rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul', map_smul, smul_eq_mul])
      (fun k => hstep1 k h₁ h₂)
  have hright : ∀ (h₁ : H) (k₁ : K) (y : H ⊗[ℂ] K), D (h₁ ⊗ₜ[ℂ] k₁) y = 0 := by
    intro h₁ k₁ y
    induction y using TensorProduct.induction_on with
    | zero => exact map_zero _
    | tmul h₂ k₂ => exact hstep2 h₁ h₂ k₁ k₂
    | add y₁ y₂ ih₁ ih₂ => rw [map_add, ih₁, ih₂, add_zero]
  have hall : ∀ (x y : H ⊗[ℂ] K), D x y = 0 := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul h₁ k₁ => exact hright h₁ k₁ y
    | add x₁ x₂ ih₁ ih₂ => rw [map_add, LinearMap.add_apply, ih₁, ih₂, add_zero]
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact sub_eq_zero.mp (hall x y)

noncomputable def A4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, (1 / 2 : ℝ);
     0, 1, -(1 / 2 : ℝ), 0;
     0, -(1 / 2 : ℝ), 1, 0;
     (1 / 2 : ℝ), 0, 0, 1]

lemma A4_posDef : A4.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [A4]
  · intro x hx
    have hquad :
        star x ⬝ᵥ (A4 *ᵥ x) =
          ((x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2 +
            (x 0 + x 3) ^ 2 + (x 1 - x 2) ^ 2) / 2 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_four, A4]
      ring
    rw [hquad]
    have hne : ∃ i : Fin 4, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    rcases hne with ⟨i, hi⟩
    fin_cases i
    · have h0 : 0 < (x 0) ^ 2 := sq_pos_of_ne_zero hi
      nlinarith [sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3),
        sq_nonneg (x 0 + x 3), sq_nonneg (x 1 - x 2)]
    · have h1 : 0 < (x 1) ^ 2 := sq_pos_of_ne_zero hi
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 2), sq_nonneg (x 3),
        sq_nonneg (x 0 + x 3), sq_nonneg (x 1 - x 2)]
    · have h2 : 0 < (x 2) ^ 2 := sq_pos_of_ne_zero hi
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 3),
        sq_nonneg (x 0 + x 3), sq_nonneg (x 1 - x 2)]
    · have h3 : 0 < (x 3) ^ 2 := sq_pos_of_ne_zero hi
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
        sq_nonneg (x 0 + x 3), sq_nonneg (x 1 - x 2)]

lemma A4_ne_one : A4 ≠ 1 := by
  intro h
  have h03 := congr_fun (congr_fun h 0) 3
  simp [A4] at h03

lemma A4_coords (x y : Fin 2 → ℝ) :
    (coords x y) ⬝ᵥ (A4 *ᵥ coords x y) = (∑ i, (x i) ^ 2) * (∑ i, (y i) ^ 2) := by
  simp [coords, dotProduct, Matrix.mulVec, Fin.sum_univ_four, Fin.sum_univ_two, A4]
  ring

end OMA.Mo285463

theorem OMA.solution : type_of% @OMA.S_mo_285463.main := by
  exact ⟨OMA.Mo285463.complex_part,
    ⟨OMA.Mo285463.A4, OMA.Mo285463.A4_posDef, OMA.Mo285463.A4_ne_one, OMA.Mo285463.A4_coords⟩⟩
