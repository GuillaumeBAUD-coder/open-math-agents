import OMAReductions.R_ErdosUlamProblem_erdos_ulam_problem_variants_solymosi_de_zeeuw_R1

-- Proof of ErdosUlamProblem.erdos_ulam_problem.variants.solymosi_de_zeeuw.R1.H2
-- Circle inversion about a point p₀ ∈ S on the circle maps the circle (minus p₀)
-- onto an affine line while preserving rationality of pairwise distances.
-- Credit: @DPS0340

open Set Module
open scoped RealInnerProductSpace

theorem OMA.solution :
    OMA.R_ErdosUlamProblem_erdos_ulam_problem_variants_solymosi_de_zeeuw_R1.H2 := by
  classical
  intro hline S hd c ρ hρ hmany
  obtain ⟨p₀, hp₀S, hp₀C⟩ := hmany.nonempty
  have hp₀_ne_c : p₀ ≠ c := by
    intro h; subst h; rw [dist_self] at hp₀C; linarith
  let v : EuclideanSpace ℝ (Fin 2) := p₀ - c
  have hv_ne : v ≠ 0 := sub_ne_zero.mpr hp₀_ne_c
  have hv_norm : ‖v‖ = ρ := by simpa [v, dist_eq_norm] using hp₀C
  -- Inversion in the unit circle centered at p₀
  let inv : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun x => p₀ + (‖x - p₀‖ ^ 2)⁻¹ • (x - p₀)
  have hinv_inv : ∀ x, x ≠ p₀ → inv (inv x) = x := by
    intro x hx
    have hxn : ‖x - p₀‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
    have hnorm : ‖inv x - p₀‖ = ‖x - p₀‖⁻¹ := by
      dsimp [inv]
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      field_simp
    change p₀ + (‖inv x - p₀‖ ^ 2)⁻¹ • (inv x - p₀) = x
    rw [hnorm]
    dsimp [inv]
    rw [add_sub_cancel_left, smul_smul]
    have hsc : ((‖x - p₀‖⁻¹) ^ 2)⁻¹ * (‖x - p₀‖ ^ 2)⁻¹ = 1 := by
      rw [inv_pow, inv_inv]; exact mul_inv_cancel₀ (pow_ne_zero 2 hxn)
    rw [hsc, one_smul, add_sub_cancel]
  have hinv_inj : Set.InjOn inv (S \ {p₀}) := by
    intro x hx y hy hxy
    have h1 := hinv_inv x hx.2
    have h2 := hinv_inv y hy.2
    rw [hxy] at h1
    exact h1.symm.trans h2
  -- Distance formula under unit-circle inversion: dist (inv x) (inv y) = dist x y / (dist x p₀ * dist y p₀)
  have hinv_dist : ∀ x y, x ≠ p₀ → y ≠ p₀ →
      dist (inv x) (inv y) = dist x y / (dist x p₀ * dist y p₀) := by
    intro x y hx hy
    set a := x - p₀
    set b := y - p₀
    have ha : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
    have hb : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy)
    have hdist_sub : inv x - inv y = (‖a‖ ^ 2)⁻¹ • a - (‖b‖ ^ 2)⁻¹ • b := by
      dsimp [inv]; abel
    have hsq : ‖inv x - inv y‖ ^ 2 = (‖a - b‖ / (‖a‖ * ‖b‖)) ^ 2 := by
      have h1 := norm_sub_sq_real ((‖a‖ ^ 2)⁻¹ • a) ((‖b‖ ^ 2)⁻¹ • b)
      have h2 := norm_sub_sq_real a b
      rw [hdist_sub, h1, norm_smul, norm_smul,
        real_inner_smul_left, real_inner_smul_right,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _)),
        abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _)),
        div_pow, h2]
      field_simp [ha, hb]
      ring
    have hnn1 : 0 ≤ ‖inv x - inv y‖ := norm_nonneg _
    have hnn2 : 0 ≤ ‖a - b‖ / (‖a‖ * ‖b‖) := by positivity
    have hnorm_eq : ‖inv x - inv y‖ = ‖a - b‖ / (‖a‖ * ‖b‖) := by
      nlinarith [sq_nonneg (‖inv x - inv y‖ - ‖a - b‖ / (‖a‖ * ‖b‖))]
    have hab : a - b = x - y := by dsimp [a, b]; abel
    simpa [dist_eq_norm, hab] using hnorm_eq
  -- Image affine line L = {y | inner ℝ (y - p₀) v = -1/2}
  let dir : Submodule ℝ (EuclideanSpace ℝ (Fin 2)) := (Submodule.span ℝ ({v} : Set _))ᗮ
  let q₀ : EuclideanSpace ℝ (Fin 2) := p₀ + (-(1 : ℝ) / (2 * ‖v‖ ^ 2)) • v
  let L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) := AffineSubspace.mk' q₀ dir
  have hmemL : ∀ y : EuclideanSpace ℝ (Fin 2), y ∈ L ↔ inner ℝ (y - p₀) v = -(1 : ℝ) / 2 := by
    intro y
    rw [AffineSubspace.mem_mk']
    change y -ᵥ q₀ ∈ (Submodule.span ℝ ({v} : Set _))ᗮ ↔ _
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left, vsub_eq_sub]
    have hv2 : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv_ne)
    have hrew : y - q₀ = (y - p₀) - (-(1 : ℝ) / (2 * ‖v‖ ^ 2)) • v := by dsimp [q₀]; abel
    rw [hrew, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hcalc : (-(1 : ℝ) / (2 * ‖v‖ ^ 2)) * ‖v‖ ^ 2 = -(1 : ℝ) / 2 := by field_simp [hv2]
    rw [hcalc]
    constructor <;> intro h <;> linarith
  have hdimL : finrank ℝ L.direction ≤ 1 := by
    have hdir : L.direction = dir := AffineSubspace.direction_mk' q₀ dir
    rw [hdir]
    have hsum := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ ({v} : Set _))
    have hspan : finrank ℝ (Submodule.span ℝ ({v} : Set _)) = 1 := finrank_span_singleton hv_ne
    have htot : finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
    dsimp [dir]
    omega
  -- Circle membership (for x ≠ p₀) ↔ inv x ∈ L
  have hcircle_iff : ∀ x, x ≠ p₀ → (dist x c = ρ ↔ inv x ∈ L) := by
    intro x hx
    rw [hmemL]
    have hxn : ‖x - p₀‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
    have hxn2 : ‖x - p₀‖ ^ 2 ≠ 0 := pow_ne_zero 2 hxn
    have hxc : x - c = (x - p₀) + v := by dsimp [v]; abel
    have hsq_iff : dist x c = ρ ↔ ‖x - c‖ ^ 2 = ρ ^ 2 := by
      rw [dist_eq_norm]
      constructor
      · intro h; rw [h]
      · intro h; nlinarith [norm_nonneg (x - c)]
    rw [hsq_iff, hxc, norm_add_sq_real, hv_norm]
    have hinv_inner : inner ℝ (inv x - p₀) v = (‖x - p₀‖ ^ 2)⁻¹ * inner ℝ (x - p₀) v := by
      dsimp [inv]; rw [add_sub_cancel_left, real_inner_smul_left]
    rw [hinv_inner]
    constructor
    · intro h
      have hlin : 2 * inner ℝ (x - p₀) v = -(‖x - p₀‖ ^ 2) := by linarith
      field_simp [hxn2]
      linarith
    · intro h
      have hmul := congrArg (fun t => (2 * ‖x - p₀‖ ^ 2) * t) h
      have hlhs : 2 * ‖x - p₀‖ ^ 2 * ((‖x - p₀‖ ^ 2)⁻¹ * inner ℝ (x - p₀) v) =
          2 * inner ℝ (x - p₀) v := by field_simp [hxn2]
      have hrhs : 2 * ‖x - p₀‖ ^ 2 * (-(1 : ℝ) / 2) = -(‖x - p₀‖ ^ 2) := by ring
      linarith
  -- Apply the affine-line theorem to S' = inv '' (S \ {p₀})
  let S' : Set (EuclideanSpace ℝ (Fin 2)) := inv '' (S \ {p₀})
  have hS'_rat : ∀ y ∈ S', ∀ z ∈ S', ∃ q : ℚ, dist y z = (q : ℝ) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨qxy, hqxy⟩ := hd x hx.1 y hy.1
    obtain ⟨qx, hqx⟩ := hd x hx.1 p₀ hp₀S
    obtain ⟨qy, hqy⟩ := hd y hy.1 p₀ hp₀S
    refine ⟨qxy / (qx * qy), ?_⟩
    rw [hinv_dist x y hx.2 hy.2, hqxy, hqx, hqy]
    push_cast; rfl
  have hS'_inf : (S' ∩ (L : Set _)).Infinite := by
    have hCsub : ({x ∈ S | dist x c = ρ} \ {p₀}).Infinite := hmany.sdiff (finite_singleton p₀)
    have hsubC : {x ∈ S | dist x c = ρ} \ {p₀} ⊆ S \ {p₀} := fun x hx => ⟨hx.1.1, hx.2⟩
    apply (hCsub.image (hinv_inj.mono hsubC)).mono
    rintro _ ⟨x, ⟨⟨hxS, hxC⟩, hxp⟩, rfl⟩
    exact ⟨⟨x, ⟨hxS, hxp⟩, rfl⟩, (hcircle_iff x hxp).mp hxC⟩
  have hS'_fin : (S' \ (L : Set _)).Finite := hline S' hS'_rat L hdimL hS'_inf
  have hsub_off : {x ∈ S | dist x c ≠ ρ} ⊆ S \ {p₀} := by
    intro x ⟨hxS, hxC⟩
    refine ⟨hxS, fun h => ?_⟩
    subst h; exact hxC hp₀C
  rw [← finite_image_iff (hinv_inj.mono hsub_off)]
  apply hS'_fin.subset
  rintro _ ⟨x, ⟨hxS, hxC⟩, rfl⟩
  have hxp : x ≠ p₀ := fun h => hxC (h ▸ hp₀C)
  exact ⟨⟨x, ⟨hxS, hxp⟩, rfl⟩, fun hL => hxC ((hcircle_iff x hxp).mpr hL)⟩
