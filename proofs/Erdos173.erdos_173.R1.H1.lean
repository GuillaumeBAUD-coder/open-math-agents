import OMAReductions.R_Erdos173_erdos_173_R1

-- Port of the eight-point argument from Jacob Parish (Plasma AI), Apache-2.0.
-- https://github.com/plasma-ai/erdos-173/tree/4a368a652753
-- The configuration is due to Erdős et al., as presented by Jelínek et al.
-- This adaptation gets the two unit rotations directly from the given equilateral triple.

open Affine
open scoped Congruent EuclideanGeometry
noncomputable section
namespace OMA.E173Side

def MonoCopy (c : ℂ → Fin 2) (a b p u : ℂ) : Prop :=
  c (p + u * a) = c p ∧ c (p + u * b) = c p

lemma monoCopy_iff (c : ℂ → Fin 2) (a b p u t m x y : ℂ) (hx : t + m * a = x)
    (hy : t + m * b = y) :
    MonoCopy c a b (p + u * t) (u * m) ↔
      c (p + u * x) = c (p + u * t) ∧ c (p + u * y) = c (p + u * t) := by
  subst hx hy
  have e₁ : p + u * t + u * m * a = p + u * (t + m * a) := by ring
  have e₂ : p + u * t + u * m * b = p + u * (t + m * b) := by ring
  simp only [MonoCopy, e₁, e₂]

/-- The color bookkeeping of part (i). -/
lemma forcing_i : ∀ A B C D B' A' C' D' : Fin 2, B = A → C = A →
    ¬ (B = A ∧ D = A) → ¬ (C = A ∧ B' = A) → ¬ (C = B ∧ D' = B) →
    ¬ (B' = A' ∧ D' = A') → ¬ (C' = A' ∧ B = A') → ¬ (C' = B' ∧ D = B') → False := by
  intro A B C D B' A' C' D'
  omega

lemma force {c : ℂ → Fin 2} {a z ζ p u : ℂ} (hu : ‖u‖ = 1)
    (norm_ζ : ‖ζ‖ = 1) (norm_one_sub_ζ : ‖1 - ζ‖ = 1)
    (hABC : MonoCopy c a (a * ζ) p u)
    (hav : ∀ p u : ℂ, ‖u‖ = 1 → ¬ MonoCopy c a z p u) : False := by
  have norm_ζ_sub_one : ‖ζ - 1‖ = 1 := (norm_sub_rev _ _).trans norm_one_sub_ζ
  have key : ∀ t m x y : ℂ, ‖m‖ = 1 → t + m * a = x → t + m * z = y →
      ¬ (c (p + u * x) = c (p + u * t) ∧ c (p + u * y) = c (p + u * t)) := by
    intro t m x y hm hx hy
    rw [← monoCopy_iff c a z p u t m x y hx hy]
    exact hav _ _ (by rw [norm_mul, hu, hm, one_mul])
  -- `BAD`, `CAB'`, `CBD'`, `B'A'D'`, `C'A'B`, `C'B'D`
  have h₁ := key 0 1 a z (by simp) (by ring) (by ring)
  have h₂ := key 0 ζ (a * ζ) (ζ * z) norm_ζ (by ring) (by ring)
  have h₃ := key a (ζ - 1) (a * ζ) (a - (1 - ζ) * z) norm_ζ_sub_one (by ring) (by ring)
  have h₄ := key (a + ζ * z) (-1) (ζ * z) (a - (1 - ζ) * z) (by simp) (by ring) (by ring)
  have h₅ := key (a + ζ * z) (-ζ) (a * (1 - ζ) + ζ * z) a (by simp [norm_ζ]) (by ring)
    (by ring)
  have h₆ := key (ζ * z) (1 - ζ) (a * (1 - ζ) + ζ * z) z norm_one_sub_ζ (by ring) (by ring)
  simp only [mul_zero, add_zero] at h₁ h₂
  exact forcing_i _ _ _ _ _ _ _ _ hABC.1 hABC.2 h₁ h₂ h₃ h₄ h₅ h₆

def toC : ℝ² ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

/-- The motion `w ↦ k w + t` of `ℂ`, as a real affine map. -/
def cMotion (k t : ℂ) : ℂ →ᵃ[ℝ] ℂ where
  toFun w := k * w + t
  linear := LinearMap.mulLeft ℝ k
  map_vadd' p v := by
    simp only [vadd_eq_add, LinearMap.mulLeft_apply]
    ring

/-- The motion `w ↦ k w + t` of `ℂ`, transported to `ℝ²`. -/
def pMotion (k t : ℂ) : ℝ² →ᵃ[ℝ] ℝ² :=
  toC.symm.toLinearEquiv.toLinearMap.toAffineMap.comp
    ((cMotion k t).comp toC.toLinearEquiv.toLinearMap.toAffineMap)

/-- `pMotion k t` acts as `w ↦ k w + t` in the coordinate `toC`. -/
lemma pMotion_apply (k t : ℂ) (x : ℝ²) : pMotion k t x = toC.symm (k * toC x + t) :=
  rfl

/-- A motion with `‖k‖ = 1` is an isometry. -/
lemma isometry_pMotion {k : ℂ} (hk : ‖k‖ = 1) (t : ℂ) : Isometry (pMotion k t) :=
  Isometry.of_dist_eq fun x y => by
    rw [pMotion_apply, pMotion_apply, LinearIsometryEquiv.dist_map, dist_eq_norm,
      add_sub_add_right_eq_sub, ← mul_sub, norm_mul, hk, one_mul, ← dist_eq_norm,
      LinearIsometryEquiv.dist_map]

/-- The point `v (σ j)`, in `ℂ`. -/
def vertex (v : Fin 3 → ℝ²) (σ : Equiv.Perm (Fin 3)) (j : Fin 3) : ℂ :=
  toC (v (σ j))

/-- The side `a = |w₁ - w₀|` of the template of `v` relabelled by `σ`. -/
def side (v : Fin 3 → ℝ²) (σ : Equiv.Perm (Fin 3)) : ℝ :=
  dist (v (σ 0)) (v (σ 1))

/-- The direction `u₀ = (w₁ - w₀)/a` of the first side. -/
def frame (v : Fin 3 → ℝ²) (σ : Equiv.Perm (Fin 3)) : ℂ :=
  (vertex v σ 1 - vertex v σ 0) / side v σ

/-- The apex `z = (w₂ - w₀)/u₀` of the template of `v` relabelled by `σ`. -/
def apex (v : Fin 3 → ℝ²) (σ : Equiv.Perm (Fin 3)) : ℂ :=
  (vertex v σ 2 - vertex v σ 0) / frame v σ

/-- Distinct points stay distinct in `ℂ`. -/
lemma vertex_ne {v : Fin 3 → ℝ²} (hv : Function.Injective v) (σ : Equiv.Perm (Fin 3))
    {i j : Fin 3} (h : i ≠ j) : vertex v σ i ≠ vertex v σ j := fun e =>
  h (σ.injective (hv (toC.injective e)))

/-- The identification with `ℂ` preserves the distances between the points. -/
lemma norm_vertex_sub (v : Fin 3 → ℝ²) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    ‖vertex v σ i - vertex v σ j‖ = dist (v (σ i)) (v (σ j)) := by
  rw [vertex, vertex, ← dist_eq_norm, LinearIsometryEquiv.dist_map]

/-- The first side of three distinct points is positive. -/
lemma side_pos {v : Fin 3 → ℝ²} (hv : Function.Injective v) (σ : Equiv.Perm (Fin 3)) :
    0 < side v σ :=
  dist_pos.2 fun e => absurd (σ.injective (hv e)) (by decide)

/-- The direction of the first side is a unit. -/
lemma norm_frame {v : Fin 3 → ℝ²} (hv : Function.Injective v) (σ : Equiv.Perm (Fin 3)) :
    ‖frame v σ‖ = 1 := by
  rw [frame, norm_div, norm_vertex_sub, Complex.norm_real, Real.norm_of_nonneg
    (side_pos hv σ).le, dist_comm]
  exact div_self (side_pos hv σ).ne'

/-- Turning the first side back by its direction gives its length. -/
lemma side_eq {v : Fin 3 → ℝ²} (hv : Function.Injective v) (σ : Equiv.Perm (Fin 3)) :
    (vertex v σ 1 - vertex v σ 0) / frame v σ = side v σ :=
  div_div_cancel₀ (sub_ne_zero.2 (vertex_ne hv σ (by decide)))

/-- A monochromatic copy of the template of `v`, for the coloring transported to `ℂ`,
gives a monochromatic image of `v` under a motion. -/
theorem exists_motion_of_monoCopy (c : ℝ² → Fin 2) {v : Fin 3 → ℝ²}
    (hv : Function.Injective v) (σ : Equiv.Perm (Fin 3)) {p u : ℂ} (hu : ‖u‖ = 1)
    (h : MonoCopy (c ∘ toC.symm) (side v σ) (apex v σ) p u) :
    ∃ k t : ℂ, ‖k‖ = 1 ∧ ∃ i, ∀ j, c (pMotion k t (v j)) = i := by
  set k := u / frame v σ
  have hk : ‖k‖ = 1 := by rw [norm_div, hu, norm_frame hv, div_one]
  set t := p - k * vertex v σ 0
  refine ⟨k, t, hk, c (toC.symm p), fun j => ?_⟩
  obtain ⟨m, rfl⟩ := σ.surjective j
  rw [pMotion_apply, ← vertex]
  fin_cases m
  · simp [t]
  · have e : k * vertex v σ 1 + t = p + u * side v σ := by
      rw [← side_eq hv]
      simp only [k, t]
      ring
    simpa [e] using h.1
  · have e : k * vertex v σ 2 + t = p + u * apex v σ := by
      simp only [k, t, apex]
      ring
    simpa [e] using h.2

end OMA.E173Side

open OMA.E173Side

theorem OMA.solution : OMA.R_Erdos173_erdos_173_R1.H1 := by
  intro c T hT i j hij v hd ⟨col, hc⟩
  obtain ⟨σ, h₀, h₁⟩ := (show ∀ i j : Fin 3, i ≠ j →
    ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 1 = j by decide) i j hij
  let r := side T.points σ
  have hr : 0 < r := side_pos T.independent.injective σ
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  let w (k : Fin 3) := toC (v k)
  have hn (k l : Fin 3) (hkl : k ≠ l) : ‖w k - w l‖ = r := by
    rw [← dist_eq_norm, LinearIsometryEquiv.dist_map, hd _ _ hkl]
    simp [r, side, h₀, h₁]
  let A := w 1 - w 0
  let B := w 2 - w 0
  have hA : ‖A‖ = r := hn 1 0 (by decide)
  have hB : ‖B‖ = r := hn 2 0 (by decide)
  have hAB : ‖A - B‖ = r := by simpa [A, B] using hn 1 2 (by decide)
  have hA0 : A ≠ 0 := norm_ne_zero_iff.mp (hA.trans_ne hr.ne')
  let u := A / (r : ℂ)
  let ζ := B / A
  have hu : ‖u‖ = 1 := by simp [u, norm_div, hA, abs_of_pos hr, hr.ne']
  have hz : ‖ζ‖ = 1 := by simp [ζ, norm_div, hB, hA, hr.ne']
  have hz' : ‖1 - ζ‖ = 1 := by
    rw [show 1 - ζ = (A - B) / A by dsimp [ζ]; field_simp]
    rw [norm_div, hAB, hA, div_self hr.ne']
  let c' := c ∘ toC.symm
  have hm : MonoCopy c' r (r * ζ) (w 0) u := by
    have e₁ : w 0 + u * r = w 1 := by simp [u, A, hrC]
    have e₂ : w 0 + u * (r * ζ) = w 2 := by
      dsimp [u, ζ]
      field_simp
      simp [A, B]
      <;> ring
    constructor
    · simpa [c', w, e₁] using (show c' (w 1) = c' (w 0) by simp [c', w, hc])
    · simpa [c', w, e₂] using (show c' (w 2) = c' (w 0) by simp [c', w, hc])
  apply force (z := apex T.points σ) hu hz hz' hm
  intro p k hk hmono
  obtain ⟨l, t, hl, clr, hclr⟩ := exists_motion_of_monoCopy c T.independent.injective σ hk hmono
  exact hT ⟨T.map (pMotion l t) (isometry_pMotion hl t).injective,
    show Congruent (pMotion l t ∘ T.points) T.points from
      (Congruent.refl _).comp_left (isometry_pMotion hl t), clr, hclr⟩
end
