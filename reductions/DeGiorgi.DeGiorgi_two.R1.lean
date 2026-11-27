import FormalConjectures.Paper.DeGiorgi

/-!
# The derivative quotient in the planar De Giorgi theorem

The three analytic inputs are a bounded-gradient estimate for the equation,
the weak divergence-form equation for the derivative quotient, and the planar
weighted Liouville theorem. The remaining argument proves the affine structure
of each level set directly from a constant derivative quotient.

See Ghoussoub and Gui (1998), https://doi.org/10.1007/s002080050196.
-/

namespace OMA.R_DeGiorgi_DeGiorgi_two_R1

open EuclideanGeometry InnerProductSpace MeasureTheory Set

private theorem hyperplanes_of_constant_quotient (u : ℝ² → ℝ)
    (hu : Differentiable ℝ u)
    (hv : ∀ x, 0 < fderiv ℝ u x (EuclideanSpace.single 0 1))
    (c : ℝ)
    (hw : ∀ x, fderiv ℝ u x (EuclideanSpace.single 1 1) =
      c * fderiv ℝ u x (EuclideanSpace.single 0 1)) :
    DeGiorgi.HasHyperplaneLevelSets u := by
  let e0 : ℝ² := EuclideanSpace.single 0 1
  let e1 : ℝ² := EuclideanSpace.single 1 1
  let b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  let L : ℝ² →ₗ[ℝ] ℝ := b.coord 0 + c • b.coord 1
  have hL (d : ℝ²) : L d = d 0 + c * d 1 := by
    simp [L, b, Module.Basis.coord_apply, EuclideanSpace.basisFun_repr]
  have hL0 : L e0 = 1 := by simp [hL, e0]
  have hbasis (d : ℝ²) : d = d 0 • e0 + d 1 • e1 := by
    ext i
    fin_cases i <;> simp [e0, e1]
  have hgradient (x d : ℝ²) :
      fderiv ℝ u x d = fderiv ℝ u x e0 * L d := by
    conv_lhs => rw [hbasis d]
    rw [map_add, map_smul, map_smul, hL]
    change d 0 * fderiv ℝ u x e0 + d 1 * fderiv ℝ u x e1 =
      fderiv ℝ u x e0 * (d 0 + c * d 1)
    rw [show fderiv ℝ u x e1 = c * fderiv ℝ u x e0 from hw x]
    ring
  have hline (x d : ℝ²) (t : ℝ) :
      HasDerivAt (fun s : ℝ => u (x + s • d)) (fderiv ℝ u (x + t • d) d) t := by
    exact (hu _).hasFDerivAt.comp_hasDerivAt t
      (by simpa using (((hasDerivAt_id t).smul_const d).const_add x))
  have hsame (x z : ℝ²) (h : L x = L z) : u x = u z := by
    have hd : L (z - x) = 0 := by rw [map_sub, h, sub_self]
    have hconst (t : ℝ) : deriv (fun s : ℝ => u (x + s • (z - x))) t = 0 := by
      rw [(hline x (z - x) t).deriv, hgradient, hd, mul_zero]
    have h01 := is_const_of_deriv_eq_zero
      (fun t => (hline x (z - x) t).differentiableAt) hconst 0 1
    simpa [add_comm] using h01
  have hdifferent (x z : ℝ²) (h : u x = u z) : L x = L z := by
    let t := L x - L z
    have hLz : L (z + t • e0) = L x := by
      rw [map_add, map_smul, hL0]
      simp [t]
    have hu0 : u (z + t • e0) = u z := (hsame _ _ hLz).trans h
    have hinj : Function.Injective (fun s : ℝ => u (z + s • e0)) := by
      apply StrictMono.injective
      apply strictMono_of_deriv_pos
      intro s
      rw [(hline z e0 s).deriv]
      exact hv _
    have ht : t = 0 := hinj (by simpa using hu0)
    exact sub_eq_zero.mp ht
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  refine ⟨AffineSubspace.mk' x L.ker, ?_, ?_⟩
  · ext z
    change u z = u x ↔ z ∈ AffineSubspace.mk' x L.ker
    rw [AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact ⟨hdifferent z x, hsame z x⟩
  · have hsurj : Function.Surjective L := fun r => ⟨r • e0, by simp [hL0]⟩
    have hdim := L.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_euclideanSpace_fin] at hdim
    simp only [Module.finrank_self] at hdim
    rw [AffineSubspace.direction_mk']
    omega

/-- A uniform bound for the transverse derivative of a bounded solution. -/
def H1 : Prop :=
  ∀ u : ℝ² → ℝ, DeGiorgi.IsBoundedSolution u →
    ∃ C : ℝ, ∀ x, |fderiv ℝ u x (EuclideanSpace.single 1 1)| ≤ C

/-- The equation for the derivative quotient, tested against compactly supported functions. -/
def H2 : Prop :=
  ∀ u : ℝ² → ℝ, DeGiorgi.IsBoundedSolution u → DeGiorgi.HasPositiveDeriv u →
    let v := fun x => fderiv ℝ u x (EuclideanSpace.single 0 1)
    let w := fun x => fderiv ℝ u x (EuclideanSpace.single 1 1)
    let q := fun x => w x / v x
    ∀ η : ℝ² → ℝ, ContDiff ℝ 1 η → HasCompactSupport η →
      (∫ x, (v x) ^ 2 * inner ℝ (gradient q x) (gradient η x)) = 0

/-- A planar weighted Liouville theorem. The product of the weight and the solution
is bounded. A radially expanded cutoff first bounds the total weighted energy of
the solution. Repeating the estimate on the cutoff annulus then forces it to vanish. -/
def H3 : Prop :=
  ∀ (v q : ℝ² → ℝ),
    ContDiff ℝ 1 v → ContDiff ℝ 1 q → (∀ x, 0 < v x) →
    (∃ C : ℝ, ∀ x, |v x * q x| ≤ C) →
    (∀ η : ℝ² → ℝ, ContDiff ℝ 1 η → HasCompactSupport η →
      (∫ x, (v x) ^ 2 * inner ℝ (gradient q x) (gradient η x)) = 0) →
    ∃ c : ℝ, ∀ x, q x = c

theorem main : H1 → H2 → H3 → type_of% @DeGiorgi.DeGiorgi_two := by
  intro hbound hequation hliouville u ⟨hu, hup⟩
  let v := fun x : ℝ² => fderiv ℝ u x (EuclideanSpace.single 0 1)
  let w := fun x : ℝ² => fderiv ℝ u x (EuclideanSpace.single 1 1)
  let q := fun x : ℝ² => w x / v x
  have hud : Differentiable ℝ u := hu.regular.differentiable (by norm_num)
  have hv : ∀ x, 0 < v x := by
    intro x
    simpa only [(hud x).lineDeriv_eq_fderiv] using hup x
  have hder : ContDiff ℝ 1 (fderiv ℝ u) := hu.regular.fderiv_right (by norm_num)
  have hvC : ContDiff ℝ 1 v := hder.clm_apply contDiff_const
  have hwC : ContDiff ℝ 1 w := hder.clm_apply contDiff_const
  have hqC : ContDiff ℝ 1 q := hwC.div hvC fun x => (hv x).ne'
  have hmul (x : ℝ²) : v x * q x = w x := by
    dsimp [q]
    field_simp [(hv x).ne']
  obtain ⟨C, hC⟩ := hbound u hu
  have hbounded : ∃ C : ℝ, ∀ x, |v x * q x| ≤ C :=
    ⟨C, fun x => hmul x ▸ hC x⟩
  obtain ⟨c, hc⟩ := hliouville v q hvC hqC hv hbounded (hequation u hu hup)
  refine hyperplanes_of_constant_quotient u hud hv c fun x => ?_
  exact (div_eq_iff (hv x).ne').mp (hc x)

end OMA.R_DeGiorgi_DeGiorgi_two_R1
