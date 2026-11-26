import FormalConjectures.Arxiv.«2607.27197».MaxwellConjecture

/-! For an equilibrium, the inverse-square law fixes the ratio of the distances to the
two charges. With that ratio fixed, the vector field equation is affine in the point. -/

namespace MaxwellTwoCharge

open Arxiv.«2607.27197»
open scoped Gradient

abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Derivative of one Coulomb potential away from its charge. -/
theorem charge_derivative (c : ℝ) (a x : Space) (hx : x ≠ a) :
    HasFDerivAt (fun y : Space => c / dist y a)
      (InnerProductSpace.toDual ℝ Space ((-c / dist x a ^ 3) • (x - a))) x := by
  have hn : ‖x - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  have hsq : HasFDerivAt (fun y : Space => ‖y - a‖ ^ 2) (2 • innerSL ℝ (x - a)) x := by
    simpa using (hasFDerivAt_sub_const (𝕜 := ℝ) (x := x) a).norm_sq
  have hdist := hsq.sqrt (pow_ne_zero 2 hn)
  simp only [Real.sqrt_sq_eq_abs, abs_norm] at hdist
  have hrec : HasDerivAt (fun r : ℝ => c / r) (-c / ‖x - a‖ ^ 2) ‖x - a‖ := by
    simpa using (hasDerivAt_const ‖x - a‖ c).fun_div (hasDerivAt_id' ‖x - a‖) hn
  simp only [dist_eq_norm]
  apply (hrec.comp_hasFDerivAt x hdist).congr_fderiv
  ext v
  simp only [smul_apply, two_smul, add_apply,
    innerSL_apply_apply, InnerProductSpace.toDual_apply_apply, real_inner_smul_left, smul_eq_mul]
  field_simp [hn]
  ring

/-- The balance of the two forces determines a positive distance ratio and a vector equation. -/
theorem equilibrium_ratio {q : Fin 2 → ℝ} {a : Fin 2 → Space} {x : Space}
    (hx : x ∈ equilibria q a) :
    ∃ r : ℝ, 0 < r ∧ |q 0| = |q 1| * r ^ 2 ∧
      q 0 • (x - a 0) = (-(q 1 * r ^ 3)) • (x - a 1) := by
  have hoff (j : Fin 2) : x ≠ a j := fun h => hx.1 ⟨j, h.symm⟩
  let d (j : Fin 2) := dist x (a j)
  have hd (j : Fin 2) : 0 < d j := dist_pos.mpr (hoff j)
  let r := d 0 / d 1
  have hr : 0 < r := div_pos (hd 0) (hd 1)
  let v (j : Fin 2) := (-q j / d j ^ 3) • (x - a j)
  have hg : HasGradientAt (potential q a) (v 0 + v 1) x := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    have hpot : potential q a =
        (fun y : Space => q 0 / dist y (a 0)) + (fun y : Space => q 1 / dist y (a 1)) := by
      funext y
      simp only [potential, Fin.sum_univ_two, Pi.add_apply]
    rw [hpot, map_add]
    exact (charge_derivative (q 0) (a 0) x (hoff 0)).add
      (charge_derivative (q 1) (a 1) x (hoff 1))
  have hz : v 0 + v 1 = 0 := hg.gradient.symm.trans hx.2
  have hs := congrArg (fun w : Space => (-(d 0 ^ 3)) • w) hz
  change (-(d 0 ^ 3)) • (v 0 + v 1) = (-(d 0 ^ 3)) • (0 : Space) at hs
  simp only [v, smul_add, smul_smul, smul_zero] at hs
  have h0 : -(d 0 ^ 3) * (-q 0 / d 0 ^ 3) = q 0 := by field_simp [(hd 0).ne']
  have h1 : -(d 0 ^ 3) * (-q 1 / d 1 ^ 3) = q 1 * r ^ 3 := by
    dsimp only [r]
    field_simp [(hd 1).ne']
  rw [h0, h1] at hs
  have hv : q 0 • (x - a 0) = (-(q 1 * r ^ 3)) • (x - a 1) := by
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left hs
  refine ⟨r, hr, ?_, hv⟩
  have hnorm := congrArg (fun w : Space => ‖w‖) hv
  simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos (pow_pos hr 3),
    ← dist_eq_norm] at hnorm
  apply mul_right_cancel₀ (mul_ne_zero hr.ne' (hd 1).ne')
  calc
    |q 0| * (r * d 1) = |q 0| * d 0 :=
      congrArg (fun t => |q 0| * t) (div_mul_cancel₀ (d 0) (hd 1).ne')
    _ = |q 1| * r ^ 3 * d 1 := hnorm
    _ = (|q 1| * r ^ 2) * (r * d 1) := by ring

/-- A fixed signed ratio of displacements from distinct sites determines at most one point. -/
theorem affine_unique {a b x y : Space} {c d : ℝ} (hab : a ≠ b) (hc : c ≠ 0)
    (hx : c • (x - a) = d • (x - b)) (hy : c • (y - a) = d • (y - b)) : x = y := by
  have hcd : c ≠ d := by
    intro h
    rw [← h] at hx
    exact hab (sub_right_inj.mp (smul_right_injective Space hc hx))
  have hzero : (c - d) • (x - y) = 0 := by
    linear_combination (norm := module) hx - hy
  exact sub_eq_zero.mp ((smul_eq_zero_iff_right (sub_ne_zero.mpr hcd)).mp hzero)

end MaxwellTwoCharge

theorem OMA.solution : type_of% @Arxiv.«2607.27197».maxwell_conjecture.variants.two_charges := by
  intro q a ha hq
  apply Set.encard_le_one_iff.mpr
  intro x y hx hy
  obtain ⟨r, hr, hqr, hxr⟩ := MaxwellTwoCharge.equilibrium_ratio hx
  obtain ⟨s, hs, hqs, hys⟩ := MaxwellTwoCharge.equilibrium_ratio hy
  have hrs : r = s := (sq_eq_sq₀ hr.le hs.le).mp
    (mul_left_cancel₀ (abs_ne_zero.mpr (hq 1)) (hqr.symm.trans hqs))
  subst s
  exact MaxwellTwoCharge.affine_unique (ha.ne (by decide : (0 : Fin 2) ≠ 1)) (hq 0) hxr hys
