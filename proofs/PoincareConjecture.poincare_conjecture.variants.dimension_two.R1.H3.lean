import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
Approximate a based loop in the unit sphere by a Bernstein polynomial in ambient
space, then radially project the polynomial and the straight-line homotopy. The
projected loop omits a point: a nonzero coordinate polynomial meets the
corresponding coordinate plane at only finitely many parameters. Stereographic
projection contracts the loop in the punctured sphere.
-/

-- Credit: @dk8827

open Metric Filter Set Polynomial
open scoped unitInterval BigOperators

namespace OMA.SphereLoops

private abbrev E := EuclideanSpace ℝ (Fin 3)
private abbrev S := sphere (0 : E) 1

private noncomputable def radial (y : E) : E := ‖y‖⁻¹ • y

private theorem radial_mem (y : E) (hy : y ≠ 0) : radial y ∈ sphere (0 : E) 1 := by
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  change dist (radial y) 0 = 1
  rw [dist_zero_right, radial, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    inv_mul_cancel₀ hn.ne']

private theorem radial_fixed (x : S) : radial (x : E) = x := by
  rw [radial, norm_eq_of_mem_sphere x, inv_one, one_smul]

private theorem radial_continuous : ContinuousOn radial ({0}ᶜ : Set E) := by
  exact (continuous_norm.continuousOn.inv₀
    (fun _ hy => norm_ne_zero_iff.2 (by simpa using hy))).smul continuous_id.continuousOn

private theorem bernstein_coord (n : ℕ) (f : C(I, E)) :
    ∃ P : ℝ[X], ∀ t : I, P.eval (t : ℝ) = bernsteinApproximation n f t 0 := by
  let l : E →L[ℝ] ℝ := EuclideanSpace.proj 0
  refine ⟨∑ k : Fin (n + 1), C (l (f (bernstein.z k))) *
    bernsteinPolynomial ℝ n k, fun t => ?_⟩
  change _ = l (bernsteinApproximation n f t)
  rw [bernsteinApproximation.apply, map_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  simp [bernstein, Polynomial.toContinuousMapOn, Polynomial.toContinuousMap, mul_comm]

private theorem radial_ratio (u : E) (hu : u ≠ 0) :
    radial u 2 / radial u 1 = u 2 / u 1 := by
  change ((‖u‖ : ℝ)⁻¹ * u 2) / ((‖u‖ : ℝ)⁻¹ * u 1) = _
  exact mul_div_mul_left _ _ (inv_ne_zero (norm_ne_zero_iff.2 hu))

private theorem omits_point (g : C(I, E)) (hn : ∀ t, g t ≠ 0)
    (P : ℝ[X]) (hP : ∀ t : I, P.eval (t : ℝ) = g t 0) :
    ∃ y : S, ∀ t : I, radial (g t) ≠ (y : E) := by
  classical
  by_cases h : P = 0
  · let w : E := WithLp.toLp 2 ![1, 0, 0]
    have hw : w ≠ 0 := by
      intro he
      have h0 := congrArg (fun x : E => x 0) he
      norm_num [w] at h0
    refine ⟨⟨radial w, radial_mem w hw⟩, fun t he => ?_⟩
    have h0 : g t 0 = 0 := by simp [← hP t, h]
    have he0 := congrArg (fun x : E => x 0) he
    change ‖g t‖⁻¹ * g t 0 = ‖w‖⁻¹ * 1 at he0
    have hp : 0 < (‖w‖ : ℝ)⁻¹ := inv_pos.2 (norm_pos_iff.2 hw)
    rw [h0, mul_zero, mul_one] at he0
    exact hp.ne' he0.symm
  · have ht : Set.Finite {t : I | P.eval (t : ℝ) = 0} :=
      (Polynomial.finite_setOfPred_isRoot h).preimage Subtype.val_injective.injOn
    let ratio (t : I) := g t 2 / g t 1
    obtain ⟨r, hr⟩ := (ht.image ratio).exists_notMem
    let w : E := WithLp.toLp 2 ![0, 1, r]
    have hw : w ≠ 0 := by
      intro he
      have h1 := congrArg (fun x : E => x 1) he
      norm_num [w] at h1
    refine ⟨⟨radial w, radial_mem w hw⟩, fun t he => ?_⟩
    have he0 := congrArg (fun x : E => x 0) he
    change ‖g t‖⁻¹ * g t 0 = ‖w‖⁻¹ * 0 at he0
    have ht0 : P.eval (t : ℝ) = 0 := by
      rw [hP]
      rw [mul_zero] at he0
      exact (mul_eq_zero.1 he0).resolve_left (inv_ne_zero (norm_ne_zero_iff.2 (hn t)))
    have heR := congrArg (fun x : E => x 2 / x 1) he
    rw [radial_ratio _ (hn t), radial_ratio w hw] at heR
    change ratio t = r / 1 at heR
    exact hr ⟨t, ht0, by simpa using heR⟩

private theorem homotopic_omitting {x : S} (p : Path x x) :
    ∃ q : Path x x, p.Homotopic q ∧ ∃ y : S, ∀ t : I, q t ≠ y := by
  let f : C(I, E) := ⟨fun t => (p t : E), continuous_subtype_val.comp p.continuous⟩
  have hnear : ∀ᶠ n in atTop, dist (bernsteinApproximation n f) f < 1 :=
    (Metric.tendsto_nhds.1 (bernsteinApproximation_uniform f)) 1 zero_lt_one
  obtain ⟨m, hm⟩ := eventually_atTop.1 hnear
  let n := m + 1
  let g := bernsteinApproximation n f
  have hclose (t : I) : dist (g t) (f t) < 1 :=
    (ContinuousMap.dist_apply_le_dist t).trans_lt (hm n (Nat.le_succ m))
  have g_zero : g 0 = (x : E) := by simp [g, f, p.source]
  have g_one : g 1 = (x : E) := by
    rw [show g 1 = f 1 from bernsteinApproximation.apply_one (by simp [n]) f]
    exact congrArg Subtype.val p.target
  let B (u : I × I) : E := f u.2 + (u.1 : ℝ) • (g u.2 - f u.2)
  have B_cont : Continuous B := by unfold B; fun_prop
  have B_ne (u : I × I) : B u ≠ 0 := by
    intro h
    have hneg : (u.1 : ℝ) • (g u.2 - f u.2) = -(f u.2) :=
      eq_neg_of_add_eq_zero_right h
    have hnorm : ‖(u.1 : ℝ) • (g u.2 - f u.2)‖ = 1 := by
      rw [hneg, norm_neg]
      exact norm_eq_of_mem_sphere (p u.2)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg u.1.2.1, ← dist_eq_norm] at hnorm
    nlinarith [u.1.2.2, dist_nonneg (x := g u.2) (y := f u.2), hclose u.2]
  have g_ne (t : I) : g t ≠ 0 := by
    simpa [B] using B_ne (1, t)
  have g_radial_cont : Continuous (fun t => radial (g t)) :=
    radial_continuous.comp_continuous g.continuous (fun t => by simpa using g_ne t)
  let q : Path x x :=
    { toFun := fun t => ⟨radial (g t), radial_mem _ (g_ne t)⟩
      continuous_toFun := g_radial_cont.subtype_mk _
      source' := Subtype.ext (by simpa [g_zero] using radial_fixed x)
      target' := Subtype.ext (by simpa [g_one] using radial_fixed x) }
  have B_radial_cont : Continuous (fun u => radial (B u)) :=
    radial_continuous.comp_continuous B_cont (fun u => by simpa using B_ne u)
  refine ⟨q, ⟨{
    toFun := fun u => ⟨radial (B u), radial_mem _ (B_ne u)⟩
    continuous_toFun := B_radial_cont.subtype_mk _
    map_zero_left := fun t => Subtype.ext (by simpa [B, f] using radial_fixed (p t))
    map_one_left := fun t => Subtype.ext (by simp [B, q])
    prop' := ?_ }⟩, ?_⟩
  · intro t u hu
    have h := (show u = 0 ∨ u = 1 by simpa using hu)
    rcases h with rfl | rfl
    · apply Subtype.ext
      simp [B, f, g_zero, p.source, radial_fixed x]
    · apply Subtype.ext
      simp [B, f, g_one, p.target, radial_fixed x]
  · obtain ⟨P, hP⟩ := bernstein_coord n f
    obtain ⟨y, hy⟩ := omits_point g g_ne P hP
    exact ⟨y, fun t he => hy t (congrArg Subtype.val he)⟩

private theorem punctured_simplyConnected (y : S) :
    SimplyConnectedSpace ↥(({y} : Set S)ᶜ) := by
  let e := stereographic (norm_eq_of_mem_sphere y)
  have hs : e.source = ({y} : Set S)ᶜ :=
    stereographic_source (norm_eq_of_mem_sphere y)
  have ht : e.target = Set.univ := stereographic_target (norm_eq_of_mem_sphere y)
  let h := (Homeomorph.setCongr hs.symm).trans
    (e.toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr ht).trans (Homeomorph.Set.univ _)))
  have : SimplyConnectedSpace ↥((ℝ ∙ (y : E))ᗮ) :=
    SimplyConnectedSpace.ofContractible _
  exact h.toHomotopyEquiv.simplyConnectedSpace

theorem sphere_simplyConnected : SimplyConnectedSpace S := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨isPathConnected_iff_pathConnectedSpace.1
    (isPathConnected_sphere (by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
      norm_num) (0 : E) zero_le_one), ?_⟩
  intro x p
  obtain ⟨q, hpq, y, hy⟩ := homotopic_omitting p
  have := punctured_simplyConnected y
  let x' : ↥(({y} : Set S)ᶜ) := ⟨x, by simpa [q.source] using hy 0⟩
  have hmem (t : I) : q t ∈ ({y} : Set S)ᶜ := by simpa using hy t
  let q' : Path x' x' :=
    { toFun := fun t => ⟨q t, hmem t⟩
      continuous_toFun := q.continuous.subtype_mk hmem
      source' := Subtype.ext q.source
      target' := Subtype.ext q.target }
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic q' (Path.refl x')
  let incl : C(↥(({y} : Set S)ᶜ), S) := ⟨Subtype.val, continuous_subtype_val⟩
  have hq : q'.map incl.continuous = q := by ext t; rfl
  have hr : (Path.refl x').map incl.continuous = Path.refl x := by ext t; rfl
  refine hpq.trans ⟨?_⟩
  simpa only [hq, hr] using H.map incl

end OMA.SphereLoops

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1.H3 :=
  OMA.SphereLoops.sphere_simplyConnected
