import FormalConjectures.Wikipedia.InscribedSquare

/-!
# Polynomial approximation for the rectangular peg problem

Compactness transfers rectangles of convergent aspect ratios to the limiting curve.
The mean value inequality prevents adjacent perpendicular sides from collapsing
when the velocities converge uniformly to a continuous, nowhere-zero velocity.

Reduction InscribedSquare.exists_inscribed_rectangle_of_smooth.R2. Credit: @yuka30240.
-/

namespace OMA.R_InscribedSquare_exists_inscribed_rectangle_of_smooth_R2

open Filter Topology ContDiff Manifold InscribedSquare
open scoped EuclideanGeometry InnerProductSpace

/-- Approximate a regular periodic parametrization and its velocity uniformly.
The positive lower chord bound records regularity and injectivity of each approximant. -/
def H1 : Prop :=
  ∀ (γ : Circle → ℝ²), IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ γ →
    ∃ P : ℕ → Fin 2 → MvPolynomial (Fin 2) ℚ,
      let f (n : ℕ) (z : Circle) : ℝ² := WithLp.toLp 2 (fun i : Fin 2 =>
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) ![(z : ℂ).re, (z : ℂ).im] (P n i))
      let velocity := deriv (γ ∘ Circle.exp)
      Continuous velocity ∧ (∀ x, velocity x ≠ 0) ∧
        (∀ n, Differentiable ℝ (f n ∘ Circle.exp)) ∧
        TendstoUniformly f γ atTop ∧
        TendstoUniformly (fun n => deriv (f n ∘ Circle.exp)) velocity atTop ∧
        ∀ n, ∃ m : ℝ, 0 < m ∧ ∀ x y : Circle, m * dist x y ≤ dist (f n x) (f n y)

/-- For fixed polynomials and aspect ratio this is a real algebraic problem.
The chord bound can be checked by squaring the two nonnegative sides. -/
def H2 : Prop :=
  ∀ P : Fin 2 → MvPolynomial (Fin 2) ℚ,
    let f (z : Circle) : ℝ² := WithLp.toLp 2 (fun i : Fin 2 =>
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) ![(z : ℂ).re, (z : ℂ).im] (P i))
    (∃ m : ℝ, 0 < m ∧ ∀ x y : Circle, m * dist x y ≤ dist (f x) (f y)) →
    ∀ q : ℚ, 0 < q → ∃ t : Fin 4 → Circle,
      IsRectangle (f (t 0)) (f (t 1)) (f (t 2)) (f (t 3)) (q : ℝ)

lemma rectangle_orthogonal {a b c d : ℝ²} {r : ℝ} (h : IsRectangle a b c d r) :
    ⟪a - b, b - c⟫_ℝ = 0 := by
  have hdiff : (a - b) - (b - c) = d - b := calc
    _ = (a + c) - (b + b) := by abel
    _ = d - b := by rw [h.diagonal_midpoints_eq]; abel
  have heq : ‖(a - b) + (b - c)‖ = ‖(a - b) - (b - c)‖ := by
    rw [sub_add_sub_cancel, hdiff, ← dist_eq_norm, ← dist_eq_norm, dist_comm d b]
    exact h.diagonal_lengths_eq
  have hs := congrArg (fun x : ℝ => x ^ 2) heq
  change ‖_ + _‖ ^ 2 = ‖_ - _‖ ^ 2 at hs
  rw [norm_add_sq_real (a - b) (b - c), norm_sub_sq_real (a - b) (b - c)] at hs
  linarith

/-- A uniform velocity estimate on an interval controls all its divided differences. -/
private lemma slope_near_velocity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} {U : Set ℝ} (hU : Convex ℝ U) (hd : Differentiable ℝ F) {v : E} {ε : ℝ} (hv : ∀ x ∈ U, ‖deriv F x - v‖ ≤ ε)
    {a b : ℝ} (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b) : ‖slope F a b - v‖ ≤ ε := by
  let G (x : ℝ) := F x - x • v
  have hG (x : ℝ) : HasDerivAt G (deriv F x - v) x := by
    simpa [G, Pi.sub_def] using (hd x).hasDerivAt.sub ((hasDerivAt_id x).smul_const v)
  have hmv := hU.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hG x).hasDerivWithinAt) hv ha hb
  have scale : (b - a) • (slope F a b - v) = G b - G a := by
    rw [smul_sub, sub_smul_slope, vsub_eq_sub, sub_smul]
    dsimp [G]
    abel
  rw [← scale, norm_smul] at hmv
  exact (le_of_mul_le_mul_left (by simpa only [mul_comm ε] using hmv)
    (norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)))

private lemma nearby_slopes_not_orthogonal {u v w : ℝ²} (hw : w ≠ 0)
    (hu : ‖u - w‖ ≤ ‖w‖ / 4) (hv : ‖v - w‖ ≤ ‖w‖ / 4) : ⟪u, v⟫_ℝ ≠ 0 := by
  intro h
  have hsmall := dist_triangle u w v
  rw [dist_comm w v, dist_eq_norm, dist_eq_norm, dist_eq_norm] at hsmall
  have hs := norm_sub_sq_real u v
  rw [h] at hs
  have hgap : ‖u - v‖ < ‖u‖ := by
    have htriangle : ‖w‖ ≤ ‖u - w‖ + ‖u‖ := by
      simpa [dist_eq_norm, norm_sub_rev] using (dist_triangle w u 0)
    linarith [norm_pos_iff.mpr hw]
  nlinarith [sq_nonneg ‖v‖, sq_lt_sq' (by linarith [norm_nonneg (u - v)]) hgap]

/-- Rectangles of varying aspect ratio survive a regular C¹ limit of parametrized curves.
The approximating curves enter only through their positions, velocities, and rectangles. -/
theorem rectangle_of_regular_limit {γ : Circle → ℝ²} (hγ : IsEmbedding γ)
    {f : ℕ → Circle → ℝ²} (hlim : TendstoUniformly f γ atTop)
    (hdiff : ∀ n, Differentiable ℝ (f n ∘ Circle.exp))
    (hvel : Continuous (deriv (γ ∘ Circle.exp))) (hreg : ∀ x, deriv (γ ∘ Circle.exp) x ≠ 0)
    (hdlim : TendstoUniformly (fun n => deriv (f n ∘ Circle.exp)) (deriv (γ ∘ Circle.exp)) atTop)
    {q : ℕ → ℝ} {r : ℝ} (hq : Tendsto q atTop (𝓝 r)) (hr : 0 < r)
    (hrect : ∀ n, ∃ t : Fin 4 → Circle,
      IsRectangle (f n (t 0)) (f n (t 1)) (f n (t 2)) (f n (t 3)) (q n)) :
    ∃ a b c d, IsRectangle (γ a) (γ b) (γ c) (γ d) r := by
  let velocity := deriv (γ ∘ Circle.exp)
  choose p hp using hrect
  obtain ⟨t, φ, hφ, ht⟩ := CompactSpace.tendsto_subseq p
  have ht' (i : Fin 4) : Tendsto (fun n => p (φ n) i) atTop (𝓝 (t i)) :=
    tendsto_pi_nhds.mp ht i
  let v (n : ℕ) (i : Fin 4) := f (φ n) (p (φ n) i)
  let w (i : Fin 4) := γ (t i)
  have hunif : TendstoUniformly (fun n => f (φ n)) γ atTop :=
    fun s hs => hφ.tendsto_atTop.eventually (hlim s hs)
  have hv (i : Fin 4) : Tendsto (fun n => v n i) atTop (𝓝 (w i)) :=
    hunif.tendsto_comp hγ.continuous.continuousAt (ht' i)
  have rect (n : ℕ) : IsRectangle (v n 0) (v n 1) (v n 2) (v n 3) (q (φ n)) := hp (φ n)
  have mid : w 0 + w 2 = w 1 + w 3 :=
    tendsto_nhds_unique_of_eventuallyEq ((hv 0).add (hv 2)) ((hv 1).add (hv 3))
      (.of_forall fun n => (rect n).diagonal_midpoints_eq)
  have diag : dist (w 0) (w 2) = dist (w 1) (w 3) :=
    tendsto_nhds_unique_of_eventuallyEq ((hv 0).dist (hv 2)) ((hv 1).dist (hv 3))
      (.of_forall fun n => (rect n).diagonal_lengths_eq)
  have ratio : dist (w 0) (w 1) = r * dist (w 1) (w 2) :=
    tendsto_nhds_unique_of_eventuallyEq ((hv 0).dist (hv 1))
      ((hq.comp hφ.tendsto_atTop).mul ((hv 1).dist (hv 2))) (.of_forall fun n =>
        (div_eq_iff (dist_ne_zero.mpr (rect n).b_ne_c)).mp (rect n).has_ratio)
  have hbc : w 1 ≠ w 2 := by
    intro he
    have hab : w 0 = w 1 := dist_eq_zero.mp (by simpa [he] using ratio)
    have tab : t 0 = t 1 := hγ.injective hab
    have tbc : t 1 = t 2 := hγ.injective he
    obtain ⟨θ, hθ⟩ := Circle.exp_surjective (t 1)
    let vel := velocity θ
    have hvelpos : 0 < ‖vel‖ := norm_pos_iff.mpr (hreg θ)
    obtain ⟨δ, hδ, hlocal⟩ := Metric.continuousAt_iff.mp (hvel.continuousAt (x := θ))
      (‖vel‖ / 8) (by positivity)
    let U := Metric.ball θ δ
    have hU : Circle.exp '' U ∈ 𝓝 (t 1) :=
      (isLocalHomeomorph_circleExp.isOpenMap _ Metric.isOpen_ball).mem_nhds
        ⟨θ, Metric.mem_ball_self hδ, hθ⟩
    have ha := (ht' 0).eventually (tab.symm ▸ hU)
    have hb := (ht' 1).eventually hU
    have hc := (ht' 2).eventually (tbc ▸ hU)
    have huniform := Metric.tendstoUniformly_iff.mp hdlim (‖vel‖ / 8) (by positivity)
    have impossible : ∀ᶠ _n : ℕ in atTop, False := by
      filter_upwards [ha, hb, hc, hφ.tendsto_atTop.eventually huniform] with n ha' hb' hc' hd'
      obtain ⟨a, haU, hax⟩ := ha'
      obtain ⟨b, hbU, hbx⟩ := hb'
      obtain ⟨c, hcU, hcx⟩ := hc'
      let F := f (φ n) ∘ Circle.exp
      have hA : F a = v n 0 := congrArg (f (φ n)) hax
      have hB : F b = v n 1 := congrArg (f (φ n)) hbx
      have hC : F c = v n 2 := congrArg (f (φ n)) hcx
      have hab' : a ≠ b := fun eq => (rect n).a_ne_b (hA.symm.trans ((congrArg F eq).trans hB))
      have hbc' : b ≠ c := fun eq => (rect n).b_ne_c (hB.symm.trans ((congrArg F eq).trans hC))
      have bound (x : ℝ) (hx : x ∈ U) : ‖deriv F x - vel‖ ≤ ‖vel‖ / 4 := by
        have small : dist (velocity x) (deriv F x) < ‖vel‖ / 8 := hd' x
        have close : dist (velocity x) vel < ‖vel‖ / 8 := hlocal hx
        rw [← dist_eq_norm]
        linarith [dist_triangle_left (deriv F x) vel (velocity x)]
      have hs := slope_near_velocity (convex_ball θ δ) (hdiff (φ n)) bound haU hbU hab'
      have hs' := slope_near_velocity (convex_ball θ δ) (hdiff (φ n)) bound hbU hcU hbc'
      apply nearby_slopes_not_orthogonal (hreg θ) hs hs'
      change ⟪slope F a b, slope F b c⟫_ℝ = 0
      rw [slope_def_module, slope_def_module, real_inner_smul_left, real_inner_smul_right,
        hA, hB, hC]
      have orth := rectangle_orthogonal (rect n)
      rw [← neg_sub (v n 0) (v n 1), ← neg_sub (v n 1) (v n 2), inner_neg_neg, orth]
      ring
    exact impossible.exists.elim fun _ hn => hn
  have hab : w 0 ≠ w 1 := dist_ne_zero.mp (ratio ▸ mul_ne_zero hr.ne' (dist_ne_zero.mpr hbc))
  exact ⟨t 0, t 1, t 2, t 3, mid, diag, hab, hbc,
    (div_eq_iff (dist_ne_zero.mpr hbc)).mpr ratio⟩

theorem main : H1 → H2 → type_of% @InscribedSquare.exists_inscribed_rectangle_of_smooth := by
  classical
  intro approx algebraic γ hγ r hr
  obtain ⟨P, hvel, hreg, hdiff, hlim, hdlim, hbound⟩ := approx γ hγ
  let f (n : ℕ) (z : Circle) : ℝ² := WithLp.toLp 2 (fun i : Fin 2 =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) ![(z : ℂ).re, (z : ℂ).im] (P n i))
  obtain ⟨q, _, hqr, hq⟩ := Real.exists_seq_rat_strictAnti_tendsto r
  have hpos (n : ℕ) : 0 < q n := by exact_mod_cast (hr.trans (hqr n))
  have hrect (n : ℕ) : ∃ t : Fin 4 → Circle,
      IsRectangle (f n (t 0)) (f n (t 1)) (f n (t 2)) (f n (t 3)) (q n : ℝ) :=
    algebraic (P n) (hbound n) (q n) (hpos n)
  exact rectangle_of_regular_limit hγ.isEmbedding hlim hdiff hvel hreg hdlim hq hr hrect

end OMA.R_InscribedSquare_exists_inscribed_rectangle_of_smooth_R2
