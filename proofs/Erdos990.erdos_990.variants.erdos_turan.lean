import FormalConjectures.ErdosProblems.«990»
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# The Erdős–Turán angular discrepancy bound

The theorem is due to Paul Erdős and Pál Turán (1950). Our proof radially
projects the roots, bounds angular power sums by symmetrizing the logarithm
of a disk polynomial, and smooths the counting interval by two box convolutions.
For related Fourier arguments see K. Soundararajan, “Equidistribution of zeros
of polynomials,” American Mathematical Monthly 126 (2019), 226–236.
-/

section Height990

/- For positive degree the coefficient height is at least two. -/
open Polynomial Finset
namespace OMA.Height990
theorem two_le (f : ℂ[X]) (h₀ : f.coeff 0 ≠ 0) (hd : 0 < f.natDegree) :
    2 ≤ Erdos990.M f := by
  classical
  have hf : f ≠ 0 := by intro h; simp [h] at h₀
  have ha := norm_pos_iff.mpr h₀
  have hb := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hf)
  have hsub : ({0,f.natDegree} : Finset ℕ) ⊆ range (f.natDegree+1) := by
    intro i hi
    rcases mem_insert.mp hi with rfl|hi
    · simp
    · rw [mem_singleton.mp hi]; simp
  have h := sum_le_sum_of_subset_of_nonneg (f:=fun i => ‖f.coeff i‖) hsub
    (fun i _ _ => norm_nonneg _)
  have hsum : ‖f.coeff 0‖+‖f.leadingCoeff‖ ≤ ∑ i∈range (f.natDegree+1), ‖f.coeff i‖ := by
    simpa only [sum_insert (by simpa using hd.ne : 0 ∉ ({f.natDegree}:Finset ℕ)),sum_singleton,coeff_natDegree] using h
  have hsq := Real.sq_sqrt (mul_nonneg ha.le hb.le)
  have hg : 2*Real.sqrt (‖f.coeff 0‖*‖f.leadingCoeff‖) ≤ ‖f.coeff 0‖+‖f.leadingCoeff‖ := by
    nlinarith only [hsq,sq_nonneg (‖f.coeff 0‖-‖f.leadingCoeff‖),Real.sqrt_nonneg (‖f.coeff 0‖*‖f.leadingCoeff‖),ha,hb,
      sq_nonneg (‖f.coeff 0‖+‖f.leadingCoeff‖-2*Real.sqrt (‖f.coeff 0‖*‖f.leadingCoeff‖))]
  exact (le_div_iff₀ (Real.sqrt_pos.mpr (mul_pos ha hb))).mpr (hg.trans hsum)

theorem one_le (f : ℂ[X]) (h₀ : f.coeff 0 ≠ 0) : 1 ≤ Erdos990.M f := by
  by_cases hd : 0 < f.natDegree
  · exact (by norm_num : (1:ℝ)≤2).trans (two_le f h₀ hd)
  · have hdeg : f.natDegree = 0 := by omega
    have hl : f.leadingCoeff = f.coeff 0 := by rw [← coeff_natDegree, hdeg]
    simp [Erdos990.M,hdeg,hl,←sq, norm_ne_zero_iff.mpr h₀]

end OMA.Height990

end Height990

section Roots990

/- Radial projection to the unit circle in the Erdős–Turán theorem.
The arithmetic mean of the squared radial errors is not needed: each
linear factor satisfies the comparison separately. -/

open Polynomial Finset
open scoped Real

namespace OMA.Roots990

noncomputable section

private def angle (z : ℂ) : ℝ :=
  if z.arg < 0 then z.arg + 2*π else z.arg

private theorem angle_range (z : ℂ) : angle z / (2*π) ∈ Set.Ico 0 1 := by
  have hp : 0 < 2*π := by positivity
  have ha := Complex.neg_pi_lt_arg z
  have hb := Complex.arg_le_pi z
  unfold angle
  split <;> constructor
  all_goals first | apply div_nonneg _ hp.le | apply (div_lt_one hp).2
  all_goals linarith [Real.pi_pos]

private theorem phase (z : ℂ) :
    fourier 1 ((angle z/(2*π) : ℝ) : AddCircle (1:ℝ)) = Complex.exp (z.arg * Complex.I) := by
  rw [fourier_coe_apply]
  have hp : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  rw [show 2 * (π:ℂ) * Complex.I * 1 * ((angle z:ℂ)/(2*π)) / 1 = (angle z:ℂ)*Complex.I by
    field_simp]
  unfold angle
  split
  · push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  · rfl

private theorem radial (w u : ℂ) (r : ℝ) (hr : 0 ≤ r) (hw : ‖w‖ = 1) (hu : ‖u‖ = 1) :
    Real.sqrt r * ‖1-w*star u‖ ≤ ‖w-r • u‖ := by
  have hunit : star u * u = 1 := by
    change (starRingEnd ℂ) u * u = 1
    simp [Complex.conj_mul',hu]
  have he : (1-w*star u)*u = u-w := by rw [sub_mul, one_mul, mul_assoc, hunit, mul_one]
  have he' := congrArg norm he
  rw [norm_mul, hu, mul_one, norm_sub_rev u w] at he'
  rw [he']
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).1
  rw [mul_pow, Real.sq_sqrt hr, norm_sub_sq_real, norm_sub_sq_real, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hw, hu]
  nlinarith [sq_nonneg (r-1)]

open scoped Classical in
theorem angles (f : ℂ[X]) (h₀ : f.coeff 0 ≠ 0) :
    ∃ x : Fin f.natDegree → ℝ, (∀ i, x i ∈ Set.Ico 0 1) ∧
      (∀ α β : ℝ, Erdos990.rootArgCount f (Set.Icc α β) =
        (univ.filter fun i => x i ∈ Set.Icc (α/(2*π)) (β/(2*π))).card) ∧
      ∀ w : ℂ, ‖w‖ = 1 →
        ∏ i, ‖1-w*star (fourier 1 ((x i:ℝ) : AddCircle (1:ℝ)))‖ ≤ Erdos990.M f := by
  classical
  have splitf := IsAlgClosed.splits f
  let e : Fin f.natDegree ≃ f.roots :=
    (Fintype.equivFinOfCardEq (by simpa using splitf.natDegree_eq_card_roots.symm)).symm
  let z (i : Fin f.natDegree) : ℂ := e i
  have hroots : univ.val.map z = f.roots := by
    calc
      _ = (univ.map e.toEmbedding).val.map (fun i : f.roots => (i:ℂ)) := by
        rw [map_val, Multiset.map_map]; rfl
      _ = _ := by rw [map_univ_equiv, Multiset.map_univ_coe]
  let x (i : Fin f.natDegree) := angle (z i)/(2*π)
  refine ⟨x, fun i => angle_range (z i), ?_, ?_⟩
  · intro α β
    unfold Erdos990.rootArgCount
    rw [← hroots, Multiset.countP_map]
    simp only [card, filter_val, x, angle, Set.mem_Icc,
      div_le_div_iff_of_pos_right (show 0 < 2*π by positivity)]
  · intro w hw
    have hp (i : Fin f.natDegree) :
        Real.sqrt ‖z i‖ * ‖1-w*star (fourier 1 ((x i:ℝ):AddCircle (1:ℝ)))‖ ≤ ‖w-z i‖ := by
      dsimp only [x]
      rw [phase]
      have h := radial w (Complex.exp ((z i).arg*Complex.I)) ‖z i‖ (norm_nonneg _) hw (by simp)
      simpa only [Complex.real_smul, Complex.norm_mul_exp_arg_mul_I] using h
    have hprod := prod_le_prod (s := (univ : Finset (Fin f.natDegree)))
      (fun i _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (fun i _ => hp i)
    rw [prod_mul_distrib] at hprod
    have hev (t : ℂ) : ‖f.eval t‖ = ‖f.leadingCoeff‖ * ∏ i, ‖t-z i‖ := by
      rw [splitf.eval_eq_prod_roots, ← hroots, Multiset.map_map, norm_mul]
      change _ * ‖∏ i, (t-z i)‖ = _
      rw [norm_prod]
    have hz : ‖f.coeff 0‖ = ‖f.leadingCoeff‖ * ∏ i, ‖z i‖ := by
      simpa [coeff_zero_eq_eval_zero] using hev 0
    have hf : f ≠ 0 := by intro he; simp [he] at h₀
    have hlead : 0 < ‖f.leadingCoeff‖ := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hf)
    have hden : 0 < Real.sqrt (‖f.coeff 0‖*‖f.leadingCoeff‖) :=
      Real.sqrt_pos.2 (mul_pos (norm_pos_iff.2 h₀) hlead)
    have hdenform : Real.sqrt (‖f.coeff 0‖*‖f.leadingCoeff‖) =
        ‖f.leadingCoeff‖ * ∏ i, Real.sqrt ‖z i‖ := by
      rw [hz, show ‖f.leadingCoeff‖ * (∏ i, ‖z i‖) * ‖f.leadingCoeff‖ =
        ‖f.leadingCoeff‖^2 * (∏ i, ‖z i‖) by ring, Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq hlead.le, Real.sqrt_prod _ (fun i _ => norm_nonneg _)]
    have hs : ‖f.eval w‖ ≤ ∑ i ∈ range (f.natDegree+1), ‖f.coeff i‖ := by
      rw [eval_eq_sum_range]
      simpa [norm_mul,norm_pow,hw] using
        norm_sum_le (range (f.natDegree+1)) (fun i => f.coeff i * w^i)
    apply (le_div_iff₀ hden).2
    rw [hdenform]
    calc
      _ = ‖f.leadingCoeff‖ * ((∏ i, Real.sqrt ‖z i‖) *
        ∏ i, ‖1-w*star (fourier 1 ((x i:ℝ):AddCircle (1:ℝ)))‖) := by ring
      _ ≤ ‖f.leadingCoeff‖ * ∏ i, ‖w-z i‖ := mul_le_mul_of_nonneg_left hprod hlead.le
      _ ≤ _ := (hev w).symm.le.trans hs

end

end OMA.Roots990

end Roots990

section Moment990

/- The Erdős–Turán angular moment estimate. Multiplying the disk polynomial
over all rotations by a kth root of unity replaces each root direction by its kth
power. The logarithm on the open disk has bounded real part; Schwarz's lemma
then bounds its first derivative, recovering the desired kth power sum. -/

open Finset Complex Metric Polynomial
open scoped Real

namespace OMA.Moment990

private theorem rotated_factors {k : ℕ} (hk : 0 < k) {s : ℂ} (hs : s ≠ 0) :
    ∏ ζ ∈ nthRootsFinset k (1 : ℂ), (1-s*ζ) = 1-s^k := by
  classical
  have hprim := Complex.isPrimitiveRoot_exp k hk.ne'
  have ev := congrArg (Polynomial.eval s⁻¹) (X_pow_sub_one_eq_prod hk hprim)
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at ev
  calc
    _ = ∏ ζ ∈ nthRootsFinset k (1 : ℂ), s*(s⁻¹-ζ) := by
      apply prod_congr rfl
      intro ζ _
      rw [mul_sub, mul_inv_cancel₀ hs]
    _ = s^k*((s⁻¹)^k-1) := by rw [prod_mul_distrib, prod_const, hprim.card_nthRootsFinset, ← ev]
    _ = _ := by rw [inv_pow, mul_sub, mul_inv_cancel₀ (pow_ne_zero _ hs), mul_one]

private theorem rotated_cap {n k : ℕ} (hk : 0 < k) (v : Fin n → ℂ) (hv : ∀ i, ‖v i‖ = 1)
    {M : ℝ} (cap : ∀ w : ℂ, ‖w‖ = 1 → ∏ i, ‖1-w*v i‖ ≤ M)
    (z : ℂ) (hz : ‖z‖ = 1) : ∏ i, ‖1-z*v i^k‖ ≤ M^k := by
  classical
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq z hk
  have hw1 : ‖w‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1
    (by rw [← norm_pow, hw, hz])
  let R := nthRootsFinset k (1 : ℂ)
  have cardR : R.card = k := (Complex.isPrimitiveRoot_exp k hk.ne').card_nthRootsFinset
  have unitR {ζ} (hζ : ζ ∈ R) : ‖ζ‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1
    (by rw [← norm_pow, (mem_nthRootsFinset hk _).mp hζ, norm_one])
  calc
    _ = ∏ i : Fin n, ∏ ζ ∈ R, ‖1-(w*ζ)*v i‖ := by
      apply prod_congr rfl
      intro i _
      have hwi : w*v i ≠ 0 := norm_ne_zero_iff.mp (by rw [norm_mul, hw1, hv, mul_one]; exact one_ne_zero)
      rw [← norm_prod, ← hw, ← mul_pow, ← rotated_factors hk hwi]
      congr 1
      apply prod_congr rfl
      intro ζ _
      ring
    _ = ∏ ζ ∈ R, ∏ i, ‖1-(w*ζ)*v i‖ := prod_comm
    _ ≤ ∏ _ζ ∈ R, M := by
      apply prod_le_prod (fun _ _ ↦ prod_nonneg fun _ _ ↦ norm_nonneg _)
      intro ζ hζ
      exact cap (w*ζ) (by rw [norm_mul, hw1, unitR hζ, mul_one])
    _ = M^k := by rw [prod_const, cardR]

private theorem log_derivative_bound (F : ℂ → ℂ) {D : ℂ} {C : ℝ} (hC : 0 < C)
    (diff : DifferentiableOn ℂ F (ball 0 1)) (der : HasDerivAt F D 0)
    (zero : F 0 = 0) (cap : ∀ z ∈ ball 0 1, (F z).re ≤ C) : ‖D‖ ≤ 2*C := by
  let g := fun z => F z / (2*(C:ℂ)-F z)
  have den {z} (hz : z ∈ ball 0 1) : 2*(C:ℂ)-F z ≠ 0 := by
    intro h
    have eq := congrArg Complex.re (sub_eq_zero.mp h)
    simp at eq
    linarith [cap z hz]
  have dg : DifferentiableOn ℂ g (ball 0 1) :=
    diff.div (diff.const_sub _) fun _ hz ↦ den hz
  have maps : Set.MapsTo g (ball 0 1) (closedBall (g 0) 1) := by
    intro z hz
    have hnorm : ‖F z‖ ≤ ‖2*(C:ℂ)-F z‖ := by
      rw [← sq_le_sq₀ (by positivity) (by positivity)]
      have bound := cap z hz
      simp only [Complex.sq_norm, Complex.normSq_apply, sub_re, mul_re, re_ofNat, ofReal_re,
        im_ofNat, zero_mul, sub_zero, sub_im, mul_im, ofReal_im, mul_zero, add_zero, zero_sub]
      nlinarith
    simpa [g, zero, norm_div] using (div_le_one_of_le₀ hnorm (norm_nonneg _))
  have d0 : HasDerivAt g (D/(2*(C:ℂ))) 0 := by
    have h := der.div (der.const_sub (2*(C:ℂ))) (den (by simp))
    change HasDerivAt (F/(fun z ↦ 2*(C:ℂ)-F z)) _ 0
    have h' : ((D*(2*(C:ℂ)-F 0)-F 0*(-D))/(2*(C:ℂ)-F 0)^2) = D/(2*(C:ℂ)) := by
      have cne : (C:ℂ) ≠ 0 := by exact_mod_cast hC.ne'
      rw [zero]; field_simp [cne]; ring
    rw [h'] at h
    exact h
  have h := Complex.norm_deriv_le_one_of_mapsTo_ball dg maps (by norm_num)
  rw [d0.deriv, norm_div, norm_mul, norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hC] at h
  exact (div_le_one (by positivity)).mp h

private theorem power_sum {n k : ℕ} (hk : 0 < k) (v : Fin n → ℂ) (hv : ∀ i, ‖v i‖ = 1)
    {M : ℝ} (hM : 1 < M)
    (cap : ∀ w : ℂ, ‖w‖ = 1 → ∏ i, ‖1-w*v i‖ ≤ M) :
    ‖∑ i, v i^k‖ ≤ k * (2*Real.log M) := by
  classical
  let u := fun i ↦ v i^k
  let F := fun z : ℂ ↦ ∑ i, Complex.log (1-z*u i)
  have hu : ∀ i, ‖u i‖=1 := fun i ↦ by simp [u, norm_pow, hv]
  have cut (i) (z) (hz : z ∈ ball 0 1) : 1-z*u i ∈ Complex.slitPlane := by
    apply Or.inl
    simp only [sub_re, one_re]
    have h := Complex.re_le_norm (z*u i)
    rw [norm_mul, hu, mul_one] at h
    linarith [mem_ball_zero_iff.mp hz]
  have hd (i : Fin n) (z : ℂ) : HasDerivAt (fun t : ℂ ↦ 1-t*u i) (-u i) z := by
    simpa using (((hasDerivAt_id z).mul_const (u i)).const_sub 1)
  have hF : DifferentiableOn ℂ F (ball 0 1) := by
    apply DifferentiableOn.fun_sum
    intro i _
    apply DifferentiableOn.clog _ (cut i)
    exact fun z _ ↦ (hd i z).differentiableAt.differentiableWithinAt
  have hder : HasDerivAt F (∑ i, -u i) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    simpa using (hd i 0).clog (cut i 0 (by simp))
  have hcap (z) (hz : z ∈ ball 0 1) : (F z).re ≤ k * Real.log M := by
    have inner : ‖∏ i, (1-z*u i)‖ ≤ M^k := by
      apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0:ℂ) 1) Metric.isBounded_ball
        (f := fun t : ℂ ↦ ∏ i, (1-t*u i)) (Differentiable.diffContOnCl (by fun_prop)) _ (subset_closure hz)
      intro t ht
      rw [frontier_ball _ one_ne_zero, mem_sphere, dist_zero_right] at ht
      simpa only [norm_prod] using rotated_cap hk v hv cap t ht
    have pos (i) : 0 < ‖1-z*u i‖ := norm_pos_iff.mpr (Complex.slitPlane_ne_zero (cut i z hz))
    rw [norm_prod] at inner
    simpa only [F, Complex.re_sum, Complex.log_re, ← Real.log_prod (fun i _ ↦ (pos i).ne'),
      Real.log_pow] using Real.log_le_log (prod_pos fun i _ ↦ pos i) inner
  have h := log_derivative_bound F (C := k*Real.log M)
    (mul_pos (by exact_mod_cast hk) (Real.log_pos hM)) hF hder (by simp [F]) hcap
  rw [Finset.sum_neg_distrib, norm_neg] at h
  exact h.trans_eq (by ring)

/-- Boundary control of the product gives linear growth of all angular Fourier moments. -/
theorem modes {n : ℕ} (x : Fin n → ℝ) {M : ℝ} (hM : 1 < M)
    (cap : ∀ w : ℂ, ‖w‖ = 1 → ∏ i, ‖1-w*star (fourier 1 ((x i:ℝ):AddCircle (1:ℝ)))‖ ≤ M)
    (k : ℕ) (hk : 0 < k) :
    ‖∑ i, fourier (k:ℤ) ((x i:ℝ):AddCircle (1:ℝ))‖ ≤ (k:ℝ)*(2*Real.log M) := by
  let v := fun i ↦ star (fourier 1 ((x i:ℝ):AddCircle (1:ℝ)))
  have hv : ∀ i, ‖v i‖ = 1 := by intro i; rw [show v i = _ from rfl, norm_star]; exact Circle.norm_coe _
  have h := power_sum hk v hv hM cap
  have eq (i) : v i^k = star (fourier (k:ℤ) ((x i:ℝ):AddCircle (1:ℝ))) := by
    simp [v, fourier_apply, AddCircle.toCircle_nsmul]
  simpa only [eq, ← star_sum, norm_star] using h

end OMA.Moment990

end Moment990

section ArcSpline990

/- Compact quadratic majorants for closed arcs, obtained by smoothing an expanded
interval twice with a box. -/
namespace OMA.ArcSpline990
open Real Set MeasureTheory Complex
open scoped Convolution FourierTransform

noncomputable def box (a b : ℝ) : ℝ → ℝ := (Icc a b).indicator 1

private theorem box_nonneg (a b x : ℝ) : 0 ≤ box a b x := by
  by_cases h : x∈Icc a b <;> simp [box,h]

private theorem box_int (a b : ℝ) : Integrable (box a b) :=
  (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))

private theorem box_comp (a b : ℝ) : HasCompactSupport (box a b) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (Set.support_indicator_subset ..)

private theorem box_mass {a b : ℝ} (h : a≤b) : ∫ t, box a b t = b-a := by
  rw [box,integral_indicator_one measurableSet_Icc,Real.volume_real_Icc_of_le h]

noncomputable def tent (h : ℝ) := box 0 h ⋆ box 0 h

private theorem tent_eq (h x : ℝ) :
    tent h x = max (min h x - max 0 (x-h)) 0 := by
  change (∫ y, box 0 h y * box 0 h (x-y)) = _
  have e (y : ℝ) : box 0 h y * box 0 h (x-y) = box (max 0 (x-h)) (min h x) y := by
    have mem : y ∈ Icc (max 0 (x-h)) (min h x) ↔ y∈Icc 0 h ∧ x-y∈Icc 0 h := by
      simp only [mem_Icc, max_le_iff, le_min_iff]
      constructor <;> rintro ⟨⟨_,_⟩,⟨_,_⟩⟩ <;> constructor <;> constructor <;> linarith
    by_cases p : y∈Icc 0 h <;> by_cases q : x-y∈Icc 0 h <;> simp [box,mem,p,q]
  simp_rw [e,box]
  rw [integral_indicator_one measurableSet_Icc,Real.volume_real_Icc]

private theorem tent_cont (h : ℝ) : Continuous (tent h) := by
  simp_rw [funext (tent_eq h)]
  fun_prop

private theorem tent_supp (h : ℝ) : Function.support (tent h) ⊆ Icc 0 (2*h) := by
  intro x hx
  by_contra outside
  change tent h x ≠ 0 at hx
  rw [tent_eq] at hx
  apply hx
  apply max_eq_right
  simp only [mem_Icc,not_and_or,not_le] at outside
  rcases outside with hn|hn
  · linarith [min_le_right h x,le_max_left 0 (x-h)]
  · linarith [min_le_left h x,le_max_right 0 (x-h)]

private theorem tent_mass {h : ℝ} (hh : 0≤h) : ∫ x, tent h x = h^2 := by
  rw [tent,integral_convolution _ (box_int ..) (box_int ..),box_mass hh]
  change (h-0)*(h-0)=h^2
  ring

noncomputable def majorant (a b h : ℝ) := tent h ⋆ box (a-2*h) b

theorem majorant_comp (a b h : ℝ) : HasCompactSupport (majorant a b h) :=
  ((box_comp 0 h).convolution _ (box_comp 0 h)).convolution _ (box_comp ..)

theorem majorant_cont (a b h : ℝ) : Continuous (majorant a b h) :=
  ((box_comp 0 h).convolution _ (box_comp 0 h)).continuous_convolution_left _ (tent_cont h)
    (box_int ..).locallyIntegrable

theorem majorant_nn (a b h x : ℝ) : 0 ≤ majorant a b h x := by
  apply integral_nonneg
  intro y
  change 0 ≤ tent h y * box (a-2*h) b (x-y)
  rw [tent_eq]
  exact mul_nonneg (le_max_right ..) (box_nonneg ..)

theorem majorant_eq {a b h x : ℝ} (hh : 0≤h) (hx : x∈Icc a b) :
    majorant a b h x = h^2 := by
  rw [←tent_mass hh]
  apply integral_congr_ae
  filter_upwards [] with y
  change tent h y * box (a-2*h) b (x-y)=tent h y
  by_cases e : tent h y=0
  · simp [e]
  · obtain ⟨hy,hy'⟩ := tent_supp h (show y∈Function.support (tent h) from e)
    have m : x-y∈Icc (a-2*h) b := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    simp [box,m]

private theorem cast_convolution (f g : ℝ → ℝ) (x : ℝ) :
    ((f ⋆ g) x : ℂ) = ((fun y => (f y:ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
      (fun y => (g y:ℂ))) x := by
  change ((∫ y, f y*g (x-y):ℝ):ℂ) = ∫ y, (f y:ℂ)*(g (x-y):ℂ)
  rw [←integral_complex_ofReal]
  simp

private noncomputable def cbox (a b x : ℝ) : ℂ := box a b x

private theorem cbox_int (a b : ℝ) : Integrable (cbox a b) := (box_int a b).ofReal

theorem majorant_ft (a b h ξ : ℝ) :
    𝓕 (fun x => (majorant a b h x:ℂ)) ξ =
      (𝓕 (cbox 0 h) ξ)^2 * 𝓕 (cbox (a-2*h) b) ξ := by
  rw [show (fun x => (majorant a b h x:ℂ)) =
      (fun x => (tent h x:ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] cbox (a-2*h) b by
        exact funext (fun x => cast_convolution _ _ x)]
  have ih : Integrable (tent h) :=
    (box_int 0 h).integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) (box_int 0 h)
  have ic : Integrable (fun x => (tent h x:ℂ)) := ih.ofReal
  rw [Real.fourier_mul_convolution_eq ic (cbox_int (a-2*h) b) ξ]
  rw [show (fun x => (tent h x:ℂ)) = cbox 0 h ⋆[ContinuousLinearMap.mul ℂ ℂ] cbox 0 h by
      exact funext (fun x => cast_convolution _ _ x)]
  rw [Real.fourier_mul_convolution_eq (cbox_int 0 h) (cbox_int 0 h) ξ,sq]

private theorem cbox_formula {a b : ℝ} (ab : a≤b) (ξ : ℝ) :
    𝓕 (cbox a b) ξ = ∫ t in a..b, Complex.exp (((-2*Real.pi*ξ:ℝ):ℂ)*Complex.I*t) := by
  rw [Real.fourier_real_eq_integral_exp_smul,intervalIntegral.integral_of_le ab,←integral_Icc_eq_integral_Ioc,
    ←integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases m : t∈Icc a b
  · simp only [cbox,box,Set.indicator_of_mem m,Pi.one_apply,Complex.ofReal_one,smul_eq_mul,mul_one]
    congr 1; push_cast; ring
  · simp [cbox,box,m]

private theorem Fourier_zero_box {a b : ℝ} (ab : a≤b) : 𝓕 (cbox a b) 0 = (b-a:ℝ) := by
  rw [cbox_formula ab]
  simp

private theorem box_small {a b : ℝ} (ab : a≤b) (ξ : ℝ) : ‖𝓕 (cbox a b) ξ‖ ≤ b-a := by
  rw [cbox_formula ab]
  calc
    _ ≤ 1*|b-a| := intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => by
      simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im])
    _ = _ := by rw [one_mul,abs_of_nonneg (sub_nonneg.mpr ab)]

private theorem box_decay {a b ξ : ℝ} (ab : a≤b) (nz : ξ ≠ 0) : ‖𝓕 (cbox a b) ξ‖ ≤ 1/|ξ| := by
  let c : ℂ := ((-2*Real.pi*ξ:ℝ):ℂ)*Complex.I
  have nc : c≠0 := by dsimp [c]; exact mul_ne_zero (by exact_mod_cast mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) nz) Complex.I_ne_zero
  have unit (t : ℝ) : ‖Complex.exp (c*t)‖=1 := by simp [c, Complex.norm_exp,Complex.mul_re,Complex.mul_im]
  rw [cbox_formula ab,integral_exp_mul_complex nc, norm_div]
  calc
    _ ≤ 2/‖c‖ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      exact (norm_sub_le _ _).trans (by rw [unit,unit]; norm_num)
    _ ≤ _ := by
      simp only [c,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_neg,abs_of_pos Real.pi_pos,
        Complex.norm_I,mul_one]
      rw [div_le_div_iff₀ (by positivity) (abs_pos.mpr nz)]
      rw [abs_of_nonneg (by norm_num : (0:ℝ)≤2),one_mul]
      nlinarith [mul_nonneg (show 0≤Real.pi-1 by linarith [Real.pi_gt_three]) (abs_nonneg ξ)]

theorem zero {a b h : ℝ} (ab : a≤b) (hh : 0≤h) :
    𝓕 (fun x => (majorant a b h x:ℂ)) 0 = ((h^2*(b-a+2*h):ℝ):ℂ) := by
  rw [majorant_ft,Fourier_zero_box hh,Fourier_zero_box (by linarith)]
  push_cast; ring

theorem bounds {a b h ξ : ℝ} (ab : a≤b) (hh : 0≤h) (nz : ξ≠0) :
    ‖𝓕 (fun x => (majorant a b h x:ℂ)) ξ‖ ≤
      min (h^2/|ξ|) (1/|ξ|^3) := by
  rw [majorant_ft,norm_mul,norm_pow]
  have A := box_decay (show a-2*h≤b by linarith) nz
  have H := box_decay hh nz
  have H' : ‖𝓕 (cbox 0 h) ξ‖ ≤ h := by simpa using box_small hh ξ
  have p := abs_pos.mpr nz
  apply le_min
  · convert mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) H' 2) A (norm_nonneg _) (sq_nonneg h) using 1; ring
  · convert mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) H 2) A (norm_nonneg _) (sq_nonneg _) using 1; ring

end OMA.ArcSpline990

end ArcSpline990

section ArcWeight990

/- The Fourier weight for smoothed arcs: split the positive modes at
the smoothing scale and telescope the inverse-square tail. -/

namespace OMA.ArcWeight990

open Finset

noncomputable def weight (m : ℕ) (k : ℤ) : ℝ :=
  min ((1/(m:ℝ))^2/|(k:ℝ)|) (1/|(k:ℝ)|^3)

theorem bound (m : ℕ) (hm : 0 < m) :
    Summable (weight m) ∧ Summable (fun k : ℤ => |(k:ℝ)| * weight m k) ∧
      (∑' k : ℤ, |(k:ℝ)| * weight m k) ≤ 4*(1/(m:ℝ)) := by
  let h := 1/(m:ℝ)
  let F (k : ℤ) := |(k:ℝ)| * weight m k
  let g (n : ℕ) := F ((n:ℤ)+1)
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have gw (n : ℕ) : g n =
      ((n:ℝ)+1) * min (h^2 / ((n:ℝ)+1)) (1 / ((n:ℝ)+1)^3) := by
    simp [g,F,weight,h,abs_of_pos (show 0 < (n:ℝ)+1 by positivity)]
  have hg (n : ℕ) : 0 ≤ g n := by rw [gw]; positivity
  have head' (n : ℕ) : g n ≤ h^2 := by
    rw [gw]
    calc
      _ ≤ ((n:ℝ)+1)*(h^2/((n:ℝ)+1)) := by gcongr; exact min_le_left _ _
      _ = _ := by field_simp
  have tail' (j : ℕ) :
      g (m+j) ≤ 1/((m:ℝ)+j) - 1/((m:ℝ)+j+1) := by
    rw [gw, Nat.cast_add]
    have hv : 0 < (m:ℝ) + j := by positivity
    generalize (m:ℝ) + j = v at hv ⊢
    have hv' : 0 < v+1 := by positivity
    calc
      _ ≤ (v+1)*(1/(v+1)^3) := by gcongr; exact min_le_right _ _
      _ ≤ _ := by field_simp; nlinarith [sq_nonneg v]
  have tail (l : ℕ) : ∑ j ∈ range l, g (m+j) ≤ h - 1/((m:ℝ)+l) := by
    induction l with
    | zero => simp [h]
    | succ l ih =>
      rw [sum_range_succ]
      push_cast
      rw [← add_assoc (m:ℝ)]
      linarith [tail' l]
  have partials (n : ℕ) : ∑ j ∈ range n, g j ≤ 2*h := by
    calc
      _ ≤ ∑ j ∈ range (m+n), g j :=
        sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun i _ _ => hg i)
      _ = (∑ j ∈ range m, g j) + ∑ j ∈ range n, g (m+j) := sum_range_add g _ _
      _ ≤ (∑ _j ∈ range m, h^2) + (h-1/((m:ℝ)+n)) :=
        add_le_add (sum_le_sum fun j _ => head' j) (tail n)
      _ ≤ _ := by
        simp only [sum_const, card_range, nsmul_eq_mul]
        have he : (m:ℝ)*h^2 = h := by dsimp [h]; field_simp
        rw [he]
        linarith [show 0 ≤ 1/((m:ℝ)+n) by positivity]
  have hsum : Summable g := summable_of_sum_range_le hg partials
  have htsum := Real.tsum_le_of_sum_range_le hg partials
  have hneg (j : ℤ) : F (-j) = F j := by simp [F,weight]
  have hsum' : Summable (fun n : ℕ => F (-((n:ℤ)+1))) := by simpa only [hneg] using hsum
  have hF : Summable F := Summable.of_add_one_of_neg_add_one hsum hsum'
  refine ⟨Summable.of_nonneg_of_le (fun k => by unfold weight; positivity) ?_ hF,hF,?_⟩
  · intro k
    rcases eq_or_ne k 0 with rfl | hk
    · simp [F,weight]
    · have hk' : 1 ≤ |(k:ℝ)| := by exact_mod_cast Int.one_le_abs hk
      exact le_mul_of_one_le_left (by unfold weight; positivity) hk'
  · change (∑' k, F k) ≤ 4*h
    rw [tsum_of_add_one_of_neg_add_one hsum hsum']
    simp only [hneg, show F 0 = 0 by simp [F], add_zero]
    change (∑' n, g n) + (∑' n, g n) ≤ 4*h
    linarith

end OMA.ArcWeight990

end ArcWeight990

section Period990

/- Periodizing a compactly supported majorant for an interval. -/
open Asymptotics Filter Function MeasureTheory
open scoped FourierTransform Topology
namespace OMA.Period990

private theorem zero_off (f : C(ℝ,ℂ)) (hf : HasCompactSupport f) :
    (f:ℝ→ℂ) =ᶠ[cocompact ℝ] (fun _ => 0) := by
  have z := hasCompactSupport_iff_eventuallyEq.mp hf
  rw [Filter.coclosedCompact_eq_cocompact] at z
  exact z

theorem translates (f : C(ℝ,ℂ)) (hf : HasCompactSupport f) (x:ℝ) :
    Summable (fun n:ℤ => f (x+n)) := by
  have zz := zero_off (f.comp ⟨Homeomorph.addLeft x,(Homeomorph.addLeft x).continuous⟩)
    (hf.comp_homeomorph (Homeomorph.addLeft x))
  have h : ∀ᶠ n : ℤ in cofinite, f (x+n) = 0 :=
    zz.comp_tendsto Int.tendsto_coe_cofinite
  exact summable_of_hasFiniteSupport (show (Function.support (fun n:ℤ => f (x+n))).Finite by
    exact h)

theorem series (f : C(ℝ,ℂ)) (hf : HasCompactSupport f)
    (hs : Summable (fun n:ℤ => 𝓕 (f:ℝ→ℂ) (n:ℝ))) (x:ℝ) :
    HasSum (fun n:ℤ => 𝓕 (f:ℝ→ℂ) (n:ℝ) * fourier n (x:UnitAddCircle))
      (∑' k:ℤ, f (x+k)) := by
  have decay : (f:ℝ→ℂ) =O[cocompact ℝ] (fun x:ℝ => |x| ^ (-(2:ℝ))) :=
    (Asymptotics.isBigO_congr (zero_off f hf) .rfl).mpr (Asymptotics.isBigO_zero _ _)
  rw [Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable f.continuous (by norm_num : (1:ℝ)<2) decay hs]
  apply Summable.hasSum
  apply Summable.of_norm
  simpa only [norm_mul,show ∀ n:ℤ, ‖fourier n (x:UnitAddCircle)‖=1 from fun _ => Circle.norm_coe _,mul_one] using hs.norm

theorem translate_le (f : C(ℝ,ℂ)) (hf : HasCompactSupport f)
    (nonneg : ∀ y, 0≤(f y).re) (x:ℝ) (j:ℤ) :
    (f (x+j)).re ≤ (∑' k:ℤ, f (x+k)).re := by
  have t := translates f hf x
  rw [Complex.re_tsum t]
  exact (Complex.reCLM.hasSum t.hasSum).summable.le_tsum j (fun k _ => nonneg (x+k))

theorem period_nonneg (f : C(ℝ,ℂ)) (hf : HasCompactSupport f)
    (nonneg : ∀ y, 0≤(f y).re) (x:ℝ) : 0≤(∑' k:ℤ, f (x+k)).re :=
  (nonneg _).trans (translate_le f hf nonneg x 0)

end OMA.Period990

end Period990

section Arc990

/- Bound the counting error on an arc by applying the compact majorant at
each input point and summing its Fourier series. -/
namespace OMA.Arc990
open Finset Set Complex
open scoped FourierTransform ComplexConjugate Classical

private theorem modes {n : ℕ} (x : Fin n → ℝ) {L : ℝ}
    (ctrl : ∀ k : ℕ, 0<k → ‖∑ i, fourier (k:ℤ) ((x i:ℝ):UnitAddCircle)‖ ≤ k*L)
    {k : ℤ} (nz : k ≠ 0) :
    ‖∑ i, fourier k ((x i:ℝ):UnitAddCircle)‖ ≤ |(k:ℝ)| *L := by
  cases k with
  | ofNat k =>
    have hk : k≠0 := by intro hz; subst k; exact nz rfl
    simpa only [Int.ofNat_eq_natCast,Int.cast_natCast,Nat.abs_cast] using ctrl k (Nat.pos_of_ne_zero hk)
  | negSucc k =>
    rw [show Int.negSucc k = -((k+1:ℕ):ℤ) by omega]
    simpa only [fourier_neg,←map_sum,Complex.norm_conj,Int.cast_neg,abs_neg,Int.cast_natCast,Nat.abs_cast]
      using ctrl (k+1) (by omega)

private theorem estimate {n : ℕ} (x : Fin n → ℝ) {L a b h : ℝ} (hL : 0≤L)
    (ab : a≤b) (hh : 0≤h)
    (ctrl : ∀ k : ℕ, 0<k → ‖∑ i, fourier (k:ℤ) ((x i:ℝ):UnitAddCircle)‖ ≤ k*L)
    (B : ℤ → ℝ) (hB : Summable B) (wB : Summable (fun k:ℤ => |(k:ℝ)| *B k))
    (cap : (∑' k:ℤ, |(k:ℝ)| *B k) ≤ 4*h) (pos : ∀ k, 0≤B k)
    (maj : ∀ k : ℤ, k≠0 → min (h^2/|(k:ℝ)|) (1/|(k:ℝ)|^3) ≤ B k) :
    h^2*((univ.filter fun i => x i ∈ Icc a b).card:ℝ) ≤
      (n:ℝ)*h^2*(b-a+2*h)+4*h*L := by
  let f : C(ℝ,ℂ) := ⟨fun t => (OMA.ArcSpline990.majorant a b h t:ℂ),
    Complex.continuous_ofReal.comp (OMA.ArcSpline990.majorant_cont a b h)⟩
  have fc : HasCompactSupport f := (OMA.ArcSpline990.majorant_comp a b h).comp_left (by simp : ((0:ℝ):ℂ)=0)
  have fn (t : ℝ) : 0 ≤ (f t).re := OMA.ArcSpline990.majorant_nn ..
  let c (k : ℤ) := 𝓕 (f:ℝ→ℂ) (k:ℝ)
  let E (k : ℤ) := ∑ i, fourier k ((x i:ℝ):UnitAddCircle)
  have c0 : c 0 = ((h^2*(b-a+2*h):ℝ):ℂ) := by
    simpa only [c,f,ContinuousMap.coe_mk,Int.cast_zero] using OMA.ArcSpline990.zero ab hh
  have bound (k : ℤ) (nz : k≠0) : ‖c k‖ ≤ B k :=
    (OMA.ArcSpline990.bounds ab hh (by exact_mod_cast nz : (k:ℝ)≠0)).trans (maj k nz)
  have cs : Summable c := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) (f := fun k => B k + if k=0 then ‖c 0‖ else 0)
    · intro k
      by_cases eq : k=0
      · subst k; simp [pos]
      · simpa [eq] using bound k eq
    · exact hB.add (hasSum_ite_eq 0 _).summable
  let V (i : Fin n) := ∑' k:ℤ, f (x i+k)
  have sums : HasSum (fun k => c k*E k) (∑ i, V i) := by
    simpa only [c,E,Finset.mul_sum] using
      (hasSum_sum (s:=univ) (fun i _ => OMA.Period990.series f fc cs (x i)))
  have ex : HasSum (fun k:ℤ => c k*E k - if k=0 then c 0*E 0 else 0)
      ((∑ i, V i)-c 0*E 0) := sums.sub (hasSum_ite_eq _ _)
  have cmp (k : ℤ) : (c k*E k - if k=0 then c 0*E 0 else 0).re ≤ (|(k:ℝ)| *B k)*L := by
    by_cases nz : k=0
    · simp [nz]
    rw [if_neg nz, sub_zero]
    calc _ ≤ ‖c k*E k‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
         _ = ‖c k‖*‖E k‖ := norm_mul _ _
         _ ≤ B k * (|(k:ℝ)| *L) :=
           mul_le_mul (bound k nz) (modes x ctrl nz) (norm_nonneg _) (pos k)
         _ = _ := by ring
  have err := hasSum_le cmp (Complex.reCLM.hasSum ex) (wB.hasSum.mul_right L)
  have Ez : E 0 = (n:ℂ) := by simp [E]
  change ((∑ i, V i)-c 0*E 0).re ≤ (∑' k:ℤ, |(k:ℝ)| *B k)*L at err
  rw [c0,Ez] at err
  simp only [Complex.sub_re,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.re_sum] at err
  have cut : h^2*((univ.filter fun i => x i∈Icc a b).card:ℝ) ≤ ∑ i, (V i).re := by
    rw [Finset.card_filter,Nat.cast_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases inside : x i∈Icc a b
    · simp only [if_pos inside,Nat.cast_one,mul_one]
      have lower := OMA.Period990.translate_le f fc fn (x i) 0
      rw [Int.cast_zero,add_zero] at lower
      change OMA.ArcSpline990.majorant a b h (x i) ≤ _ at lower
      rwa [OMA.ArcSpline990.majorant_eq hh inside] at lower
    · simpa [inside,V] using OMA.Period990.period_nonneg f fc fn (x i)
  linarith [mul_le_mul_of_nonneg_right cap hL]

private theorem upper {n : ℕ} (x : Fin n → ℝ) {L a b : ℝ} (hn : 0<n) (hL : 0<L)
    (ab : a≤b)
    (ctrl : ∀ k : ℕ, 0<k → ‖∑ i, fourier (k:ℤ) ((x i:ℝ):UnitAddCircle)‖ ≤ k*L) :
    ((univ.filter fun i => x i∈Icc a b).card:ℝ) ≤ (b-a)*n + 10*Real.sqrt (n*L) := by
  let K : ℝ := (univ.filter fun i => x i∈Icc a b).card
  have kn : K ≤ n := by
    dsimp [K]
    exact_mod_cast (Finset.card_filter_le Finset.univ (fun i => x i∈Icc a b)).trans_eq (Fintype.card_fin n)
  have np : (0:ℝ)<n := by exact_mod_cast hn
  have nn : 0≤(b-a)*(n:ℝ) := mul_nonneg (sub_nonneg.mpr ab) np.le
  by_cases small : (n:ℝ)≤L
  · have le : (n:ℝ) ≤ Real.sqrt (n*L) := (Real.le_sqrt np.le (mul_nonneg np.le hL.le)).mpr (by
      nlinarith [mul_le_mul_of_nonneg_left small np.le])
    change K ≤ _
    linarith
  let t := Real.sqrt (n/L)
  have ts : t^2=(n:ℝ)/L := Real.sq_sqrt (div_nonneg np.le hL.le)
  have tp : 0<t := Real.sqrt_pos.mpr (div_pos np hL)
  have nident : (n:ℝ)=L*t^2 := by rw [ts]; field_simp
  have t1 : 1≤t := by
    have h1 : 1≤(n:ℝ)/L := (le_div_iff₀ hL).mpr (by linarith)
    nlinarith
  let m := ⌈t⌉₊
  have tlo : t ≤ m := Nat.le_ceil t
  have mpos : 0 < m := by exact_mod_cast tp.trans_le tlo
  have mup : (m:ℝ)≤2*t := by linarith [show (m:ℝ)<t+1 from Nat.ceil_lt_add_one tp.le]
  let h := 1/(m:ℝ)
  have hp : 0<h := one_div_pos.mpr (by exact_mod_cast mpos)
  obtain ⟨sb,sw,cap⟩ := OMA.ArcWeight990.bound m mpos
  have est := estimate x hL.le ab hp.le ctrl (OMA.ArcWeight990.weight m) sb sw cap
    (fun k => by dsimp [OMA.ArcWeight990.weight]; positivity) (fun _ _ => le_rfl)
  change h^2*K ≤ (n:ℝ)*h^2*(b-a+2*h)+4*h*L at est
  have mh : (m:ℝ)*h=1 := by dsimp [h]; field_simp
  have lo : K ≤ (n:ℝ)*(b-a)+2*n*h+4*m*L := by
    apply (le_of_mul_le_mul_left (a:=h^2) _ (sq_pos_of_pos hp))
    calc
      _ ≤ _ := est
      _ = _ := by linear_combination -4*h*L*(mh)
  have first : (n:ℝ)*h≤L*t := by
    change (n:ℝ)*(1/(m:ℝ))≤L*t
    rw [mul_one_div,div_le_iff₀ (by exact_mod_cast mpos : (0:ℝ) < m)]
    rw [nident]
    nlinarith [mul_le_mul_of_nonneg_left tlo (mul_nonneg hL.le tp.le)]
  have eq : Real.sqrt (n*L) = L*t := by
    rw [nident,show L*t^2*L=(L*t)^2 by ring,Real.sqrt_sq (mul_nonneg hL.le tp.le)]
  change K ≤ _
  rw [eq]
  nlinarith [mul_le_mul_of_nonneg_right mup hL.le]

/-- The arc-discrepancy estimate for a family whose kth Fourier moment is at
most kL. Closed arcs, including singletons and the full interval, are allowed. -/
theorem discrepancy {n : ℕ} (x : Fin n → ℝ) (hn : 0<n)
    (hx : ∀ i, 0≤x i ∧ x i<1) {L : ℝ} (hL : 0<L)
    (ctrl : ∀ k : ℕ, 0<k → ‖∑ i, fourier (k:ℤ) ((x i:ℝ):UnitAddCircle)‖ ≤ k*L)
    (a b : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1) :
    |((univ.filter fun i => x i∈Icc a b).card:ℝ) - (b-a)*n| ≤ 20*Real.sqrt (n*L) := by
  let count (u v : ℝ) := (univ.filter (fun i => x i∈Icc u v)).card
  have cover : n ≤ count 0 a + count a b + count b 1 := by
    change n ≤ ((univ.filter _).card + (univ.filter _).card + (univ.filter _).card)
    simp only [Finset.card_filter,←Finset.sum_add_distrib]
    calc n = ∑ _i : Fin n, 1 := by simp
         _ ≤ _ := Finset.sum_le_sum (fun i _ => by
           obtain ⟨lo,hi⟩ := hx i
           by_cases h : x i≤a
           · have m : x i∈Icc 0 a := ⟨lo,h⟩
             simp only [if_pos m]; omega
           · by_cases h' : x i≤b
             · have m : x i∈Icc a b := ⟨le_of_not_ge h,h'⟩
               simp only [if_pos m]; omega
             · have m : x i∈Icc b 1 := ⟨le_of_not_ge h',hi.le⟩
               simp only [if_pos m]; omega)
  have up (u v : ℝ) (huv : u≤v) : (count u v:ℝ) ≤ (v-u)*n+10*Real.sqrt (n*L) :=
    upper x hn hL huv ctrl
  have cover' : (n:ℝ) ≤ (count 0 a:ℝ)+count a b+count b 1 := by exact_mod_cast cover
  change |(count a b:ℝ)-(b-a)*n| ≤ _
  exact abs_le.mpr ⟨by linarith [up 0 a ha,up b 1 hb],by linarith [up a b hab,Real.sqrt_nonneg ((n:ℝ)*L)]⟩

end OMA.Arc990

end Arc990

section Finish990

/- Scale angles back to radians and combine the bounds. -/
open scoped Real

theorem OMA.solution : type_of% @Erdos990.erdos_990.variants.erdos_turan := by
  classical
  refine ⟨20*Real.sqrt 2, ?_⟩
  intro f h₀ α β hα hαβ hβ
  obtain ⟨x, hx, count, cap⟩ := OMA.Roots990.angles f h₀
  rw [count]
  by_cases hn : 0 < f.natDegree
  · have hp : 0 < 2*π := by positivity
    have hM : 1 < Erdos990.M f := lt_of_lt_of_le (by norm_num) (OMA.Height990.two_le f h₀ hn)
    have hl := Real.log_pos hM
    have h := OMA.Arc990.discrepancy x hn hx (mul_pos (by norm_num : (0:ℝ)<2) hl)
      (OMA.Moment990.modes x hM cap) (α/(2*π)) (β/(2*π)) (div_nonneg hα hp.le)
      (div_le_div_of_nonneg_right hαβ hp.le) ((div_le_one hp).2 hβ)
    rw [← sub_div] at h
    refine h.trans_eq ?_
    rw [show (f.natDegree:ℝ)*(2*Real.log (Erdos990.M f)) =
      2*((f.natDegree:ℝ)*Real.log (Erdos990.M f)) by ring,
      Real.sqrt_mul (by norm_num : (0:ℝ)≤2), mul_assoc]
  · have hz : f.natDegree = 0 := by omega
    have hempty : IsEmpty (Fin f.natDegree) := hz ▸ Fin.isEmpty'
    simp [hz]

end Finish990
