import FormalConjectures.ErdosProblems.«517»
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.Complex.Liouville

/-!
The Fejér gap theorem by Biernacki's descending elimination of exponents
(Sur les équations algébriques contenant des paramètres arbitraires, pp. 20–23).
We count zeros along a root-free polynomial homotopy and use a radius
depending on the number of roots sought. The convergence and limit arguments
are adapted from @JaviSoto’s reduction R1 (PR 5556) and @Ciphore’s merged
H2 proof (9741aec0, PR 6062), respectively.
-/

open Filter Finset Metric Polynomial Set
open scoped Topology NNReal

-- Credit: @MrSeizy
noncomputable section
namespace OMA.Section517

theorem convergence (n : ℕ → ℕ) (a : ℕ → ℂ) (f : ℂ → ℂ) (v : ℂ)
    (hf : ∀ z, HasSum (fun j => a j*z^(n j)) (f z)) :
    (∀ R : ℝ, TendstoUniformlyOn (fun j z => (((∑ j ∈ Finset.range j, Polynomial.monomial (n j) (a j)) - Polynomial.C v)).eval z) (fun z => f z-v)
      atTop (Metric.closedBall 0 R)) ∧ AnalyticOnNhd ℂ (fun z => f z-v) Set.univ := by
  have uniform (R : ℝ) : TendstoUniformlyOn (fun j z => (((∑ j ∈ Finset.range j, Polynomial.monomial (n j) (a j)) - Polynomial.C v)).eval z)
      (fun z => f z-v) atTop (Metric.closedBall 0 R) := by
    let T := max R 0
    have hT : 0 ≤ T := le_max_right _ _
    have hs := (hf (T:ℂ)).summable.norm
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hT] at hs
    have hu := tendstoUniformlyOn_tsum_nat (f := fun j (z:ℂ) => a j*z^(n j))
      (s := Metric.closedBall 0 R) hs (by
        intro j z hz
        have hR : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall] using hz
        rw [norm_mul,norm_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hR.trans (le_max_left _ _)) _) (norm_nonneg _))
    have eqf : (fun z => ∑' j, a j*z^(n j)) = f := funext fun z => (hf z).tsum_eq
    rw [eqf] at hu
    rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
    intro ε he
    filter_upwards [hu ε he] with K hK
    intro z hz
    simpa [eval_finsetSum,dist_eq_norm,sub_sub_sub_cancel_right] using hK z hz
  refine ⟨uniform, ?_⟩
  have hl : TendstoLocallyUniformlyOn (fun j z => (((∑ j ∈ Finset.range j, Polynomial.monomial (n j) (a j)) - Polynomial.C v)).eval z)
      (fun z => f z-v) atTop Set.univ := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mpr
    intro C _ hc
    obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_closedBall (0:ℂ)).mp hc.isBounded
    exact (uniform R).mono hR
  exact (hl.differentiableOn (Eventually.of_forall fun j =>
    (((∑ j ∈ Finset.range j, Polynomial.monomial (n j) (a j)) - Polynomial.C v)).differentiable.differentiableOn) isOpen_univ).analyticOnNhd isOpen_univ

end OMA.Section517

namespace OMA.FejerZeros

private theorem factorNorm (s : Multiset ℂ) (z : ℂ) :
    ‖((s.map fun r => X - C r).prod : ℂ[X]).eval z‖ =
      (s.map fun r => ‖z - r‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih => simp [ih]

/-- Factoring out roots within distance A of c leaves a polynomial whose value
at c is bounded by its maximum on the circle of radius 3A. -/
private theorem centerBound (p : ℂ[X]) (s : Multiset ℂ) (hp : p ≠ 0)
    (hs : s ≤ p.roots) {c : ℂ} {A M : ℝ} (hA : 0 < A)
    (hnear : ∀ r ∈ s, ‖c - r‖ ≤ A)
    (hcircle : ∀ z ∈ sphere c (3 * A), ‖p.eval z‖ ≤ M) :
    ‖p.eval c‖ ≤ M * (1 / 2 : ℝ) ^ s.card := by
  obtain ⟨q, hq⟩ := (s.prod_X_sub_C_dvd_iff_le_roots hp).2 hs
  have heval (z : ℂ) :
      ‖p.eval z‖ = (s.map fun r => ‖z - r‖).prod * ‖q.eval z‖ := by
    rw [hq, eval_mul, norm_mul, factorNorm]
  have hqCircle (z : ℂ) (hz : z ∈ sphere c (3 * A)) :
      ‖q.eval z‖ ≤ M / (2 * A) ^ s.card := by
    have hl (r : ℂ) (hr : r ∈ s) : 2 * A ≤ ‖z - r‖ := by
      have htriangle := dist_triangle z r c
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, norm_sub_rev r c,
        mem_sphere_iff_norm.mp hz] at htriangle
      linarith [hnear r hr]
    have hfactor : (2 * A) ^ s.card ≤ (s.map fun r => ‖z - r‖).prod := by
      simpa using Multiset.prod_map_le_prod_map₀ (s := s) (fun _ => 2 * A)
        (fun r => ‖z - r‖) (fun _ _ => by positivity) hl
    apply (le_div_iff₀ (by positivity)).2
    rw [mul_comm]
    calc
      (2 * A) ^ s.card * ‖q.eval z‖ ≤
          (s.map fun r => ‖z - r‖).prod * ‖q.eval z‖ :=
        mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
      _ = ‖p.eval z‖ := (heval z).symm
      _ ≤ M := hcircle z hz
  have hqc : ‖q.eval c‖ ≤ M / (2 * A) ^ s.card := by
    simpa using Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 0
      (show 0 < 3 * A by positivity) q.differentiable.diffContOnCl hqCircle
  have hfactor : (s.map fun r => ‖c - r‖).prod ≤ A ^ s.card := by
    simpa using Multiset.prod_map_le_prod_map₀ (s := s) (fun r => ‖c - r‖)
      (fun _ => A) (fun _ _ => norm_nonneg _) hnear
  rw [heval]
  calc
    _ ≤ A ^ s.card * (M / (2 * A) ^ s.card) :=
      (mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hqc (by positivity))
    _ = M * (1 / 2 : ℝ) ^ s.card := by
      rw [show A ^ s.card * (M / (2 * A) ^ s.card) =
        M * (A ^ s.card / (2 * A) ^ s.card) by ring, ← div_pow]
      congr 2
      field_simp

/-- Uniform convergence excludes polynomial roots from every compact set on
which the limit has no zeros. -/
private theorem eventuallyRootFree (P : ℕ → ℂ[X]) {f : ℂ → ℂ} (hf : Continuous f)
    (hu : ∀ R : ℝ, TendstoUniformlyOn (fun j z => (P j).eval z) f atTop (closedBall 0 R))
    {K : Set ℂ} {R : ℝ} (hK : IsCompact K) (hKR : K ⊆ closedBall 0 R)
    (hnz : ∀ z ∈ K, f z ≠ 0) :
    ∀ᶠ j in atTop, ∀ z ∈ K, (P j).eval z ≠ 0 := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne hf.norm.continuousOn
  have hpos : 0 < ‖f z₀‖ := norm_pos_iff.mpr (hnz _ hz₀)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hu R)) _ hpos] with j hj
  intro z hz he
  have hd := hj z (hKR hz)
  rw [he] at hd
  have hle : ‖f z₀‖ ≤ ‖f z‖ := hmin hz
  simp only [dist_eq_norm, sub_zero] at hd
  exact (not_lt_of_ge hle) hd

set_option maxHeartbeats 600000 in
theorem transferZeros (P : ℕ → ℂ[X]) (f : ℂ → ℂ)
    (hAnalytic : AnalyticOnNhd ℂ f Set.univ)
    (hUniform : ∀ R : ℝ, TendstoUniformlyOn (fun j z => (P j).eval z) f atTop
      (Metric.closedBall 0 R))
    (hMany : ∀ m : ℕ, ∃ R : ℝ, ∀ᶠ j : ℕ in atTop,
      m ≤ ((P j).roots.filter (fun z => ‖z‖ ≤ R)).card) :
    {z | f z = 0}.Infinite := by
  classical
  intro hFinite
  have hContinuous : Continuous f :=
    continuousOn_univ.mp hAnalytic.continuousOn
  obtain ⟨B, hB⟩ := (hFinite.image (fun z => ‖z‖)).bddAbove
  let R₀ := max B 0 + 1
  have hR₀ : 0 < R₀ := by dsimp [R₀]; linarith [le_max_right B 0]
  have hzeros (z : ℂ) (hz : f z = 0) : ‖z‖ < R₀ := by
    exact (hB (mem_image_of_mem (fun z => ‖z‖) hz)).trans_lt
      (by dsimp [R₀]; linarith [le_max_left B 0])
  let c : ℂ := (R₀ : ℂ)
  have hcnorm : ‖c‖ = R₀ := by simp [c, Complex.norm_real, abs_of_pos hR₀]
  have hcnz : f c ≠ 0 := fun hc => (lt_irrefl R₀) (hcnorm ▸ hzeros c hc)
  let A : ℝ := R₀ + ‖c‖
  have hA : 0 < A := by dsimp [A]; positivity
  let S : ℝ := 3 * A + ‖c‖
  have hcS : c ∈ closedBall 0 S := by
    simpa [Metric.mem_closedBall, S] using (show ‖c‖ ≤ 3 * A + ‖c‖ by linarith)
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) S).bddAbove_image
    hContinuous.norm.continuousOn
  let M := max M₀ 0 + 1
  have hM : 0 < M := by dsimp [M]; linarith [le_max_right M₀ 0]
  have hMbound (z : ℂ) (hz : z ∈ closedBall 0 S) : ‖f z‖ + 1 ≤ M := by
    have hzM := hM₀ (mem_image_of_mem (fun z => ‖f z‖) hz)
    dsimp [M]
    linarith [le_max_left M₀ 0]
  have heSmall : 0 < ‖f c‖ / 2 := half_pos (norm_pos_iff.mpr hcnz)
  have ht : Tendsto (fun m : ℕ => M * (1 / 2 : ℝ) ^ m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)).const_mul M
  obtain ⟨m, hm⟩ := (ht.eventually (gt_mem_nhds heSmall)).exists
  obtain ⟨R, hR⟩ := hMany m
  let K := closedBall (0 : ℂ) R ∩ {z : ℂ | R₀ ≤ ‖z‖}
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const continuous_norm)
  have hKfree := eventuallyRootFree P hContinuous hUniform hK (fun _ hz => hz.1)
    (fun z hz hzero => (not_lt_of_ge hz.2) (hzeros z hzero))
  have hUb := Metric.tendstoUniformlyOn_iff.mp (hUniform S)
  have hBoth := hR.and (hKfree.and ((hUb 1 zero_lt_one).and (hUb _ heSmall)))
  obtain ⟨j, hjR, hjK, hjB, hjc⟩ := hBoth.exists
  have hcClose := hjc c hcS
  have hdiff : ‖f c - (P j).eval c‖ < ‖f c‖ / 2 := by
    simpa [dist_eq_norm, norm_sub_rev] using hcClose
  have hLower : ‖f c‖ / 2 < ‖(P j).eval c‖ := by
    have htriangle := norm_add_le (f c - (P j).eval c) ((P j).eval c)
    rw [sub_add_cancel] at htriangle
    linarith
  have hp : P j ≠ 0 := by
    intro he
    simp [he, not_lt_of_ge heSmall.le] at hLower
  let s := (P j).roots.filter (fun z => ‖z‖ ≤ R)
  have hnear (r : ℂ) (hr : r ∈ s) : ‖c - r‖ ≤ A := by
    have ⟨hroot, hrR⟩ := Multiset.mem_filter.mp hr
    have hrR₀ : ‖r‖ < R₀ := by
      by_contra! hge
      exact hjK r ⟨by simpa using hrR, hge⟩ ((mem_roots hp).mp hroot)
    exact (norm_sub_le c r).trans (by dsimp [A]; linarith)
  have hcircle (z : ℂ) (hz : z ∈ sphere c (3 * A)) : ‖(P j).eval z‖ ≤ M := by
    have hzS : z ∈ closedBall (0 : ℂ) S := by
      have ht := dist_triangle z c (0 : ℂ)
      rw [mem_sphere.mp hz] at ht
      simpa [Metric.mem_closedBall, S] using ht
    have hclose : ‖(P j).eval z - f z‖ < 1 := by
      simpa [dist_eq_norm, norm_sub_rev] using hjB z hzS
    have htriangle := norm_add_le ((P j).eval z - f z) (f z)
    rw [sub_add_cancel] at htriangle
    linarith [hMbound z hzS]
  have hUpper := centerBound (P j) s hp (Multiset.filter_le _ _) hA hnear hcircle
  have hdec : (1 / 2 : ℝ) ^ s.card ≤ (1 / 2 : ℝ) ^ m :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hjR
  exact (not_lt_of_ge (hUpper.trans (mul_le_mul_of_nonneg_left hdec hM.le)))
    (hm.trans hLower)

end OMA.FejerZeros

namespace OMA.FejerElimination

private theorem degree {n : ℕ → ℕ} (h : StrictMono n) (a : ℕ → ℂ) (v : ℂ) (s : ℕ)
    (hp : 0<n s) (ha : a s≠0) : (((∑ j ∈ Finset.range (s+1), Polynomial.monomial (n j) (a j)) - Polynomial.C v)).natDegree=n s := by
  classical
  have up : (((∑ j ∈ Finset.range (s+1), Polynomial.monomial (n j) (a j)) - Polynomial.C v)).natDegree ≤ n s := by
    apply (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
    apply natDegree_sum_le_of_forall_le
    intro j hj
    exact (natDegree_monomial_le _).trans (h.monotone (by have := mem_range.mp hj; omega))
  apply le_antisymm up
  apply le_natDegree_of_ne_zero
  have eqn : (((∑ j ∈ Finset.range (s+1), Polynomial.monomial (n j) (a j)) - Polynomial.C v)).coeff (n s) = a s := by
    rw [coeff_sub,finsetSum_coeff,coeff_C_of_ne_zero hp.ne',sub_zero,sum_eq_single s]
    · simp
    · intro b _ ne; exact coeff_monomial_of_ne _ (fun e => ne (h.injective e.symm))
    · simp
  rwa [eqn]


private theorem eval_logderiv_prod (S : Multiset ℂ) (w : ℂ)
    (h : ((S.map fun a => X - C a).prod : ℂ[X]).eval w ≠ 0) :
    ((S.map fun a => X - C a).prod : ℂ[X]).derivative.eval w /
      ((S.map fun a => X - C a).prod : ℂ[X]).eval w =
    (S.map fun a => (w - a)⁻¹).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, eval_mul, eval_sub, eval_X, eval_C,
      mul_ne_zero_iff] at h
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, derivative_mul,
      derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul,
      eval_sub, eval_X, eval_C]
    rw [← ih h.2]
    field_simp [h.1, h.2]

private theorem eval_logderiv {P : ℂ[X]} {w : ℂ} (h : P.eval w ≠ 0) :
    P.derivative.eval w / P.eval w = (P.roots.map fun a => (w - a)⁻¹).sum := by
  have hp : P ≠ 0 := by rintro rfl; apply h; simp
  have hl : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have fac := (IsAlgClosed.splits P).eq_prod_roots
  have hprod : ((P.roots.map fun a => X - C a).prod : ℂ[X]).eval w ≠ 0 := by
    intro he
    apply h
    rw [fac, eval_mul, he, mul_zero]
  calc
    _ = (C P.leadingCoeff * (P.roots.map fun a => X - C a).prod).derivative.eval w /
        (C P.leadingCoeff * (P.roots.map fun a => X - C a).prod).eval w :=
      congrArg (fun Q : ℂ[X] => Q.derivative.eval w / Q.eval w) fac
    _ = _ := by
      simpa only [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C,
        mul_div_mul_left _ _ hl] using eval_logderiv_prod P.roots w hprod

private def rootCount (P : ℂ[X]) (r : ℝ) : ℕ :=
  (P.roots.filter fun a => ‖a‖ ≤ r).card

private theorem circleIntegral_inv_factor {r : ℝ} (hr : 0 < r) {a : ℂ} (ha : ‖a‖ ≠ r) :
    circleIntegral (fun w => (w - a)⁻¹) 0 r =
      if ‖a‖ ≤ r then (2 * (Real.pi : ℂ) * Complex.I) else 0 := by
  split_ifs with hi
  · exact circleIntegral.integral_sub_inv_of_mem_ball
      (by simpa [mem_ball, dist_zero_right] using lt_of_le_of_ne hi ha)
  · have hd : DiffContOnCl ℂ (fun w : ℂ => (w - a)⁻¹) (ball 0 r) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ hr.ne']
      apply (differentiableOn_id.sub (differentiableOn_const _)).inv
      intro w hw
      apply sub_ne_zero.mpr
      rintro rfl
      exact hi (by simpa [mem_closedBall, dist_zero_right] using hw)
    exact hd.circleIntegral_eq_zero hr.le

private theorem circleIntegral_inv_sum {r : ℝ} (hr : 0 < r) (S : Multiset ℂ)
    (hS : ∀ a ∈ S, ‖a‖ ≠ r) :
    circleIntegral (fun w => (S.map fun a => (w - a)⁻¹).sum) 0 r =
      (2 * (Real.pi : ℂ) * Complex.I) * ((S.filter fun a => ‖a‖ ≤ r).card : ℂ) := by
  induction S using Multiset.induction_on with
  | empty => simp [circleIntegral]
  | cons a S ih =>
    have ha := hS a (Multiset.mem_cons_self _ _)
    have hs (b) (hb : b ∈ S) := hS b (Multiset.mem_cons_of_mem hb)
    have hc (b : ℂ) (hb : ‖b‖ ≠ r) :
        ContinuousOn (fun w : ℂ => (w - b)⁻¹) (sphere 0 r) := by
      apply (continuousOn_id.sub continuousOn_const).inv₀
      intro w hw
      apply sub_ne_zero.mpr
      rintro rfl
      exact hb (by simpa [mem_sphere, dist_zero_right] using hw)
    have hsum (T : Multiset ℂ) (ht : ∀ b ∈ T, ‖b‖ ≠ r) :
        ContinuousOn (fun w : ℂ => (T.map fun b => (w - b)⁻¹).sum) (sphere 0 r) := by
      induction T using Multiset.induction_on with
      | empty => simpa using (continuousOn_const (c := (0 : ℂ)))
      | cons b T ih' =>
        simp only [Multiset.map_cons, Multiset.sum_cons]
        exact (hc b (ht _ (Multiset.mem_cons_self _ _))).add
          (ih' (fun c hc => ht c (Multiset.mem_cons_of_mem hc)))
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [circleIntegral.integral_add ((hc a ha).circleIntegrable hr.le)
      ((hsum S hs).circleIntegrable hr.le), circleIntegral_inv_factor hr ha, ih hs, Multiset.filter_cons]
    split_ifs <;> simp
    ring

private theorem circleIntegral_logderiv {r : ℝ} (hr : 0 < r) {P : ℂ[X]}
    (h : ∀ w ∈ sphere 0 r, P.eval w ≠ 0) :
    circleIntegral (fun w => P.derivative.eval w / P.eval w) 0 r =
      (2 * (Real.pi : ℂ) * Complex.I) * (rootCount P r : ℂ) := by
  rw [circleIntegral.integral_congr hr.le (fun w hw => eval_logderiv (h w hw))]
  apply circleIntegral_inv_sum hr
  intro a ha he
  exact h a (by simpa [mem_sphere, dist_zero_right] using he) (isRoot_of_mem_roots ha)

private theorem count_homotopy {r : ℝ} (hr : 0 < r) (P : ℝ → ℂ[X])
    (hD : ContinuousOn (fun y : ℝ × ℂ => (P y.1).derivative.eval y.2)
      (Set.Icc 0 1 ×ˢ sphere 0 r))
    (hC : ContinuousOn (fun y : ℝ × ℂ => (P y.1).eval y.2)
      (Set.Icc 0 1 ×ˢ sphere 0 r))
    (h : ∀ u ∈ Set.Icc 0 1, ∀ w ∈ sphere 0 r, (P u).eval w ≠ 0) :
    rootCount (P 0) r = rootCount (P 1) r := by
  let F (u : ℝ) (w : ℂ) := (P u).derivative.eval w / (P u).eval w
  have hF : ContinuousOn (fun y : ℝ × ℂ => F y.1 y.2) (Set.Icc 0 1 ×ˢ sphere 0 r) :=
    hD.div hC (fun _ hy => h _ hy.1 _ hy.2)
  have hu := (isCompact_Icc.prod (isCompact_sphere (0 : ℂ) r)).uniformContinuousOn_of_continuous hF
  have hc : ContinuousOn (fun u => circleIntegral (F u) 0 r) (Set.Icc 0 1) := by
    intro u hu₀
    apply (hu.tendstoUniformlyOn hu₀).tendsto_circleIntegral_of_continuousOn hr.le
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn fun _ hw => ⟨hv, hw⟩
  let A : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hA : A ≠ 0 := by simp [A, Real.pi_ne_zero, Complex.I_ne_zero]
  have he (u : ℝ) (hu : u ∈ Set.Icc 0 1) : circleIntegral (F u) 0 r / A =
      (rootCount (P u) r : ℂ) := by
    rw [circleIntegral_logderiv hr (h u hu), mul_comm]
    exact mul_div_cancel_right₀ _ hA
  have hc' : ContinuousOn (fun u => (rootCount (P u) r : ℝ)) (Set.Icc 0 1) := by
    have hd := Complex.continuous_re.comp_continuousOn (hc.div_const A)
    apply hd.congr
    intro u hu
    simp only [Function.comp_apply, he u hu, Complex.natCast_re]
  have hmap : MapsTo (fun u => (rootCount (P u) r : ℝ)) (Set.Icc 0 1)
      (range ((↑) : ℕ → ℝ)) := fun _ _ => mem_range_self _
  have hdiscrete : IsDiscrete (range ((↑) : ℕ → ℝ)) := by
    apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
    rintro _ ⟨n, rfl⟩
    refine ⟨Set.Ioo ((n : ℝ) - 1) ((n : ℝ) + 1), isOpen_Ioo, ?_⟩
    ext x
    constructor
    · rintro ⟨hx, ⟨j, rfl⟩⟩
      have hlo : (n : ℝ) < (j : ℝ) + 1 := by linarith [hx.1]
      have hhi : (j : ℝ) < (n : ℝ) + 1 := hx.2
      have h₁ : n < j + 1 := by exact_mod_cast hlo
      have h₂ : j < n + 1 := by exact_mod_cast hhi
      exact mem_singleton_iff.mpr (by congr 1; omega)
    · rintro rfl
      exact ⟨⟨by linarith, by linarith⟩, mem_range_self _⟩
  have hd := isPreconnected_Icc.constant_of_mapsTo hdiscrete hc' hmap
    (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
  exact_mod_cast hd

private theorem rootCount_mono (P : ℂ[X]) {r t : ℝ} (h : r ≤ t) :
    rootCount P r ≤ rootCount P t :=
  Multiset.card_le_card (Multiset.monotone_filter_right _ fun _ ha => ha.trans h)

private theorem exists_separated_radius (S : Multiset ℂ) {q : ℝ} (hq : 1 < q)
    (k : ℕ) (r : ℝ) (hr : 0 < r) (h : (S.filter fun a => ‖a‖ ≤ r).card ≤ k) :
    ∃ t : ℝ, r / q ^ k ≤ t ∧ t ≤ r ∧ ∀ a ∈ S, ‖a‖ ≤ t → ‖a‖ ≤ t / q := by
  have hq₀ : 0 < q := by linarith
  induction k generalizing r with
  | zero =>
    refine ⟨r, by simp, le_rfl, ?_⟩
    intro a ha har
    have hn : a ∈ S.filter (fun b => ‖b‖ ≤ r) := Multiset.mem_filter.mpr ⟨ha, har⟩
    have hz : (S.filter fun a => ‖a‖ ≤ r) = 0 :=
      Multiset.card_eq_zero.mp (Nat.eq_zero_of_le_zero h)
    rw [hz] at hn
    exact (Multiset.notMem_zero a hn).elim
  | succ k ih =>
    have hrq : r / q ≤ r := div_le_self hr.le hq.le
    by_cases hs : ∀ a ∈ S, ‖a‖ ≤ r → ‖a‖ ≤ r / q
    · exact ⟨r, div_le_self hr.le (one_le_pow₀ hq.le), le_rfl, hs⟩
    · push Not at hs
      obtain ⟨a, ha, har, haqr⟩ := hs
      have hlt : (S.filter fun b => ‖b‖ ≤ r / q) < (S.filter fun b => ‖b‖ ≤ r) := by
        apply lt_of_le_of_ne (Multiset.monotone_filter_right _ fun _ hb => hb.trans hrq)
        intro he
        have hm : a ∈ S.filter (fun b => ‖b‖ ≤ r) := Multiset.mem_filter.mpr ⟨ha, har⟩
        rw [← he] at hm
        exact haqr.not_ge (Multiset.mem_filter.mp hm).2
      have hcard := Multiset.card_lt_card hlt
      obtain ⟨t, ht, htr, hsep⟩ := ih (r / q) (div_pos hr hq₀) (by omega)
      exact ⟨t, by simpa [pow_succ, div_div, mul_comm] using ht, htr.trans hrq, hsep⟩

private theorem re_div_le_half {w a : ℂ} (h : ‖w‖ < ‖a‖) :
    (w / (w - a)).re ≤ 1 / 2 := by
  have hne : w - a ≠ 0 := sub_ne_zero.mpr (fun e => h.ne (congrArg norm e))
  have hp : 0 < Complex.normSq (w - a) := Complex.normSq_pos.mpr hne
  have hs : Complex.normSq w ≤ Complex.normSq a := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) h.le _
  rw [Complex.div_re, ← add_div, div_le_iff₀ hp]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at *
  nlinarith

private theorem re_div_le_inner {w a : ℂ} {t q : ℝ} (ht : 0 < t) (hq : 1 < q)
    (hw : ‖w‖ = t) (ha : ‖a‖ ≤ t / q) :
    (w / (w - a)).re ≤ 1 + (q - 1)⁻¹ := by
  have hq₀ : 0 < q := by linarith
  have hsmall : t / q < t := div_lt_self ht hq
  have hne : w - a ≠ 0 := sub_ne_zero.mpr (fun e => (ha.trans_lt hsmall).ne (e ▸ hw))
  have htri := norm_sub_norm_le w a
  rw [hw] at htri
  have hb : ‖a‖ * (q - 1) ≤ ‖w - a‖ := by
    have hh := (le_div_iff₀ hq₀).mp ha
    linarith
  have he : w / (w - a) = 1 + a / (w - a) := by field_simp; ring
  rw [he, Complex.add_re, Complex.one_re]
  apply add_le_add_right
  refine (Complex.re_le_norm _).trans ?_
  rw [norm_div, ← one_div, div_le_div_iff₀ (norm_pos_iff.mpr hne) (sub_pos.mpr hq), one_mul]
  exact hb

private theorem sum_le_filter {S : Multiset ℂ} {g : ℂ → ℝ} {d : ℂ → Prop} [DecidablePred d]
    {A B : ℝ} (h : ∀ a ∈ S, g a ≤ if d a then A else B) :
    (S.map g).sum ≤ (S.card : ℝ) * B + ((S.filter d).card : ℝ) * (A - B) := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    have ha := h a (Multiset.mem_cons_self _ _)
    have hs := ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))
    by_cases hd : d a <;> simp [hd] at ha ⊢ <;> linarith

private def eliminate (N : ℕ) (P : ℂ[X]) : ℂ[X] := (N : ℂ) • P - X * P.derivative

/-- A section with fewer than m roots on a closed disk still has fewer than m
    after top-degree elimination, with a controlled decrease in radius. -/
private theorem count_eliminate {P : ℂ[X]} {N m : ℕ} (hN : P.natDegree = N)
    (hm : 2 * m ≤ N) {r : ℝ} (hr : 0 < r) (hcount : rootCount P r < m) :
    rootCount (eliminate N P) (r / Real.exp (4 * (m : ℝ)^2 / N)) < m := by
  have hm₀ : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hN₀ : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNm : 2 * (m : ℝ) ≤ N := by exact_mod_cast hm
  let q := 1 + 4 * (m : ℝ) / N
  have hq : 1 < q := by dsimp [q]; linarith [show 0 < 4 * (m : ℝ) / N by positivity]
  have hq₀ : 0 < q := by linarith
  obtain ⟨t, ht, htr, hgap⟩ := exists_separated_radius P.roots hq m r hr hcount.le
  have ht₀ : 0 < t := (div_pos hr (pow_pos hq₀ _)).trans_le ht
  have hroot : ¬ ∃ a ∈ P.roots, ‖a‖ = t := by
    rintro ⟨a, ha, h⟩
    have hd := hgap a ha h.le
    rw [h] at hd
    exact (div_lt_self ht₀ hq).not_ge hd
  have hP : P ≠ 0 := by
    rintro rfl
    simp at hN
    omega
  have hnz (w : ℂ) (hw : w ∈ sphere 0 t) : P.eval w ≠ 0 := by
    intro he
    exact hroot ⟨w, (mem_roots hP).mpr he, by simpa [mem_sphere, dist_zero_right] using hw⟩
  have hlt (w : ℂ) (hw : w ∈ sphere 0 t) :
      (w * (P.derivative.eval w / P.eval w)).re < (N : ℝ) := by
    have hwt : ‖w‖ = t := by simpa [mem_sphere, dist_zero_right] using hw
    rw [eval_logderiv (hnz w hw), ← Multiset.sum_map_mul_left]
    change Complex.reAddGroupHom _ < _
    rw [map_multiset_sum, Multiset.map_map]
    have hb (a : ℂ) (ha : a ∈ P.roots) :
        (w * (w - a)⁻¹).re ≤ if ‖a‖ ≤ t then 1 + (q - 1)⁻¹ else 1/2 := by
      rw [← div_eq_mul_inv]
      split_ifs with hi
      · exact re_div_le_inner ht₀ hq hwt (hgap a ha hi)
      · apply re_div_le_half; rwa [hwt, lt_iff_not_ge]
    have hs := sum_le_filter hb
    rw [← (IsAlgClosed.splits P).natDegree_eq_card_roots, hN] at hs
    have hk : (rootCount P t : ℝ) < m :=
      Nat.cast_lt.mpr ((rootCount_mono P htr).trans_lt hcount)
    have hl := mul_lt_mul_of_pos_right hk (show 0 < 1 + (q - 1)⁻¹ - 1/2 by
      linarith [inv_pos.mpr (sub_pos.mpr hq)])
    have hqeq : (m : ℝ) * (1 + (q - 1)⁻¹ - 1/2) = m / 2 + N / 4 := by
      dsimp [q]
      rw [add_sub_cancel_left]
      field_simp
      ring
    rw [hqeq] at hl
    change _ ≤ _ + (rootCount P t : ℝ) * _ at hs
    change (P.roots.map fun a => (w * (w - a)⁻¹).re).sum < (N : ℝ)
    linarith only [hs, hl, hNm]
  let H (u : ℝ) : ℂ[X] := (N : ℂ) • P - (u : ℂ) • (X * P.derivative)
  have hH (u : ℝ) (hu : u ∈ Set.Icc 0 1) (w : ℂ) (hw : w ∈ sphere 0 t) : (H u).eval w ≠ 0 := by
    intro he
    have hpos : 0 < (N : ℝ) - u * (w * (P.derivative.eval w / P.eval w)).re := by
      by_cases hc : 0 ≤ (w * (P.derivative.eval w / P.eval w)).re
      · linarith [mul_le_of_le_one_left hc hu.2, hlt w hw]
      · linarith [mul_nonpos_of_nonneg_of_nonpos hu.1 (le_of_not_ge hc)]
    have he' : ((N : ℂ) - (u : ℂ) * (w * (P.derivative.eval w / P.eval w))) * P.eval w = 0 := by
      rw [← he]
      simp only [H, eval_sub, eval_smul, smul_eq_mul, eval_mul, eval_X]
      field_simp [hnz w hw]
    have hz := congrArg Complex.re ((mul_eq_zero.mp he').resolve_right (hnz w hw))
    simp only [Complex.sub_re, Complex.natCast_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] at hz
    exact hpos.ne' hz
  have hC : ContinuousOn (fun y : ℝ × ℂ => (H y.1).eval y.2)
      (Set.Icc 0 1 ×ˢ sphere 0 t) := by
    simp only [H, eval_sub, eval_smul, smul_eq_mul, eval_mul, eval_X]
    fun_prop
  have hD : ContinuousOn (fun y : ℝ × ℂ => (H y.1).derivative.eval y.2)
      (Set.Icc 0 1 ×ˢ sphere 0 t) := by
    simp only [H, derivative_sub, map_smul, derivative_mul, derivative_X, one_mul,
      eval_sub, eval_smul, smul_eq_mul, eval_add, eval_mul, eval_X]
    fun_prop
  have heq := count_homotopy ht₀ H hD hC hH
  have hcast : (N : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < N by omega))
  have hzero : H 0 = C (N : ℂ) * P := by simp [H, smul_eq_C_mul]
  have hone : H 1 = eliminate N P := by simp [H, eliminate]
  rw [hzero, hone] at heq
  have hroots : (C (N : ℂ) * P).roots = P.roots := by
    rw [roots_mul (mul_ne_zero (C_ne_zero.mpr hcast) hP), roots_C, zero_add]
  unfold rootCount at heq
  rw [hroots] at heq
  change rootCount P t = rootCount (eliminate N P) t at heq
  have hpow : q ^ m ≤ Real.exp (4 * (m : ℝ)^2 / N) := by
    calc
      q ^ m ≤ (Real.exp (4 * (m : ℝ) / N)) ^ m :=
        pow_le_pow_left₀ hq₀.le (by simpa [q, add_comm] using Real.add_one_le_exp (4 * (m : ℝ) / N)) _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hrad := (div_le_div_of_nonneg_left hr.le (pow_pos hq₀ _) hpow).trans ht
  exact (rootCount_mono _ hrad).trans_lt (heq ▸ (rootCount_mono P htr).trans_lt hcount)

private def normalizedEliminate (N p : ℕ) : ℂ[X] →ₗ[ℂ] ℂ[X] :=
  ((N : ℂ) - (p : ℂ))⁻¹ •
    ((N : ℂ) • LinearMap.id - (LinearMap.mulLeft ℂ (X : ℂ[X])).comp derivative)

private theorem normalized_apply (N p : ℕ) (P : ℂ[X]) :
    normalizedEliminate N p P = ((N : ℂ) - (p : ℂ))⁻¹ • eliminate N P := rfl

private theorem normalized_coeff (N p : ℕ) (P : ℂ[X]) (i : ℕ) :
    (normalizedEliminate N p P).coeff i =
      (((N : ℂ) - (i : ℂ)) / ((N : ℂ) - (p : ℂ))) * P.coeff i := by
  rw [normalized_apply, coeff_smul, eliminate, coeff_sub, coeff_smul]
  cases i with
  | zero => simp [div_eq_mul_inv, mul_left_comm, mul_assoc]
  | succ i =>
    rw [coeff_X_mul, coeff_derivative]
    simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring

private theorem normalized_monomial (N p i : ℕ) (c : ℂ) :
    normalizedEliminate N p (monomial i c) =
      monomial i ((((N : ℂ) - (i : ℂ)) / ((N : ℂ) - (p : ℂ))) * c) := by
  ext j
  rw [normalized_coeff]
  by_cases h : j = i
  · subst j
    simp
  · simp [coeff_monomial, Ne.symm h]

private theorem subtraction_cast_ne {i N : ℕ} (hi : i < N) : (N : ℂ) - (i : ℂ) ≠ 0 :=
  sub_ne_zero.mpr (by exact_mod_cast hi.ne')

private theorem normalized_degree {N p : ℕ} (hp : p < N) {P : ℂ[X]} (hP : P ≠ 0)
    (hd : P.natDegree = p) : (normalizedEliminate N p P).natDegree = p := by
  have hc : (normalizedEliminate N p P).coeff p = P.coeff p := by
    rw [normalized_coeff, div_self (subtraction_cast_ne hp), one_mul]
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [normalized_coeff, coeff_eq_zero_of_natDegree_lt (hd ▸ hi), mul_zero]
  · apply le_natDegree_of_ne_zero
    rw [hc, ← hd, ← leadingCoeff]
    exact leadingCoeff_ne_zero.mpr hP

private theorem normalized_leading {N p : ℕ} (hp : p < N) {P : ℂ[X]} (hP : P ≠ 0)
    (hd : P.natDegree = p) : (normalizedEliminate N p P).leadingCoeff = P.leadingCoeff := by
  change (normalizedEliminate N p P).coeff (normalizedEliminate N p P).natDegree =
    P.coeff P.natDegree
  rw [normalized_degree hp hP hd, hd, normalized_coeff, div_self (subtraction_cast_ne hp), one_mul]

private theorem coefficient_growth {N p i : ℕ} (hi : i ≤ p) (hp : p < N) :
    ‖(((N : ℂ) - (i : ℂ)) / ((N : ℂ) - (p : ℂ)))‖ ≤
      Real.exp ((p : ℝ) * ((p : ℝ) + 1) / N) := by
  have hNP : (p : ℝ) + 1 ≤ N := by exact_mod_cast hp
  have hN : 0 < (N : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) p]
  have hP : 0 < (N : ℝ) - p := by linarith
  have hi₁ : (i : ℝ) ≤ p := by exact_mod_cast hi
  have hi₂ : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
  have he : (N : ℝ) ≤ ((p : ℝ) + 1) * ((N : ℝ) - p) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) p) (sub_nonneg.mpr hNP)]
  have hb : (p : ℝ) / ((N : ℝ) - p) ≤ (p : ℝ) * ((p : ℝ) + 1) / N := by
    rw [div_le_div_iff₀ hP hN]
    nlinarith [mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (α := ℝ) p)]
  rw [← Complex.ofReal_natCast N, ← Complex.ofReal_natCast i, ← Complex.ofReal_natCast p,
    ← Complex.ofReal_sub, ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) hP.le)]
  calc
    ((N : ℝ) - i) / ((N : ℝ) - p) ≤ (N : ℝ) / ((N : ℝ) - p) :=
      div_le_div_of_nonneg_right (by linarith) hP.le
    _ = 1 + (p : ℝ) / ((N : ℝ) - p) := by field_simp; ring
    _ ≤ _ := by linarith [Real.add_one_le_exp ((p : ℝ) * ((p : ℝ) + 1) / N)]

private def sectionPoly (P : ℂ[X]) (n : ℕ → ℕ) (s : ℕ) (b : ℕ → ℂ) (k : ℕ) : ℂ[X] :=
  P + ∑ i ∈ range k, monomial (n (s + 1 + i)) (b i)

private def tailSum (n : ℕ → ℕ) (s k : ℕ) : ℝ :=
  ∑ i ∈ range k, (n (s + 1 + i) : ℝ)⁻¹

private theorem section_degree {n : ℕ → ℕ} (hn : StrictMono n) {P : ℂ[X]}
    {s k : ℕ} {b : ℕ → ℂ} (hP : P.natDegree = n s) (hb : b k ≠ 0) :
    (sectionPoly P n s b (k + 1)).natDegree = n (s + 1 + k) := by
  rw [sectionPoly, sum_range_succ, ← add_assoc]
  rw [natDegree_add_eq_right_of_natDegree_lt]
  · exact natDegree_monomial_eq _ hb
  rw [natDegree_monomial_eq _ hb]
  exact (natDegree_add_le _ _).trans_lt (max_lt
    (hP ▸ hn (by omega))
    (by
      have hu : (∑ i ∈ range k, monomial (n (s + 1 + i)) (b i)).natDegree ≤ n (s + k) := by
        apply natDegree_sum_le_of_forall_le
        intro i hi
        exact (natDegree_monomial_le _).trans (hn.monotone (by have := mem_range.mp hi; omega))
      exact hu.trans_lt (hn (by omega))))

private theorem section_eliminate (P : ℂ[X]) (n : ℕ → ℕ) (s k : ℕ) (b : ℕ → ℂ) :
    let N := n (s + 1 + k)
    let p := n s
    normalizedEliminate N p (sectionPoly P n s b (k + 1)) =
      sectionPoly (normalizedEliminate N p P) n s
        (fun i => ((((N : ℂ) - (n (s + 1 + i) : ℂ)) / ((N : ℂ) - (p : ℂ))) * b i)) k := by
  dsimp only
  simp [sectionPoly, sum_range_succ, map_sum, normalized_monomial, add_assoc]

private theorem cauchy_le_of_coeff {P : ℂ[X]} (hP : P ≠ 0) {B : ℝ} (hB : 1 ≤ B)
    (hc : ∀ i < P.natDegree, ‖P.coeff i‖ ≤ (B - 1) * ‖P.leadingCoeff‖) :
    (P.cauchyBound : ℝ) ≤ B := by
  have hnorm : 0 < ‖P.leadingCoeff‖ := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hP)
  let M : ℝ≥0 := ⟨(B - 1) * ‖P.leadingCoeff‖, mul_nonneg (sub_nonneg.mpr hB) hnorm.le⟩
  have hs : (range P.natDegree).sup (fun i => ‖P.coeff i‖₊) ≤ M := by
    apply Finset.sup_le
    intro i hi
    exact hc i (mem_range.mp hi)
  simp only [cauchyBound, NNReal.coe_add, NNReal.coe_div, coe_nnnorm, NNReal.coe_one]
  have hs' := NNReal.coe_mono hs
  change _ ≤ (B - 1) * ‖P.leadingCoeff‖ at hs'
  linarith only [(div_le_iff₀ hnorm).mpr hs']

/-- All the constants for iterated elimination depend only on the base degree,
    the desired number of roots, and the sum of reciprocal tail exponents. -/
private theorem finite_sections {n : ℕ → ℕ} (hn : StrictMono n) (s m k : ℕ)
    (hm : 0 < m) (hmp : 2 * m ≤ n s) (P : ℂ[X]) (hP : P ≠ 0)
    (hd : P.natDegree = n s) (b : ℕ → ℂ) (hb : ∀ i < k, b i ≠ 0)
    (B : ℝ) (hB : 1 ≤ B)
    (hc : ∀ i < n s, ‖P.coeff i‖ ≤ (B - 1) * ‖P.leadingCoeff‖) :
    m ≤ rootCount (sectionPoly P n s b k)
      (B * Real.exp ((4 * (m : ℝ)^2 + (n s : ℝ) * ((n s : ℝ) + 1)) * tailSum n s k)) := by
  induction k generalizing P b B with
  | zero =>
    simp only [sectionPoly, range_zero, sum_empty, add_zero, tailSum, mul_zero, Real.exp_zero,
      mul_one]
    have hball : P.roots.filter (fun a => ‖a‖ ≤ B) = P.roots := by
      apply Multiset.filter_eq_self.mpr
      intro z hz
      exact (show ‖z‖ < (P.cauchyBound : ℝ) from
        (isRoot_of_mem_roots hz).norm_lt_cauchyBound hP).le.trans
        (cauchy_le_of_coeff hP hB (hd.symm ▸ hc))
    rw [rootCount, hball, ← (IsAlgClosed.splits P).natDegree_eq_card_roots, hd]
    omega
  | succ k ih =>
    let N := n (s + 1 + k)
    let p := n s
    let A := 4 * (m : ℝ)^2
    let D := (p : ℝ) * ((p : ℝ) + 1)
    let R := B * Real.exp ((A + D) * tailSum n s (k + 1))
    let Q := normalizedEliminate N p P
    let b' (i : ℕ) := ((((N : ℂ) - (n (s + 1 + i) : ℂ)) / ((N : ℂ) - (p : ℂ))) * b i)
    have hpN : p < N := hn (by omega)
    have hNm : 2 * m ≤ N := hmp.trans hpN.le
    have hN₀ : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hQdegree : Q.natDegree = p := normalized_degree hpN hP hd
    have hQleading : Q.leadingCoeff = P.leadingCoeff := normalized_leading hpN hP hd
    have hQ : Q ≠ 0 := by
      intro he
      have he' := congrArg leadingCoeff he
      rw [hQleading, leadingCoeff_zero] at he'
      exact (leadingCoeff_ne_zero.mpr hP) he'
    have hb' (i : ℕ) (hi : i < k) : b' i ≠ 0 :=
      mul_ne_zero (div_ne_zero (subtraction_cast_ne (hn (by omega)))
        (subtraction_cast_ne hpN)) (hb i (by omega))
    have hL : 1 ≤ Real.exp (D / N) := Real.one_le_exp (by dsimp [D]; positivity)
    have hB' : 1 ≤ B * Real.exp (D / N) := one_le_mul_of_one_le_of_one_le hB hL
    have hcoeff (i : ℕ) (hi : i < p) :
        ‖Q.coeff i‖ ≤ (B * Real.exp (D / N) - 1) * ‖Q.leadingCoeff‖ := by
      rw [hQleading, normalized_coeff, norm_mul]
      have hg := coefficient_growth hi.le hpN
      change _ ≤ Real.exp (D / N) at hg
      calc
        _ ≤ Real.exp (D / N) * ((B - 1) * ‖P.leadingCoeff‖) :=
          mul_le_mul hg (hc i hi) (norm_nonneg _) (Real.exp_pos _).le
        _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
    have hbase := ih Q hQ hQdegree b' hb' (B * Real.exp (D / N)) hB' hcoeff
    by_contra! hlt
    have ht := count_eliminate (section_degree hn hd (hb k (Nat.lt_succ_self _)))
      hNm (show 0 < R by dsimp [R]; positivity) hlt
    have hnorm : rootCount (normalizedEliminate N p (sectionPoly P n s b (k + 1)))
        (R / Real.exp (A / N)) =
        rootCount (eliminate N (sectionPoly P n s b (k + 1))) (R / Real.exp (A / N)) := by
      rw [rootCount, rootCount, normalized_apply,
        roots_smul_nonzero _ (inv_ne_zero (subtraction_cast_ne hpN))]
    have hsect : normalizedEliminate N p (sectionPoly P n s b (k + 1)) =
        sectionPoly Q n s b' k := section_eliminate P n s k b
    have hrad : R / Real.exp (A / N) =
        (B * Real.exp (D / N)) * Real.exp ((A + D) * tailSum n s k) := by
      dsimp only [R]
      rw [mul_div_assoc, ← Real.exp_sub, mul_assoc, ← Real.exp_add]
      congr 2
      have htail : tailSum n s (k + 1) = tailSum n s k + (N : ℝ)⁻¹ := sum_range_succ _ _
      rw [htail]
      ring
    rw [← hnorm, hsect, hrad] at ht
    exact (not_lt_of_ge hbase) ht

private theorem tailSum_le {n : ℕ → ℕ} (hn : HasFejerGaps n) (s k : ℕ) :
    tailSum n s k ≤ ∑' i, (n i : ℝ)⁻¹ := by
  let f : ℕ → ℕ := fun i => s + 1 + i
  have hf : Function.Injective f := by
    intro x y h
    dsimp [f] at h
    omega
  have he : tailSum n s k = ∑ i ∈ (range k).image f, (n i : ℝ)⁻¹ := by
    rw [sum_image (fun x _ y _ h => hf h)]
    rfl
  rw [he]
  exact hn.2.sum_le_tsum _ (fun i _ => by positivity)

end OMA.FejerElimination

open OMA.FejerElimination OMA.FejerZeros OMA.Section517

set_option maxHeartbeats 600000 in
theorem OMA.solution : type_of% @Erdos517.erdos_517.variants.fejer := by
  classical
  intro f n hn a ha hf v
  obtain ⟨hUniform, hAnalytic⟩ := convergence n a f v hf
  have result := transferZeros
    (fun K : ℕ => (∑ j ∈ range K, Polynomial.monomial (n j) (a j)) - Polynomial.C v)
    (fun z => f z - v) hAnalytic hUniform
  simp only [sub_eq_zero] at result
  apply result
  intro m
  let l := m + 1
  let s := 2 * l
  let p := n s
  have hmp : 2 * l ≤ p := hn.1.id_le s
  have hl : 0 < l := by dsimp [l]; omega
  have hp : 0 < p := by omega
  let P := (∑ j ∈ range (s + 1), Polynomial.monomial (n j) (a j)) - Polynomial.C v
  have hd : P.natDegree = p := degree hn.1 a v s hp (ha s)
  have hP : P ≠ 0 := by
    intro he
    simp [he] at hd
    omega
  have hc₀ : 0 < ‖P.leadingCoeff‖ := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hP)
  let M := ∑ i ∈ range p, ‖P.coeff i‖
  let B := 1 + M / ‖P.leadingCoeff‖
  have hB : 1 ≤ B := by
    dsimp [B, M]
    exact le_add_of_nonneg_right (by positivity)
  have hc (i : ℕ) (hi : i < n s) : ‖P.coeff i‖ ≤ (B - 1) * ‖P.leadingCoeff‖ := by
    have he : (B - 1) * ‖P.leadingCoeff‖ = M := by
      dsimp only [B]
      rw [add_sub_cancel_left, div_mul_cancel₀ _ hc₀.ne']
    rw [he]
    exact single_le_sum (f := fun i => ‖P.coeff i‖) (fun _ _ => norm_nonneg _)
      (mem_range.mpr hi)
  let A := 4 * (l : ℝ)^2 + (p : ℝ) * ((p : ℝ) + 1)
  let R := B * Real.exp (A * ∑' i, (n i : ℝ)⁻¹)
  refine ⟨R, ?_⟩
  filter_upwards [eventually_ge_atTop (s + 1)] with K hK
  let k := K - (s + 1)
  have hk : s + 1 + k = K := Nat.add_sub_of_le hK
  let b (i : ℕ) := a (s + 1 + i)
  have hsection : sectionPoly P n s b k =
      (∑ j ∈ range K, Polynomial.monomial (n j) (a j)) - Polynomial.C v := by
    rw [← hk, sum_range_add]
    dsimp [sectionPoly, P, b]
    abel
  have hroots := finite_sections hn.1 s l k hl hmp P hP hd b (fun i _ => ha _) B hB hc
  have hle : B * Real.exp (A * tailSum n s k) ≤ R := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (tailSum_le hn s k) (by dsimp [A]; positivity)
  rw [hsection] at hroots
  exact (Nat.le_succ m).trans (hroots.trans (rootCount_mono _ hle))

