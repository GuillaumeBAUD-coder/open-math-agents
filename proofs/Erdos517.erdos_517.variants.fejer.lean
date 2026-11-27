import FormalConjectures.ErdosProblems.«517»
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Polynomial.Reverse

-- Problem: Erdős Problem 517 — fejer
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/517.lean:46 (declaration Erdos517.erdos_517.variants.fejer)
-- Credit: @nijv (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Proof of Erdős Problem 517 (Fejér gaps variant) via iterated Euler operators,
annulus pigeonhole, Gauss-Lucas, and polynomial Rouché. -/

open Polynomial Finset Filter Metric Set Real Complex
open scoped Topology Classical

noncomputable section

namespace OMA.Fejer517A

/- ### Part 1: Section convergence and zero-count disk transfer -/

private theorem section_convergence (n : ℕ → ℕ) (a : ℕ → ℂ) (f : ℂ → ℂ) (v : ℂ)
    (hf : ∀ z, HasSum (fun j => a j * z ^ n j) (f z)) :
    (∀ R : ℝ, TendstoUniformlyOn
      (fun j z => ((∑ k ∈ Finset.range j, monomial (n k) (a k)) - C v).eval z)
      (fun z => f z - v) atTop (closedBall 0 R)) ∧
    AnalyticOnNhd ℂ (fun z => f z - v) Set.univ := by
  have uniform (R : ℝ) : TendstoUniformlyOn
      (fun j z => ((∑ k ∈ Finset.range j, monomial (n k) (a k)) - C v).eval z)
      (fun z => f z - v) atTop (closedBall 0 R) := by
    let T := max R 0
    have hT : 0 ≤ T := le_max_right _ _
    have hs := (hf (T : ℂ)).summable.norm
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT] at hs
    have hu := tendstoUniformlyOn_tsum_nat (f := fun j (z : ℂ) => a j * z ^ n j)
      (s := closedBall 0 R) hs (by
        intro j z hz
        have hR : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall] using hz
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hR.trans (le_max_left _ _)) _) (norm_nonneg _))
    have eqf : (fun z => ∑' j, a j * z ^ n j) = f := funext fun z => (hf z).tsum_eq
    rw [eqf] at hu
    rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
    intro ε he
    filter_upwards [hu ε he] with K hK
    intro z hz
    simpa [eval_finsetSum, dist_eq_norm, sub_sub_sub_cancel_right] using hK z hz
  refine ⟨uniform, ?_⟩
  have hl : TendstoLocallyUniformlyOn
      (fun j z => ((∑ k ∈ Finset.range j, monomial (n k) (a k)) - C v).eval z)
      (fun z => f z - v) atTop Set.univ := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mpr
    intro C _ hc
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hc.isBounded
    exact (uniform R).mono hR
  exact (hl.differentiableOn (Eventually.of_forall fun j =>
    ((∑ k ∈ Finset.range j, monomial (n k) (a k)) - C v).differentiable.differentiableOn)
    isOpen_univ).analyticOnNhd isOpen_univ

private theorem factorNorm (s : Multiset ℂ) (z : ℂ) :
    ‖((s.map fun r => X - C r).prod : ℂ[X]).eval z‖ =
      (s.map fun r => ‖z - r‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih => simp [ih]

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

private theorem zero_transfer (P : ℕ → ℂ[X]) (f : ℂ → ℂ)
    (hAnalytic : AnalyticOnNhd ℂ f Set.univ)
    (hUniform : ∀ R : ℝ, TendstoUniformlyOn (fun j z => (P j).eval z) f atTop (closedBall 0 R))
    (hMany : ∀ m : ℕ, ∃ R : ℝ, ∀ᶠ j : ℕ in atTop, m ≤ ((P j).roots.filter (fun z => ‖z‖ ≤ R)).card) :
    {z | f z = 0}.Infinite := by
  intro hFinite
  have hContinuous : Continuous f := continuousOn_univ.mp hAnalytic.continuousOn
  obtain ⟨B, hB⟩ := (hFinite.image (fun z => ‖z‖)).bddAbove
  let R₀ := max B 0 + 1
  have hR₀ : 0 < R₀ := by dsimp [R₀]; linarith [le_max_right B 0]
  have hzeros (z : ℂ) (hz : f z = 0) : ‖z‖ < R₀ :=
    (hB (mem_image_of_mem (fun z => ‖z‖) hz)).trans_lt (by dsimp [R₀]; linarith [le_max_left B 0])
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

/- ### Part 2: Polynomial Argument Principle and Rouché on a circle -/

private theorem circleIntegral_sub_inv_of_gt {r : ℂ} {t : ℝ} (ht : 0 < t) (hr : t < ‖r‖) :
    (∮ z in C(0, t), (z - r)⁻¹) = 0 := by
  have hdiff : DiffContOnCl ℂ (fun z : ℂ => (z - r)⁻¹) (ball 0 t) := by
    refine DifferentiableOn.diffContOnCl ?_
    intro z hz
    have hzr : z - r ≠ 0 := by
      intro h
      have hzeq : z = r := sub_eq_zero.mp h
      rw [closure_ball (0 : ℂ) ht.ne'] at hz
      have hle : ‖z‖ ≤ t := by simpa [Metric.mem_closedBall] using hz
      rw [hzeq] at hle
      linarith
    exact ((differentiableAt_id.sub (differentiableAt_const r)).inv hzr).differentiableWithinAt
  exact hdiff.circleIntegral_eq_zero ht.le

private theorem card_filter_eq_sum_count {α : Type*} (s : Multiset α) (p : α → Prop) :
    ((s.filter p).card : ℂ) = ∑ x ∈ s.toFinset, if p x then (s.count x : ℂ) else 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    by_cases ha : a ∈ s
    · have hfin : (a ::ₘ s).toFinset = s.toFinset := by
        ext x; simp [ha]
      rw [hfin]
      by_cases hp : p a
      · rw [Multiset.filter_cons_of_pos s hp, Multiset.card_cons, Nat.cast_add, Nat.cast_one, ih]
        rw [← Finset.add_sum_erase _ _ (Multiset.mem_toFinset.mpr ha),
            ← Finset.add_sum_erase _ _ (Multiset.mem_toFinset.mpr ha)]
        simp only [hp, ↓reduceIte, Multiset.count_cons_self, Nat.cast_add, Nat.cast_one]
        have hcongr : ∑ x ∈ s.toFinset.erase a, (if p x then ((a ::ₘ s).count x : ℂ) else 0) =
            ∑ x ∈ s.toFinset.erase a, (if p x then (s.count x : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [Multiset.count_cons_of_ne (Finset.ne_of_mem_erase hx)]
        rw [hcongr]
        ring
      · rw [Multiset.filter_cons_of_neg s hp, ih]
        refine Finset.sum_congr rfl fun x hx => ?_
        by_cases hxa : x = a
        · subst hxa; simp [hp]
        · rw [Multiset.count_cons_of_ne hxa]
    · have hfin : (a ::ₘ s).toFinset = insert a s.toFinset := by
        ext x; simp
      have ha' : a ∉ s.toFinset := by simpa using ha
      rw [hfin, Finset.sum_insert ha']
      have hcongr : ∑ x ∈ s.toFinset, (if p x then ((a ::ₘ s).count x : ℂ) else 0) =
          ∑ x ∈ s.toFinset, (if p x then (s.count x : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxa : x ≠ a := fun h => ha' (h ▸ hx)
        rw [Multiset.count_cons_of_ne hxa]
      rw [hcongr]
      have hcnt : (a ::ₘ s).count a = 1 := by
        rw [Multiset.count_cons_self, Multiset.count_eq_zero.mpr ha]
      by_cases hp : p a
      · rw [Multiset.filter_cons_of_pos s hp, Multiset.card_cons, Nat.cast_add, Nat.cast_one, ih]
        simp [hp, hcnt, add_comm]
      · rw [Multiset.filter_cons_of_neg s hp, ih]
        simp [hp]

private theorem poly_arg_principle (P : ℂ[X]) (t : ℝ) (ht : 0 < t)
    (hnz : ∀ z : ℂ, ‖z‖ = t → P.eval z ≠ 0) :
    (2 * π * I : ℂ)⁻¹ * (∮ z in C(0, t), P.derivative.eval z / P.eval z) =
      ((P.roots.filter (fun r => ‖r‖ < t)).card : ℂ) := by
  have hP0 : P ≠ 0 := by
    intro h
    have hnorm : ‖(t : ℂ)‖ = t := by simp [Complex.norm_real, abs_of_pos ht]
    have := hnz (t : ℂ) hnorm
    simp [h] at this
  have hcongr : (∮ z in C(0, t), P.derivative.eval z / P.eval z) =
      ∮ z in C(0, t), ∑ r ∈ P.roots.toFinset, (P.rootMultiplicity r : ℂ) * (z - r)⁻¹ := by
    refine circleIntegral.integral_congr ht.le fun z hz => ?_
    have hzn : ‖z‖ = t := by simpa [Metric.mem_sphere] using hz
    rw [(IsAlgClosed.splits P).eval_derivative_div_eval_of_ne_zero (hnz z hzn)]
    rw [Finset.sum_multiset_map_count]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [P.count_roots, one_div]
  have hint : ∀ r ∈ P.roots.toFinset,
      CircleIntegrable (fun z : ℂ => (P.rootMultiplicity r : ℂ) * (z - r)⁻¹) 0 t := by
    intro r hr
    have hrroot : P.eval r = 0 := (mem_roots hP0).mp (Multiset.mem_toFinset.mp hr)
    have hrne : ‖r‖ ≠ t := fun heq => hnz r heq hrroot
    refine ContinuousOn.circleIntegrable ht.le ?_
    refine continuousOn_const.mul ?_
    refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun z hz => ?_
    intro hsub
    have hzr : z = r := sub_eq_zero.mp hsub
    have hzn : ‖z‖ = t := by simpa [Metric.mem_sphere] using hz
    exact hrne (hzr ▸ hzn)
  rw [hcongr, circleIntegral.integral_fun_sum hint]
  have hterm : ∀ r ∈ P.roots.toFinset,
      (∮ z in C(0, t), (P.rootMultiplicity r : ℂ) * (z - r)⁻¹) =
        (2 * π * I : ℂ) * (if ‖r‖ < t then (P.roots.count r : ℂ) else 0) := by
    intro r hr
    rw [circleIntegral.integral_const_mul, ← P.count_roots]
    have hrroot : P.eval r = 0 := (mem_roots hP0).mp (Multiset.mem_toFinset.mp hr)
    have hrne : ‖r‖ ≠ t := fun heq => hnz r heq hrroot
    by_cases hlt : ‖r‖ < t
    · have hmem : r ∈ ball (0 : ℂ) t := by simpa [Metric.mem_ball] using hlt
      rw [circleIntegral.integral_sub_inv_of_mem_ball hmem, if_pos hlt, mul_comm]
    · have hgt : t < ‖r‖ := lt_of_le_of_ne (not_lt.mp hlt) hrne.symm
      rw [circleIntegral_sub_inv_of_gt ht hgt, if_neg hlt, mul_zero, mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [← mul_assoc, inv_mul_cancel₀ h2pi, one_mul, card_filter_eq_sum_count]

private theorem poly_rouche (F G : ℂ[X]) (t : ℝ) (ht : 0 < t)
    (hFG : ∀ w : ℂ, ‖w‖ = t → ‖G.eval w‖ < ‖F.eval w‖) :
    (F.roots.filter (fun w => ‖w‖ < t)).card =
      ((F + G).roots.filter (fun w => ‖w‖ < t)).card := by
  let H : ℝ → ℂ[X] := fun s => F + C (s : ℂ) * G
  have hHnz : ∀ s ∈ Icc (0 : ℝ) 1, ∀ w : ℂ, ‖w‖ = t → (H s).eval w ≠ 0 := by
    intro s hs w hw heq
    have hlt := hFG w hw
    have hs0 : 0 ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have hev : F.eval w + (s : ℂ) * G.eval w = 0 := by simpa [H] using heq
    have hFeq : F.eval w = -((s : ℂ) * G.eval w) := eq_neg_of_add_eq_zero_left hev
    have hnorm : ‖F.eval w‖ = s * ‖G.eval w‖ := by
      rw [hFeq, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
    have hle : s * ‖G.eval w‖ ≤ ‖G.eval w‖ := by nlinarith [norm_nonneg (G.eval w)]
    linarith
  let Φ : Set.Icc (0 : ℝ) 1 → ℂ := fun s =>
    (2 * π * I : ℂ)⁻¹ *
      ∫ θ in (0 : ℝ)..(2 * π),
        (deriv (circleMap 0 t) θ) *
          ((F.derivative.eval (circleMap 0 t θ) + (s.1 : ℂ) * G.derivative.eval (circleMap 0 t θ)) /
           (F.eval (circleMap 0 t θ) + (s.1 : ℂ) * G.eval (circleMap 0 t θ)))
  have hΦ_eq : ∀ s : Set.Icc (0 : ℝ) 1,
      Φ s = (((H s.1).roots.filter (fun w => ‖w‖ < t)).card : ℂ) := by
    intro s
    have harg := poly_arg_principle (H s.1) t ht (hHnz s.1 s.2)
    rw [← harg]
    dsimp only [Φ]
    rw [circleIntegral]
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [smul_eq_mul]
    congr 1
    have hd : (H s.1).derivative = F.derivative + C (s.1 : ℂ) * G.derivative := by
      simp [H, derivative_add, derivative_mul, derivative_C]
    simp [H, hd]
  have hΦ_cont : Continuous Φ := by
    refine continuous_const.mul ?_
    let g : Set.Icc (0 : ℝ) 1 × ℝ → ℂ := fun p =>
      (circleMap 0 t p.2 * I) *
        ((F.derivative.eval (circleMap 0 t p.2) + (p.1.1 : ℂ) * G.derivative.eval (circleMap 0 t p.2)) /
         (F.eval (circleMap 0 t p.2) + (p.1.1 : ℂ) * G.eval (circleMap 0 t p.2)))
    have hg_cont : Continuous g := by
      have hcm : Continuous (fun p : Set.Icc (0 : ℝ) 1 × ℝ => circleMap 0 t p.2) :=
        (continuous_circleMap 0 t).comp continuous_snd
      have hs : Continuous (fun p : Set.Icc (0 : ℝ) 1 × ℝ => (p.1.1 : ℂ)) :=
        Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
      refine (hcm.mul continuous_const).mul ?_
      refine Continuous.div ?_ ?_ ?_
      · exact (F.derivative.continuous.comp hcm).add (hs.mul (G.derivative.continuous.comp hcm))
      · exact (F.continuous.comp hcm).add (hs.mul (G.continuous.comp hcm))
      · intro p
        have hw : ‖circleMap 0 t p.2‖ = t := by
          simp [abs_of_pos ht]
        simpa [H] using hHnz p.1.1 p.1.2 (circleMap 0 t p.2) hw
    have hIntCont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := MeasureTheory.volume)
      (f := fun (s : Set.Icc (0 : ℝ) 1) (θ : ℝ) => g (s, θ)) hg_cont (0 : ℝ) (2 * π)
    refine hIntCont.congr fun s => ?_
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp [g, deriv_circleMap]
  let N : Set.Icc (0 : ℝ) 1 → ℕ := fun s => ((H s.1).roots.filter (fun w => ‖w‖ < t)).card
  have hN_re : ∀ s : Set.Icc (0 : ℝ) 1, (N s : ℝ) = (Φ s).re := by
    intro s; rw [hΦ_eq s]; simp [N]
  have hN_real_cont : Continuous (fun s : Set.Icc (0 : ℝ) 1 => (N s : ℝ)) := by
    have : (fun s : Set.Icc (0 : ℝ) 1 => (N s : ℝ)) = Complex.re ∘ Φ := funext hN_re
    rw [this]
    exact Complex.continuous_re.comp hΦ_cont
  let s₀ : Set.Icc (0 : ℝ) 1 := ⟨0, left_mem_Icc.mpr zero_le_one⟩
  let s₁ : Set.Icc (0 : ℝ) 1 := ⟨1, right_mem_Icc.mpr zero_le_one⟩
  have hU_open : IsOpen {s : Set.Icc (0 : ℝ) 1 | N s = N s₀} := by
    have heq : {s : Set.Icc (0 : ℝ) 1 | N s = N s₀} =
        (fun s : Set.Icc (0 : ℝ) 1 => (N s : ℝ)) ⁻¹' Metric.ball (N s₀ : ℝ) 1 := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_ball, Real.dist_eq]
      constructor
      · intro h; simp [h]
      · intro h
        have h1 : (N s : ℝ) - (N s₀ : ℝ) < 1 := (abs_lt.mp h).2
        have h2 : -1 < (N s : ℝ) - (N s₀ : ℝ) := (abs_lt.mp h).1
        have hlt1 : N s < N s₀ + 1 := by exact_mod_cast (by linarith : (N s : ℝ) < (N s₀ : ℝ) + 1)
        have hlt2 : N s₀ < N s + 1 := by exact_mod_cast (by linarith : (N s₀ : ℝ) < (N s : ℝ) + 1)
        omega
    rw [heq]
    exact Metric.isOpen_ball.preimage hN_real_cont
  have hV_open : IsOpen {s : Set.Icc (0 : ℝ) 1 | N s ≠ N s₀} := by
    have heq : {s : Set.Icc (0 : ℝ) 1 | N s ≠ N s₀} =
        (fun s : Set.Icc (0 : ℝ) 1 => (N s : ℝ)) ⁻¹' (Set.Iio ((N s₀ : ℝ) - 1 / 2) ∪ Set.Ioi ((N s₀ : ℝ) + 1 / 2)) := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
      constructor
      · intro hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · left
          have : (N s : ℝ) + 1 ≤ (N s₀ : ℝ) := by exact_mod_cast hlt
          linarith
        · right
          have : (N s₀ : ℝ) + 1 ≤ (N s : ℝ) := by exact_mod_cast hgt
          linarith
      · rintro (h | h) heq
        · rw [heq] at h; linarith
        · rw [heq] at h; linarith
    rw [heq]
    exact (isOpen_Iio.union isOpen_Ioi).preimage hN_real_cont
  have : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hclopen : IsClopen {s : Set.Icc (0 : ℝ) 1 | N s = N s₀} := by
    refine ⟨?_, hU_open⟩
    rw [← isOpen_compl_iff]
    exact hV_open
  have huniv := hclopen.eq_univ ⟨s₀, rfl⟩
  have hs₁_mem : s₁ ∈ {s : Set.Icc (0 : ℝ) 1 | N s = N s₀} := by
    rw [huniv]; trivial
  have hNs : N s₁ = N s₀ := hs₁_mem
  have hH0 : H 0 = F := by simp [H]
  have hH1 : H 1 = F + G := by simp [H]
  simpa [N, s₀, s₁, hH0, hH1] using hNs.symm

/- ### Part 3: Euler operator and reflection -/

private theorem multiset_norm_sum_le (s : Multiset ℂ) :
    ‖s.sum‖ ≤ (s.map (‖·‖)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.sum_cons, Multiset.map_cons]
    exact (norm_add_le a s.sum).trans (add_le_add le_rfl ih)

private theorem multiset_sum_map_le {α : Type*} (s : Multiset α) (f g : α → ℝ)
    (h : ∀ x ∈ s, f x ≤ g x) :
    (s.map f).sum ≤ (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact add_le_add (h a (Multiset.mem_cons_self a s))
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

private theorem multiset_mul_sum (c : ℂ) (s : Multiset ℂ) :
    c * s.sum = (s.map (c * ·)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.sum_cons, Multiset.map_cons, mul_add, ih]

private def eulerOp (N : ℕ) (H : ℂ[X]) : ℂ[X] :=
  C (N : ℂ) * H - X * H.derivative

private theorem coeff_eulerOp (N : ℕ) (H : ℂ[X]) (k : ℕ) :
    (eulerOp N H).coeff k = ((N : ℂ) - (k : ℂ)) * H.coeff k := by
  cases k with
  | zero =>
    simp [eulerOp]
  | succ m =>
    simp only [eulerOp, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_derivative]
    push_cast
    ring

private theorem eulerOp_add (N : ℕ) (P Q : ℂ[X]) :
    eulerOp N (P + Q) = eulerOp N P + eulerOp N Q := by
  ext k
  simp [coeff_eulerOp, mul_add]

private theorem eulerOp_sum {ι : Type*} (s : Finset ι) (N : ℕ) (f : ι → ℂ[X]) :
    eulerOp N (∑ i ∈ s, f i) = ∑ i ∈ s, eulerOp N (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    ext k; simp [coeff_eulerOp]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, eulerOp_add, ih]

private theorem eulerOp_monomial (N k : ℕ) (c : ℂ) :
    eulerOp N (monomial k c) = monomial k (((N : ℂ) - (k : ℂ)) * c) := by
  ext m
  rw [coeff_eulerOp, coeff_monomial, coeff_monomial]
  split_ifs with h
  · subst h; rfl
  · simp

private theorem eulerOp_monomial_self (N : ℕ) (c : ℂ) :
    eulerOp N (monomial N c) = 0 := by
  rw [eulerOp_monomial]
  simp

private theorem eval_zero_eulerOp (N : ℕ) (H : ℂ[X]) :
    (eulerOp N H).eval 0 = (N : ℂ) * H.eval 0 := by
  simp [eulerOp]

private theorem natDegree_eulerOp_le {N : ℕ} {H : ℂ[X]} (hdeg : H.natDegree ≤ N) (hN : 1 ≤ N) :
    (eulerOp N H).natDegree ≤ N - 1 := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
  rw [coeff_eulerOp]
  by_cases hkn : k = N
  · subst hkn; simp
  · have hgt : H.natDegree < k := by omega
    rw [coeff_eq_zero_of_natDegree_lt hgt, mul_zero]

private theorem natDegree_eulerOp_eq {N : ℕ} {Q : ℂ[X]} (hQ : Q ≠ 0) (hdeg : Q.natDegree < N) :
    (eulerOp N Q).natDegree = Q.natDegree := by
  apply le_antisymm
  · refine natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
    rw [coeff_eulerOp, coeff_eq_zero_of_natDegree_lt hk, mul_zero]
  · apply le_natDegree_of_ne_zero
    rw [coeff_eulerOp]
    have hsub : (N : ℂ) - (Q.natDegree : ℂ) ≠ 0 := by
      intro h
      have hEq : (N : ℂ) = (Q.natDegree : ℂ) := sub_eq_zero.mp h
      have hNat : N = Q.natDegree := Nat.cast_injective hEq
      omega
    exact mul_ne_zero hsub (leadingCoeff_ne_zero.mpr hQ)

private theorem derivative_reflect_eq_reflect_eulerOp {N : ℕ} {H : ℂ[X]}
    (hdeg : H.natDegree ≤ N) (hN : 1 ≤ N) :
    (H.reflect N).derivative = (eulerOp N H).reflect (N - 1) := by
  ext k
  rw [coeff_derivative, coeff_reflect, coeff_reflect, coeff_eulerOp]
  by_cases hk : k + 1 ≤ N
  · have hk' : k ≤ N - 1 := by omega
    rw [revAt_le hk, revAt_le hk']
    have hsub : N - (k + 1) = N - 1 - k := by omega
    rw [hsub]
    have hcast : ((N : ℂ) - ((N - 1 - k : ℕ) : ℂ)) = (k : ℂ) + 1 := by
      have hle : N - 1 - k ≤ N := by omega
      have hnat : N = (N - 1 - k) + (k + 1) := by omega
      have hC : (N : ℂ) = ((N - 1 - k : ℕ) : ℂ) + ((k : ℂ) + 1) := by exact_mod_cast hnat
      linear_combination hC
    rw [hcast]
    ring
  · have hk1 : N < k + 1 := by omega
    have hk2 : N - 1 < k := by omega
    rw [revAt_eq_self_of_lt hk1, revAt_eq_self_of_lt hk2]
    have hgt1 : H.natDegree < k + 1 := lt_of_le_of_lt hdeg hk1
    rw [coeff_eq_zero_of_natDegree_lt hgt1, zero_mul]
    by_cases hkn : k = N
    · subst hkn; simp
    · have hgt2 : H.natDegree < k := by omega
      rw [coeff_eq_zero_of_natDegree_lt hgt2, mul_zero]

private theorem natDegree_derivative_eq_pred {p : ℂ[X]} (hp : 0 < p.natDegree) :
    p.derivative.natDegree = p.natDegree - 1 := by
  apply le_antisymm (natDegree_derivative_le p)
  apply le_natDegree_of_ne_zero
  rw [coeff_derivative]
  have hsub : p.natDegree - 1 + 1 = p.natDegree := by omega
  rw [hsub]
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  have hne : ((p.natDegree - 1 : ℕ) : ℂ) + 1 ≠ 0 := by
    have hcast : ((p.natDegree - 1 : ℕ) : ℂ) + 1 = (p.natDegree : ℂ) := by exact_mod_cast hsub
    rw [hcast]
    exact Nat.cast_ne_zero.mpr (by omega)
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hp0) hne

private theorem natDegree_multiset_prod_X_sub_C (s : Multiset ℂ) :
    ((s.map fun r => X - C r).prod : ℂ[X]).natDegree = s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    have hmonic : (X - C r : ℂ[X]).Monic := monic_X_sub_C r
    have hm : ((s.map fun a => X - C a).prod : ℂ[X]).Monic :=
      monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a
    rw [hmonic.natDegree_mul hm, natDegree_X_sub_C, ih, add_comm]

private theorem reflect_prod_X_sub_C (s : Multiset ℂ) (h0 : (0 : ℂ) ∉ s) :
    ((s.map fun r => X - C r).prod : ℂ[X]).reflect s.card =
      C ((s.map fun r => -r).prod) * (s.map fun r => X - C r⁻¹).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    have hr0 : r ≠ 0 := fun h => h0 (h ▸ Multiset.mem_cons_self r s)
    have hs0 : (0 : ℂ) ∉ s := fun h => h0 (Multiset.mem_cons_of_mem h)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm s.card 1]
    rw [reflect_mul (X - C r) _ (by rw [natDegree_X_sub_C]) (by rw [natDegree_multiset_prod_X_sub_C])]
    rw [ih hs0]
    have h1 : (X - C r : ℂ[X]).reflect 1 = C (-r) * (X - C r⁻¹) := by
      ext k
      rw [coeff_reflect]
      match k with
      | 0 =>
        simp [revAt_le (by omega : 0 ≤ 1), hr0]
      | 1 =>
        simp [revAt_le (by omega : 1 ≤ 1)]
      | m + 2 =>
        rw [revAt_eq_self_of_lt (by omega : 1 < m + 2)]
        simp [coeff_X]
    rw [h1, Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, map_mul]
    ring

private theorem roots_reflect_eq {H : ℂ[X]} {N : ℕ} (hdeg : H.natDegree ≤ N) (h0 : H.eval 0 ≠ 0) :
    (H.reflect N).natDegree = N ∧
    (H.reflect N).roots = (N - H.natDegree) • ({0} : Multiset ℂ) + H.roots.map (·⁻¹) := by
  have hH0 : H ≠ 0 := fun h => h0 (by simp [h])
  have h0root : (0 : ℂ) ∉ H.roots := fun h => h0 ((mem_roots hH0).mp h)
  have hcard : H.roots.card = H.natDegree := (IsAlgClosed.splits H).natDegree_eq_card_roots.symm
  have hfac : H = C H.leadingCoeff * (H.roots.map fun r => X - C r).prod :=
    (C_leadingCoeff_mul_prod_multiset_X_sub_C hcard).symm
  have hNsplit : N = (N - H.natDegree) + H.roots.card := by omega
  have hrefl : H.reflect N =
      C (H.leadingCoeff * (H.roots.map fun r => -r).prod) *
        (X ^ (N - H.natDegree) * (H.roots.map fun r => X - C r⁻¹).prod) := by
    calc
      H.reflect N =
          (C H.leadingCoeff * (H.roots.map fun r => X - C r).prod).reflect
            ((N - H.natDegree) + H.roots.card) := by
        rw [← hfac, ← hNsplit]
      _ = (C H.leadingCoeff).reflect (N - H.natDegree) *
          ((H.roots.map fun r => X - C r).prod).reflect H.roots.card := by
        have hd1 : (C H.leadingCoeff : ℂ[X]).natDegree ≤ N - H.natDegree := by simp
        have hd2 : ((H.roots.map fun r => X - C r).prod : ℂ[X]).natDegree ≤ H.roots.card :=
          (natDegree_multiset_prod_X_sub_C H.roots).le
        exact reflect_mul (C H.leadingCoeff) ((H.roots.map fun r => X - C r).prod) hd1 hd2
      _ = (C H.leadingCoeff * X ^ (N - H.natDegree)) *
          (C ((H.roots.map fun r => -r).prod) * (H.roots.map fun r => X - C r⁻¹).prod) := by
        rw [reflect_prod_X_sub_C H.roots h0root]
        have hC : (C H.leadingCoeff : ℂ[X]).reflect (N - H.natDegree) =
            C H.leadingCoeff * X ^ (N - H.natDegree) := by
          simp
        rw [hC]
      _ = C (H.leadingCoeff * (H.roots.map fun r => -r).prod) *
          (X ^ (N - H.natDegree) * (H.roots.map fun r => X - C r⁻¹).prod) := by
        rw [map_mul]; ring
  have hcne : H.leadingCoeff * (H.roots.map fun r => -r).prod ≠ 0 := by
    refine mul_ne_zero (leadingCoeff_ne_zero.mpr hH0) ?_
    intro hprod
    rw [Multiset.prod_eq_zero_iff] at hprod
    obtain ⟨r, hr, hneg⟩ := Multiset.mem_map.mp hprod
    exact h0root (neg_eq_zero.mp hneg ▸ hr)
  have hprod_ne : ((H.roots.map fun r => X - C r⁻¹).prod : ℂ[X]) ≠ 0 := by
    have hm : ((H.roots.map fun r => X - C r⁻¹).prod : ℂ[X]).Monic :=
      monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a⁻¹
    exact hm.ne_zero
  have hX_ne : (X ^ (N - H.natDegree) : ℂ[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  have hroots : (H.reflect N).roots = (N - H.natDegree) • ({0} : Multiset ℂ) + H.roots.map (·⁻¹) := by
    rw [hrefl, roots_C_mul _ hcne, roots_mul (mul_ne_zero hX_ne hprod_ne), roots_X_pow]
    have hmap : ((H.roots.map fun r => X - C r⁻¹).prod : ℂ[X]).roots = H.roots.map (·⁻¹) := by
      have hcomp : (H.roots.map fun r => X - C r⁻¹) = (H.roots.map (·⁻¹)).map fun a => X - C a := by
        simp [Multiset.map_map]
      rw [hcomp, roots_multiset_prod_X_sub_C]
    rw [hmap]
  have hdeg_eq : (H.reflect N).natDegree = N := by
    rw [(IsAlgClosed.splits (H.reflect N)).natDegree_eq_card_roots, hroots]
    simp only [Multiset.card_add, Multiset.card_nsmul, Multiset.card_singleton, mul_one,
      Multiset.card_map, hcard]
    omega
  exact ⟨hdeg_eq, hroots⟩

private theorem roots_reflect_card_ge {H : ℂ[X]} {N : ℕ} {ρ : ℝ}
    (hdeg : H.natDegree ≤ N) (h0 : H.eval 0 ≠ 0) (hρ : 0 < ρ) :
    ((H.reflect N).roots.filter (fun w => ρ⁻¹ ≤ ‖w‖)).card =
      (H.roots.filter (fun z => ‖z‖ ≤ ρ)).card := by
  have hH0 : H ≠ 0 := fun h => h0 (by simp [h])
  have h0root : (0 : ℂ) ∉ H.roots := fun h => h0 ((mem_roots hH0).mp h)
  rw [(roots_reflect_eq hdeg h0).2, Multiset.filter_add, Multiset.card_add]
  have hzero : (((N - H.natDegree) • ({0} : Multiset ℂ)).filter (fun w => ρ⁻¹ ≤ ‖w‖)) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro w hw
    have hw0 : w = 0 := by
      have : w ∈ ({0} : Multiset ℂ) := Multiset.mem_of_mem_nsmul hw
      simpa using this
    subst hw0
    simp [not_le.mpr (inv_pos.mpr hρ)]
  rw [hzero, Multiset.card_zero, zero_add, Multiset.filter_map, Multiset.card_map]
  congr 1
  refine Multiset.filter_congr fun z hz => ?_
  have hz0 : z ≠ 0 := fun h => h0root (h ▸ hz)
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  simp only [Function.comp_apply, norm_inv]
  exact inv_le_inv₀ hρ hzn

/- ### Part 4: Forward Euler root bound -/

private theorem eulerOp_forward_step {Q : ℂ[X]} {N : ℕ} {R : ℝ}
    (hQ : Q ≠ 0) (hdeg : Q.natDegree < N) (hR : 0 ≤ R)
    (hroots : ∀ z ∈ Q.roots, ‖z‖ ≤ R) :
    eulerOp N Q ≠ 0 ∧
    (eulerOp N Q).natDegree = Q.natDegree ∧
    ∀ z ∈ (eulerOp N Q).roots, ‖z‖ ≤ R * ((N : ℝ) / ((N : ℝ) - (Q.natDegree : ℝ))) := by
  have hdeg_eq : (eulerOp N Q).natDegree = Q.natDegree := natDegree_eulerOp_eq hQ hdeg
  have hne : eulerOp N Q ≠ 0 := by
    intro h
    have hcoeff := congrArg (fun p : ℂ[X] => p.coeff Q.natDegree) h
    rw [coeff_eulerOp, coeff_zero] at hcoeff
    have hsub : (N : ℂ) - (Q.natDegree : ℂ) ≠ 0 := by
      intro he
      have : N = Q.natDegree := Nat.cast_injective (sub_eq_zero.mp he)
      omega
    exact mul_ne_zero hsub (leadingCoeff_ne_zero.mpr hQ) hcoeff
  refine ⟨hne, hdeg_eq, ?_⟩
  intro z hz
  by_contra! hlt
  have hNd : 0 < (N : ℝ) - (Q.natDegree : ℝ) := by
    have : (Q.natDegree : ℝ) < (N : ℝ) := by exact_mod_cast hdeg
    linarith
  have hfrac : 1 ≤ (N : ℝ) / ((N : ℝ) - (Q.natDegree : ℝ)) := by
    rw [one_le_div hNd]
    linarith [Nat.cast_nonneg (α := ℝ) Q.natDegree]
  have hRz : R < ‖z‖ := by nlinarith
  have hzpos : 0 < ‖z‖ := lt_of_le_of_lt hR hRz
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
  have hQz : Q.eval z ≠ 0 := by
    intro hze
    have hmem : z ∈ Q.roots := (mem_roots hQ).mpr hze
    linarith [hroots z hmem]
  have heul : (eulerOp N Q).eval z = 0 := (mem_roots hne).mp hz
  have hlog : Q.derivative.eval z / Q.eval z = (N : ℂ) / z := by
    have heq : (N : ℂ) * Q.eval z - z * Q.derivative.eval z = 0 := by
      simpa [eulerOp] using heul
    have hmul : z * Q.derivative.eval z = (N : ℂ) * Q.eval z := (sub_eq_zero.mp heq).symm
    rw [div_eq_div_iff hQz hz0]
    linear_combination hmul
  have hsum : (N : ℂ) / z = (Q.roots.map fun r => 1 / (z - r)).sum := by
    rw [← hlog, (IsAlgClosed.splits Q).eval_derivative_div_eval_of_ne_zero hQz]
  have hnorm_le : (N : ℝ) / ‖z‖ ≤ (Q.roots.card : ℝ) / (‖z‖ - R) := by
    have hLHS : ‖(N : ℂ) / z‖ = (N : ℝ) / ‖z‖ := by
      rw [norm_div, Complex.norm_natCast]
    rw [← hLHS, hsum]
    have htri : ‖(Q.roots.map fun r => (1 : ℂ) / (z - r)).sum‖ ≤
        (Q.roots.map fun r => ‖(1 : ℂ) / (z - r)‖).sum := by
      simpa [Multiset.map_map] using
        multiset_norm_sum_le (Q.roots.map fun r => (1 : ℂ) / (z - r))
    have hterm : (Q.roots.map fun r => ‖(1 : ℂ) / (z - r)‖).sum ≤
        (Q.roots.map fun _ => (‖z‖ - R)⁻¹).sum := by
      refine multiset_sum_map_le Q.roots _ _ fun r hr => ?_
      have hrr : ‖r‖ ≤ R := hroots r hr
      have hdist : ‖z‖ - R ≤ ‖z - r‖ := by
        have ht := norm_sub_norm_le z r
        linarith
      have hpos : 0 < ‖z‖ - R := by linarith
      rw [one_div, norm_inv]
      exact inv_anti₀ hpos hdist
    have hcard_sum : (Q.roots.map fun _ => (‖z‖ - R)⁻¹).sum = (Q.roots.card : ℝ) / (‖z‖ - R) := by
      simp [div_eq_mul_inv]
    exact htri.trans (hterm.trans_eq hcard_sum)
  have hcard : Q.roots.card = Q.natDegree := (IsAlgClosed.splits Q).natDegree_eq_card_roots.symm
  rw [hcard] at hnorm_le
  have hmul : (N : ℝ) * (‖z‖ - R) ≤ (Q.natDegree : ℝ) * ‖z‖ := by
    exact (div_le_div_iff₀ hzpos (by linarith)).mp hnorm_le
  have hbound : ‖z‖ ≤ R * ((N : ℝ) / ((N : ℝ) - (Q.natDegree : ℝ))) := by
    rw [← mul_div_assoc, le_div_iff₀ hNd]
    linarith
  linarith

/- ### Part 5: Backward root-count bound via annulus pigeonhole + Gauss-Lucas + Rouché -/

private theorem re_div_sub_ge {w α : ℂ} {a t : ℝ} (ha : 0 ≤ a) (hat : a < t)
    (hw : ‖w‖ = t) (hα : ‖α‖ ≤ a) :
    t / (t + a) ≤ (w / (w - α)).re := by
  have htpos : 0 < t := lt_of_le_of_lt ha hat
  have hsub_ne : w - α ≠ 0 := by
    intro h
    have hweq : w = α := sub_eq_zero.mp h
    rw [hweq] at hw
    linarith
  have hns_pos : 0 < Complex.normSq (w - α) := Complex.normSq_pos.mpr hsub_ne
  have hta_pos : 0 < t + a := by linarith
  have hre : (w / (w - α)).re =
      (w.re * (w.re - α.re) + w.im * (w.im - α.im)) / Complex.normSq (w - α) := by
    rw [Complex.div_re, sub_re, sub_im, add_div]
  rw [hre, div_le_div_iff₀ hta_pos hns_pos]
  have hw2 : w.re ^ 2 + w.im ^ 2 = t ^ 2 := by
    have h1 := Complex.sq_norm w
    rw [hw, Complex.normSq_apply] at h1
    linarith
  have hα2 : α.re ^ 2 + α.im ^ 2 = ‖α‖ ^ 2 := by
    have h1 := Complex.sq_norm α
    rw [Complex.normSq_apply] at h1
    linarith
  have hns : Complex.normSq (w - α) =
      (w.re - α.re) ^ 2 + (w.im - α.im) ^ 2 := by
    rw [Complex.normSq_apply, sub_re, sub_im]; ring
  rw [hns]
  set c : ℝ := w.re * α.re + w.im * α.im
  have hcs : c ^ 2 ≤ t ^ 2 * ‖α‖ ^ 2 := by
    have hdiff : 0 ≤ (w.re * α.im - w.im * α.re) ^ 2 := sq_nonneg _
    have hid : c ^ 2 + (w.re * α.im - w.im * α.re) ^ 2 =
        (w.re ^ 2 + w.im ^ 2) * (α.re ^ 2 + α.im ^ 2) := by
      dsimp [c]; ring
    rw [hw2, hα2] at hid
    linarith
  have hc_ge : -(t * ‖α‖) ≤ c := by
    have h1 : (c + t * ‖α‖) * (t * ‖α‖ - c) = t ^ 2 * ‖α‖ ^ 2 - c ^ 2 := by ring
    have hnonneg : 0 ≤ t * ‖α‖ := mul_nonneg htpos.le (norm_nonneg α)
    by_contra! hlt
    have hneg1 : c + t * ‖α‖ < 0 := by linarith
    have hpos2 : 0 < t * ‖α‖ - c := by linarith
    have hprod : (c + t * ‖α‖) * (t * ‖α‖ - c) < 0 := mul_neg_of_neg_of_pos hneg1 hpos2
    linarith
  have hα_nonneg : 0 ≤ ‖α‖ := norm_nonneg α
  have hfactor : 0 ≤ t * (t + ‖α‖) * (a - ‖α‖) := by
    have h1 : 0 ≤ t * (t + ‖α‖) := by positivity
    have h2 : 0 ≤ a - ‖α‖ := by linarith
    exact mul_nonneg h1 h2
  have hident :
      (w.re * (w.re - α.re) + w.im * (w.im - α.im)) * (t + a) -
        t * ((w.re - α.re) ^ 2 + (w.im - α.im) ^ 2) =
      t ^ 2 * a - t * ‖α‖ ^ 2 + (t - a) * c := by
    have h1 : w.re * (w.re - α.re) + w.im * (w.im - α.im) = t ^ 2 - c := by
      dsimp [c]; linarith [hw2]
    have h2 : (w.re - α.re) ^ 2 + (w.im - α.im) ^ 2 = t ^ 2 - 2 * c + ‖α‖ ^ 2 := by
      dsimp [c]; linarith [hw2, hα2]
    rw [h1, h2]
    ring
  have hineq : t * (t + ‖α‖) * (a - ‖α‖) ≤ t ^ 2 * a - t * ‖α‖ ^ 2 + (t - a) * c := by
    nlinarith
  linarith

private theorem derivative_roots_bound {g : ℂ[X]} {N m₀ : ℕ} {r₁ : ℝ}
    (hdeg : g.natDegree = N) (hm₀ : 1 ≤ m₀) (hN : 2 * m₀ ≤ N) (hr₁ : 0 < r₁)
    (hcard : (g.roots.filter (fun w => r₁ ≤ ‖w‖)).card < m₀) :
    ((g.derivative).roots.filter
      (fun w => r₁ * (1 + (5 * (m₀ : ℝ)) / ((N : ℝ) - 2 * (m₀ : ℝ) + 2)) ^ m₀ ≤ ‖w‖)).card < m₀ := by
  have hg0 : g ≠ 0 := by intro h; simp [h] at hdeg; omega
  set δ : ℝ := (5 * (m₀ : ℝ)) / ((N : ℝ) - 2 * (m₀ : ℝ) + 2)
  set lam : ℝ := 1 + δ
  have hden_pos : 0 < (N : ℝ) - 2 * (m₀ : ℝ) + 2 := by
    have : 2 * (m₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hm₀_pos : (0 : ℝ) < (m₀ : ℝ) := by exact_mod_cast (by omega : 0 < m₀)
  have hδ_pos : 0 < δ := div_pos (by positivity) hden_pos
  have hlam_gt : 1 < lam := by dsimp [lam]; linarith
  have hlam_pos : 0 < lam := by linarith
  -- Annulus pigeonhole: find an empty annulus among the m₀ concentric annuli
  have hex_annulus : ∃ i < m₀, ∀ w ∈ g.roots, ¬(r₁ * lam ^ i ≤ ‖w‖ ∧ ‖w‖ < r₁ * lam ^ (i + 1)) := by
    by_contra! hall
    let f : ℕ → ℂ := fun i => if h : i < m₀ then Classical.choose (hall i h) else 0
    have hf_spec : ∀ i (hi : i < m₀),
        f i ∈ g.roots ∧ r₁ * lam ^ i ≤ ‖f i‖ ∧ ‖f i‖ < r₁ * lam ^ (i + 1) := by
      intro i hi
      simpa [f, hi] using Classical.choose_spec (hall i hi)
    have hinj : Set.InjOn f (Finset.range m₀ : Set ℕ) := by
      intro i hi j hj heq
      have hi' : i < m₀ := Finset.mem_range.mp hi
      have hj' : j < m₀ := Finset.mem_range.mp hj
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h1 := (hf_spec i hi').2.2
        have h2 := (hf_spec j hj').2.1
        have hpow : lam ^ (i + 1) ≤ lam ^ j := pow_le_pow_right₀ hlam_gt.le hlt
        have hmul : r₁ * lam ^ (i + 1) ≤ r₁ * lam ^ j := mul_le_mul_of_nonneg_left hpow hr₁.le
        rw [heq] at h1
        linarith
      · have h1 := (hf_spec j hj').2.2
        have h2 := (hf_spec i hi').2.1
        have hpow : lam ^ (j + 1) ≤ lam ^ i := pow_le_pow_right₀ hlam_gt.le hgt
        have hmul : r₁ * lam ^ (j + 1) ≤ r₁ * lam ^ i := mul_le_mul_of_nonneg_left hpow hr₁.le
        rw [← heq] at h1
        linarith
    have hsub : (Finset.range m₀).image f ⊆ (g.roots.filter (fun w => r₁ ≤ ‖w‖)).toFinset := by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
      have hi' : i < m₀ := Finset.mem_range.mp hi
      rw [Multiset.mem_toFinset, Multiset.mem_filter]
      refine ⟨(hf_spec i hi').1, ?_⟩
      have hpow : (1 : ℝ) ≤ lam ^ i := one_le_pow₀ hlam_gt.le
      have := (hf_spec i hi').2.1
      nlinarith
    have h1 : m₀ = ((Finset.range m₀).image f).card := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    have h2 : ((Finset.range m₀).image f).card ≤ (g.roots.filter (fun w => r₁ ≤ ‖w‖)).toFinset.card :=
      Finset.card_le_card hsub
    have h3 : (g.roots.filter (fun w => r₁ ≤ ‖w‖)).toFinset.card ≤
        (g.roots.filter (fun w => r₁ ≤ ‖w‖)).card := Multiset.toFinset_card_le _
    omega
  obtain ⟨i, hi, hempty⟩ := hex_annulus
  set a : ℝ := r₁ * lam ^ i
  set b : ℝ := r₁ * lam ^ (i + 1)
  set t : ℝ := a * (1 + lam) / 2
  have ha_pos : 0 < a := mul_pos hr₁ (pow_pos hlam_pos i)
  have hb_eq : b = a * lam := by dsimp [a, b]; rw [pow_succ]; ring
  have hat : a < t := by dsimp [t]; nlinarith
  have htb : t < b := by rw [hb_eq]; dsimp [t]; nlinarith
  have ht_pos : 0 < t := lt_trans ha_pos hat
  have ha_ge : r₁ ≤ a := by
    have h1 : (1 : ℝ) ≤ lam ^ i := one_le_pow₀ hlam_gt.le
    dsimp [a]; nlinarith
  have hb_le : b ≤ r₁ * lam ^ m₀ := by
    have hpow : lam ^ (i + 1) ≤ lam ^ m₀ := pow_le_pow_right₀ hlam_gt.le (by omega)
    dsimp [b]
    exact mul_le_mul_of_nonneg_left hpow hr₁.le
  -- Split g = P_in * P_out
  set U : Multiset ℂ := g.roots.filter (fun w => ‖w‖ < a)
  set V : Multiset ℂ := g.roots.filter (fun w => ¬(‖w‖ < a))
  have hUV : g.roots = U + V := (Multiset.filter_add_not (fun w : ℂ => ‖w‖ < a) g.roots).symm
  have hV_ge_b : ∀ w ∈ V, b ≤ ‖w‖ := by
    intro w hw
    have ⟨hmem, hnotlt⟩ := Multiset.mem_filter.mp hw
    have hge : a ≤ ‖w‖ := not_lt.mp hnotlt
    by_contra! hlt
    exact hempty w hmem ⟨hge, hlt⟩
  have hV_le_filter : V ≤ g.roots.filter (fun w => r₁ ≤ ‖w‖) :=
    Multiset.monotone_filter_right g.roots fun w hw => le_trans ha_ge (not_lt.mp hw)
  have hV_card : V.card < m₀ := lt_of_le_of_lt (Multiset.card_le_card hV_le_filter) hcard
  have hUV_card : U.card + V.card = N := by
    have htot := (IsAlgClosed.splits g).natDegree_eq_card_roots
    rw [hdeg, hUV, Multiset.card_add] at htot
    omega
  have hU_ge : 2 ≤ U.card := by omega
  let P_in : ℂ[X] := (U.map fun r => X - C r).prod
  let P_out : ℂ[X] := C g.leadingCoeff * (V.map fun r => X - C r).prod
  have hg_eq : g = P_in * P_out := by
    have htot : g.roots.card = g.natDegree := (IsAlgClosed.splits g).natDegree_eq_card_roots.symm
    have hfac := (C_leadingCoeff_mul_prod_multiset_X_sub_C htot).symm
    rw [hUV, Multiset.map_add, Multiset.prod_add] at hfac
    calc
      g = C g.leadingCoeff * ((U.map fun r => X - C r).prod * (V.map fun r => X - C r).prod) := hfac
      _ = P_in * P_out := by dsimp [P_in, P_out]; ring
  have hPin_roots : P_in.roots = U := roots_multiset_prod_X_sub_C U
  have hPin_deg : P_in.natDegree = U.card := natDegree_multiset_prod_X_sub_C U
  have hPin_ne : P_in ≠ 0 := by intro h; simp [h] at hPin_deg; omega
  have hPout_roots : P_out.roots = V := by
    dsimp [P_out]
    rw [roots_C_mul _ (leadingCoeff_ne_zero.mpr hg0), roots_multiset_prod_X_sub_C]
  have hPout_ne : P_out ≠ 0 := by
    dsimp [P_out]
    refine mul_ne_zero (C_ne_zero.mpr (leadingCoeff_ne_zero.mpr hg0)) ?_
    have hm : ((V.map fun a => X - C a).prod : ℂ[X]).Monic :=
      monic_multiset_prod_of_monic _ _ fun r _ => monic_X_sub_C r
    exact hm.ne_zero
  let F : ℂ[X] := P_in.derivative * P_out
  let G : ℂ[X] := P_in * P_out.derivative
  have hderiv_eq : g.derivative = F + G := by
    rw [hg_eq, derivative_mul]
  -- Rouché inequality on ‖w‖ = t
  have hFG : ∀ w : ℂ, ‖w‖ = t → ‖G.eval w‖ < ‖F.eval w‖ := by
    intro w hw
    have hPin_w : P_in.eval w ≠ 0 := by
      intro he
      have hwU : w ∈ U := hPin_roots ▸ (mem_roots hPin_ne).mpr he
      have hlt := (Multiset.mem_filter.mp hwU).2
      linarith
    have hPout_w : P_out.eval w ≠ 0 := by
      intro he
      have hwV : w ∈ V := hPout_roots ▸ (mem_roots hPout_ne).mpr he
      have hge := hV_ge_b w hwV
      linarith
    -- Lower bound on ‖P_in'(w) / P_in(w)‖
    have hlow : (U.card : ℝ) / (t + a) ≤ ‖P_in.derivative.eval w / P_in.eval w‖ := by
      have hlog := (IsAlgClosed.splits P_in).eval_derivative_div_eval_of_ne_zero hPin_w
      rw [hPin_roots] at hlog
      have hmul : w * (P_in.derivative.eval w / P_in.eval w) = (U.map fun α => w / (w - α)).sum := by
        rw [hlog, multiset_mul_sum, Multiset.map_map]
        congr 1
        refine Multiset.map_congr rfl fun α _ => ?_
        simp [Function.comp_apply, div_eq_mul_inv]
      have hre_sum : (w * (P_in.derivative.eval w / P_in.eval w)).re =
          (U.map fun α => (w / (w - α)).re).sum := by
        rw [hmul]
        clear hmul
        induction U using Multiset.induction_on with
        | empty => simp
        | cons α s ih => simp [ih]
      have hre_ge : (U.card : ℝ) * (t / (t + a)) ≤ (U.map fun α => (w / (w - α)).re).sum := by
        have hconst : (U.card : ℝ) * (t / (t + a)) = (U.map fun _ => t / (t + a)).sum := by
          simp
        rw [hconst]
        refine multiset_sum_map_le U _ _ fun α hα => ?_
        have hα_lt : ‖α‖ < a := (Multiset.mem_filter.mp hα).2
        exact re_div_sub_ge ha_pos.le hat hw hα_lt.le
      have hre_le : (w * (P_in.derivative.eval w / P_in.eval w)).re ≤
          t * ‖P_in.derivative.eval w / P_in.eval w‖ := by
        calc
          (w * (P_in.derivative.eval w / P_in.eval w)).re ≤
              ‖w * (P_in.derivative.eval w / P_in.eval w)‖ := Complex.re_le_norm _
          _ = t * ‖P_in.derivative.eval w / P_in.eval w‖ := by rw [norm_mul, hw]
      have h1 : t * ((U.card : ℝ) / (t + a)) ≤ t * ‖P_in.derivative.eval w / P_in.eval w‖ := by
        have h2 : (U.card : ℝ) * (t / (t + a)) = t * ((U.card : ℝ) / (t + a)) := by ring
        linarith
      exact le_of_mul_le_mul_left h1 ht_pos
    -- Upper bound on ‖P_out'(w) / P_out(w)‖
    have hup : ‖P_out.derivative.eval w / P_out.eval w‖ ≤ (V.card : ℝ) / (b - t) := by
      have hlog := (IsAlgClosed.splits P_out).eval_derivative_div_eval_of_ne_zero hPout_w
      rw [hPout_roots] at hlog
      rw [hlog]
      have htri : ‖(V.map fun β => (1 : ℂ) / (w - β)).sum‖ ≤
          (V.map fun β => ‖(1 : ℂ) / (w - β)‖).sum := by
        simpa [Multiset.map_map] using
          multiset_norm_sum_le (V.map fun β => (1 : ℂ) / (w - β))
      have hterm : (V.map fun β => ‖(1 : ℂ) / (w - β)‖).sum ≤
          (V.map fun _ => (b - t)⁻¹).sum := by
        refine multiset_sum_map_le V _ _ fun β hβ => ?_
        have hβb : b ≤ ‖β‖ := hV_ge_b β hβ
        have hdist : b - t ≤ ‖w - β‖ := by
          have ht1 := norm_sub_norm_le β w
          rw [norm_sub_rev] at ht1
          linarith
        rw [one_div, norm_inv]
        exact inv_anti₀ (by linarith) hdist
      have hcard_sum : (V.map fun _ => (b - t)⁻¹).sum = (V.card : ℝ) / (b - t) := by
        simp [div_eq_mul_inv]
      exact htri.trans (hterm.trans_eq hcard_sum)
    -- Strict comparison (V.card) / (b - t) < (U.card) / (t + a)
    have hstrict : (V.card : ℝ) / (b - t) < (U.card : ℝ) / (t + a) := by
      have hbt : b - t = a * δ / 2 := by rw [hb_eq]; dsimp [t, lam]; ring
      have hta : t + a = a * (4 + δ) / 2 := by dsimp [t, lam]; ring
      rw [hbt, hta, div_lt_div_iff₀ (by positivity) (by positivity)]
      have hVle : (V.card : ℝ) ≤ (m₀ : ℝ) - 1 := by
        have : V.card + 1 ≤ m₀ := hV_card
        have : (V.card : ℝ) + 1 ≤ (m₀ : ℝ) := by exact_mod_cast this
        linarith
      have hUVR : (U.card : ℝ) + (V.card : ℝ) = (N : ℝ) := by exact_mod_cast hUV_card
      have hdiff_ge : (N : ℝ) - 2 * (m₀ : ℝ) + 2 ≤ (U.card : ℝ) - (V.card : ℝ) := by linarith
      have hmul_δ : ((N : ℝ) - 2 * (m₀ : ℝ) + 2) * δ = 5 * (m₀ : ℝ) := by
        dsimp [δ]
        exact mul_div_cancel₀ _ hden_pos.ne'
      have hkey : 4 * (V.card : ℝ) < ((U.card : ℝ) - (V.card : ℝ)) * δ := by
        have h1 : 5 * (m₀ : ℝ) ≤ ((U.card : ℝ) - (V.card : ℝ)) * δ := by
          rw [← hmul_δ]
          exact mul_le_mul_of_nonneg_right hdiff_ge hδ_pos.le
        linarith
      nlinarith
    have hdiv_lt : ‖P_out.derivative.eval w / P_out.eval w‖ <
        ‖P_in.derivative.eval w / P_in.eval w‖ := lt_of_le_of_lt hup (lt_of_lt_of_le hstrict hlow)
    rw [norm_div, norm_div] at hdiv_lt
    have hpos1 : 0 < ‖P_in.eval w‖ := norm_pos_iff.mpr hPin_w
    have hpos2 : 0 < ‖P_out.eval w‖ := norm_pos_iff.mpr hPout_w
    have hcross : ‖P_out.derivative.eval w‖ * ‖P_in.eval w‖ <
        ‖P_in.derivative.eval w‖ * ‖P_out.eval w‖ := by
      exact (div_lt_div_iff₀ hpos2 hpos1).mp hdiv_lt
    simpa [F, G, eval_mul, norm_mul, mul_comm] using hcross
  -- Apply Polynomial Rouché
  have hrouche := poly_rouche F G t ht_pos hFG
  rw [← hderiv_eq] at hrouche
  -- Count roots of F = P_in' * P_out in ‖w‖ < t using Gauss-Lucas
  have hPin_pos_deg : 0 < P_in.degree := by
    rw [degree_eq_natDegree hPin_ne, hPin_deg]
    exact_mod_cast (by omega : 0 < U.card)
  have hPin'_deg : P_in.derivative.natDegree = U.card - 1 := by
    rw [natDegree_derivative_eq_pred (by omega), hPin_deg]
  have hPin'_ne : P_in.derivative ≠ 0 := by
    intro h; simp [h] at hPin'_deg; omega
  have hF_roots : F.roots = P_in.derivative.roots + P_out.roots := by
    dsimp [F]
    exact roots_mul (mul_ne_zero hPin'_ne hPout_ne)
  have hPin'_in : ∀ z ∈ P_in.derivative.roots, ‖z‖ < t := by
    intro z hz
    have hzset : z ∈ P_in.derivative.rootSet ℂ := by
      rw [mem_rootSet_of_ne hPin'_ne, coe_aeval_eq_eval]
      exact (mem_roots hPin'_ne).mp hz
    have hgl := Polynomial.rootSet_derivative_subset_convexHull_rootSet hPin_pos_deg hzset
    have hsub : P_in.rootSet ℂ ⊆ Metric.ball (0 : ℂ) a := by
      intro r hr
      rw [mem_rootSet_of_ne hPin_ne, coe_aeval_eq_eval] at hr
      have hrU : r ∈ U := hPin_roots ▸ (mem_roots hPin_ne).mpr hr
      simpa [Metric.mem_ball] using (Multiset.mem_filter.mp hrU).2
    have hmem_ball : z ∈ Metric.ball (0 : ℂ) a :=
      convexHull_min hsub (convex_ball (0 : ℂ) a) hgl
    have hza : ‖z‖ < a := by simpa [Metric.mem_ball] using hmem_ball
    exact lt_trans hza hat
  have hPin'_count : (P_in.derivative.roots.filter (fun w => ‖w‖ < t)).card = U.card - 1 := by
    rw [Multiset.filter_eq_self.mpr hPin'_in,
      ← (IsAlgClosed.splits P_in.derivative).natDegree_eq_card_roots, hPin'_deg]
  have hPout_count : (P_out.roots.filter (fun w => ‖w‖ < t)).card = 0 := by
    rw [hPout_roots, Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro w hw
    linarith [hV_ge_b w hw]
  have hF_count : (F.roots.filter (fun w => ‖w‖ < t)).card = U.card - 1 := by
    rw [hF_roots, Multiset.filter_add, Multiset.card_add, hPin'_count, hPout_count, add_zero]
  have hgd_lt_t : (g.derivative.roots.filter (fun w => ‖w‖ < t)).card = U.card - 1 := by
    rw [← hrouche, hF_count]
  -- Monotonicity from t to r₁ * lam ^ m₀ and complement count
  have hgd_lt_r2 : U.card - 1 ≤ (g.derivative.roots.filter (fun w => ‖w‖ < r₁ * lam ^ m₀)).card := by
    rw [← hgd_lt_t]
    exact Multiset.card_le_card (Multiset.monotone_filter_right _ fun w hw =>
      lt_of_lt_of_le (lt_trans hw htb) hb_le)
  have hgd_tot : g.derivative.roots.card = N - 1 := by
    rw [← (IsAlgClosed.splits g.derivative).natDegree_eq_card_roots,
      natDegree_derivative_eq_pred (by omega), hdeg]
  have hsplit : (g.derivative.roots.filter (fun w => ‖w‖ < r₁ * lam ^ m₀)).card +
      (g.derivative.roots.filter (fun w => r₁ * lam ^ m₀ ≤ ‖w‖)).card = N - 1 := by
    have hfilt : g.derivative.roots.filter (fun w => r₁ * lam ^ m₀ ≤ ‖w‖) =
        g.derivative.roots.filter (fun w => ¬(‖w‖ < r₁ * lam ^ m₀)) :=
      Multiset.filter_congr fun _ _ => not_lt.symm
    rw [hfilt, ← Multiset.card_add, Multiset.filter_add_not, hgd_tot]
  omega

private theorem eulerOp_backward_step {H : ℂ[X]} {N m₀ : ℕ} {ρ : ℝ}
    (hm₀ : 1 ≤ m₀) (hN : 2 * m₀ ≤ N) (hdeg : H.natDegree ≤ N) (h0 : H.eval 0 ≠ 0) (hρ : 0 < ρ)
    (hcard : (H.roots.filter
      (fun z => ‖z‖ ≤ ρ * (1 + (5 * (m₀ : ℝ)) / ((N : ℝ) - 2 * (m₀ : ℝ) + 2)) ^ m₀)).card < m₀) :
    ((eulerOp N H).roots.filter (fun z => ‖z‖ ≤ ρ)).card < m₀ := by
  set lam : ℝ := 1 + (5 * (m₀ : ℝ)) / ((N : ℝ) - 2 * (m₀ : ℝ) + 2)
  have hden_pos : 0 < (N : ℝ) - 2 * (m₀ : ℝ) + 2 := by
    have : 2 * (m₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hm₀_pos : (0 : ℝ) < (m₀ : ℝ) := by exact_mod_cast (by omega : 0 < m₀)
  have hlam_pos : 0 < lam := by dsimp [lam]; positivity
  have hρlam_pos : 0 < ρ * lam ^ m₀ := mul_pos hρ (pow_pos hlam_pos m₀)
  let g := H.reflect N
  have hg_deg : g.natDegree = N := (roots_reflect_eq hdeg h0).1
  have hg_card : (g.roots.filter (fun w => (ρ * lam ^ m₀)⁻¹ ≤ ‖w‖)).card < m₀ := by
    rwa [roots_reflect_card_ge hdeg h0 hρlam_pos]
  have hgd := derivative_roots_bound hg_deg hm₀ hN (inv_pos.mpr hρlam_pos) hg_card
  have hcancel : (ρ * lam ^ m₀)⁻¹ * lam ^ m₀ = ρ⁻¹ := by
    rw [mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero m₀ hlam_pos.ne'), mul_one]
  rw [hcancel] at hgd
  have hgd_eq : g.derivative = (eulerOp N H).reflect (N - 1) :=
    derivative_reflect_eq_reflect_eulerOp hdeg (by omega)
  rw [hgd_eq] at hgd
  have heul_deg : (eulerOp N H).natDegree ≤ N - 1 := natDegree_eulerOp_le hdeg (by omega)
  have heul_0 : (eulerOp N H).eval 0 ≠ 0 := by
    rw [eval_zero_eulerOp]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) h0
  rwa [roots_reflect_card_ge heul_deg heul_0 hρ] at hgd

/- ### Part 6: Inductive lacunary root bound and product bounds -/

private theorem lacunary_roots_bound (m₀ s d₀ : ℕ) (N : ℕ → ℕ)
    (hm₀ : 1 ≤ m₀) (hm₀d₀ : m₀ ≤ d₀) (hd₀ : d₀ < N (s + 1)) (h2m₀ : 2 * m₀ ≤ N (s + 1))
    (hN_mono : ∀ i j, s + 1 ≤ i → i < j → N i < N j) :
    ∀ K, s + 1 ≤ K →
      ∀ (P₀ : ℂ[X]) (a : ℕ → ℂ) (R : ℝ),
        P₀.eval 0 ≠ 0 →
        P₀.natDegree = d₀ →
        0 < R →
        (∀ z ∈ P₀.roots, ‖z‖ ≤ R) →
        m₀ ≤ ((P₀ + ∑ j ∈ Ico (s + 1) K, monomial (N j) (a j)).roots.filter
          (fun z => ‖z‖ ≤
            R * (∏ j ∈ Ico (s + 1) K, ((N j : ℝ) / ((N j : ℝ) - (d₀ : ℝ)))) *
                (∏ j ∈ Ico (s + 1) K,
                  (1 + (5 * (m₀ : ℝ)) / ((N j : ℝ) - 2 * (m₀ : ℝ) + 2)) ^ m₀))).card := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base =>
    intro P₀ a R hP0 hdeg hR hroots
    have hsum : P₀ + ∑ j ∈ Ico (s + 1) (s + 1), monomial (N j) (a j) = P₀ := by simp
    have hrad : R * (∏ j ∈ Ico (s + 1) (s + 1), ((N j : ℝ) / ((N j : ℝ) - (d₀ : ℝ)))) *
        (∏ j ∈ Ico (s + 1) (s + 1),
          (1 + (5 * (m₀ : ℝ)) / ((N j : ℝ) - 2 * (m₀ : ℝ) + 2)) ^ m₀) = R := by simp
    rw [hsum]
    have hall : P₀.roots.filter (fun z => ‖z‖ ≤
        R * (∏ j ∈ Ico (s + 1) (s + 1), ((N j : ℝ) / ((N j : ℝ) - (d₀ : ℝ)))) *
            (∏ j ∈ Ico (s + 1) (s + 1),
              (1 + (5 * (m₀ : ℝ)) / ((N j : ℝ) - 2 * (m₀ : ℝ) + 2)) ^ m₀)) = P₀.roots := by
      refine Multiset.filter_eq_self.mpr fun z hz => ?_
      rw [hrad]
      exact hroots z hz
    rw [hall, ← (IsAlgClosed.splits P₀).natDegree_eq_card_roots, hdeg]
    exact hm₀d₀
  | succ K hK ih =>
    intro P₀ a R hP0 hdeg hR hroots
    have hNK_ge : N (s + 1) ≤ N K := by
      rcases eq_or_lt_of_le hK with rfl | hlt
      · exact le_rfl
      · exact (hN_mono (s + 1) K le_rfl hlt).le
    have hP0_ne : P₀ ≠ 0 := fun h => hP0 (by simp [h])
    have hd₀_lt_NK : d₀ < N K := lt_of_lt_of_le hd₀ hNK_ge
    have h2m₀_NK : 2 * m₀ ≤ N K := le_trans h2m₀ hNK_ge
    let P₁ := eulerOp (N K) P₀
    let a₁ : ℕ → ℂ := fun j => ((N K : ℂ) - (N j : ℂ)) * a j
    let R₁ : ℝ := R * ((N K : ℝ) / ((N K : ℝ) - (d₀ : ℝ)))
    have hfwd := eulerOp_forward_step (N := N K) hP0_ne (hdeg.symm ▸ hd₀_lt_NK) hR.le hroots
    have hP1_0 : P₁.eval 0 ≠ 0 := by
      dsimp [P₁]
      rw [eval_zero_eulerOp]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hP0
    have hP1_deg : P₁.natDegree = d₀ := hfwd.2.1.trans hdeg
    have hR1_pos : 0 < R₁ := by
      dsimp [R₁]
      have hsub : 0 < (N K : ℝ) - (d₀ : ℝ) := by
        have : (d₀ : ℝ) < (N K : ℝ) := by exact_mod_cast hd₀_lt_NK
        linarith
      have hNKpos : (0 : ℝ) < (N K : ℝ) := by exact_mod_cast (by omega : 0 < N K)
      positivity
    have hP1_roots : ∀ z ∈ P₁.roots, ‖z‖ ≤ R₁ := by
      simpa [P₁, R₁, hdeg] using hfwd.2.2
    have hIH := ih P₁ a₁ R₁ hP1_0 hP1_deg hR1_pos hP1_roots
    let H := P₀ + ∑ j ∈ Ico (s + 1) (K + 1), monomial (N j) (a j)
    have heul_H : eulerOp (N K) H = P₁ + ∑ j ∈ Ico (s + 1) K, monomial (N j) (a₁ j) := by
      dsimp [H, P₁, a₁]
      rw [Finset.sum_Ico_succ_top hK, eulerOp_add, eulerOp_add, eulerOp_monomial_self, add_zero,
        eulerOp_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [eulerOp_monomial]
    let ρ : ℝ := R₁ * (∏ j ∈ Ico (s + 1) K, ((N j : ℝ) / ((N j : ℝ) - (d₀ : ℝ)))) *
        (∏ j ∈ Ico (s + 1) K, (1 + (5 * (m₀ : ℝ)) / ((N j : ℝ) - 2 * (m₀ : ℝ) + 2)) ^ m₀)
    have hρ_pos : 0 < ρ := by
      dsimp [ρ]
      refine mul_pos (mul_pos hR1_pos ?_) ?_
      · refine Finset.prod_pos fun j hj => ?_
        have hj1 : s + 1 ≤ j := (Finset.mem_Ico.mp hj).1
        have hNj_ge : N (s + 1) ≤ N j := by
          rcases eq_or_lt_of_le hj1 with rfl | hlt
          · exact le_rfl
          · exact (hN_mono (s + 1) j le_rfl hlt).le
        have hlt : (d₀ : ℝ) < (N j : ℝ) := by exact_mod_cast (lt_of_lt_of_le hd₀ hNj_ge)
        have hpos : (0 : ℝ) < (N j : ℝ) := by exact_mod_cast (by omega : 0 < N j)
        exact div_pos hpos (by linarith)
      · refine Finset.prod_pos fun j hj => ?_
        have hj1 : s + 1 ≤ j := (Finset.mem_Ico.mp hj).1
        have hNj_ge : N (s + 1) ≤ N j := by
          rcases eq_or_lt_of_le hj1 with rfl | hlt
          · exact le_rfl
          · exact (hN_mono (s + 1) j le_rfl hlt).le
        have hden : 0 < (N j : ℝ) - 2 * (m₀ : ℝ) + 2 := by
          have : 2 * (m₀ : ℝ) ≤ (N j : ℝ) := by exact_mod_cast (le_trans h2m₀ hNj_ge)
          linarith
        have hnum : (0 : ℝ) ≤ 5 * (m₀ : ℝ) := by positivity
        exact pow_pos (by linarith [div_nonneg hnum hden.le]) m₀
    have hH_deg : H.natDegree ≤ N K := by
      dsimp [H]
      refine (natDegree_add_le _ _).trans (max_le (by omega) ?_)
      refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
      have hj1 : s + 1 ≤ j := (Finset.mem_Ico.mp hj).1
      have hj2 : j ≤ K := by have := (Finset.mem_Ico.mp hj).2; omega
      have hNj_le : N j ≤ N K := by
        rcases eq_or_lt_of_le hj2 with rfl | hlt
        · exact le_rfl
        · exact (hN_mono j K hj1 hlt).le
      exact (natDegree_monomial_le _).trans hNj_le
    have hH_0 : H.eval 0 ≠ 0 := by
      have hsum0 : (∑ j ∈ Ico (s + 1) (K + 1), monomial (N j) (a j)).eval 0 = 0 := by
        rw [eval_finsetSum]
        refine Finset.sum_eq_zero fun j hj => ?_
        have hj1 : s + 1 ≤ j := (Finset.mem_Ico.mp hj).1
        have hNj_ge : N (s + 1) ≤ N j := by
          rcases eq_or_lt_of_le hj1 with rfl | hlt
          · exact le_rfl
          · exact (hN_mono (s + 1) j le_rfl hlt).le
        rw [eval_monomial, zero_pow (by omega), mul_zero]
      dsimp [H]
      rw [eval_add, hsum0, add_zero]
      exact hP0
    have hρ_next : ρ * (1 + (5 * (m₀ : ℝ)) / ((N K : ℝ) - 2 * (m₀ : ℝ) + 2)) ^ m₀ =
        R * (∏ j ∈ Ico (s + 1) (K + 1), ((N j : ℝ) / ((N j : ℝ) - (d₀ : ℝ)))) *
            (∏ j ∈ Ico (s + 1) (K + 1),
              (1 + (5 * (m₀ : ℝ)) / ((N j : ℝ) - 2 * (m₀ : ℝ) + 2)) ^ m₀) := by
      dsimp [ρ, R₁]
      rw [Finset.prod_Ico_succ_top hK, Finset.prod_Ico_succ_top hK]
      ring
    by_contra! hlt
    rw [← hρ_next] at hlt
    have hback := eulerOp_backward_step hm₀ h2m₀_NK hH_deg hH_0 hρ_pos hlt
    rw [heul_H] at hback
    exact (not_le_of_gt hback) hIH

private theorem forward_product_bound {n : ℕ → ℕ} (gaps : HasFejerGaps n) (p : ℕ) (S : Finset ℕ)
    (tail : ∀ j ∈ S, p < n j) :
    ∏ j ∈ S, ((n j : ℝ) / ((n j : ℝ) - p)) ≤
      Real.exp (((p : ℝ) * ((p : ℝ) + 1)) * (∑' j, (n j : ℝ)⁻¹)) := by
  have cmp (j : ℕ) (hj : j ∈ S) : ((n j : ℝ) / ((n j : ℝ) - p)) ≤
      Real.exp (((p : ℝ) * ((p : ℝ) + 1)) * (n j : ℝ)⁻¹) := by
    have high : (p : ℝ) + 1 ≤ n j := by exact_mod_cast tail j hj
    have dp : 0 < (n j : ℝ) - p := by linarith
    have np : (0 : ℝ) < n j := by linarith [Nat.cast_nonneg (α := ℝ) p]
    have less : (p : ℝ) / ((n j : ℝ) - p) ≤ ((p : ℝ) * ((p : ℝ) + 1)) * (n j : ℝ)⁻¹ := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ dp np]
      have hh : (n j : ℝ) ≤ ((p : ℝ) + 1) * ((n j : ℝ) - p) := by
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) p) (sub_nonneg.mpr high)]
      nlinarith [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α := ℝ) p)]
    have eqn : (n j : ℝ) / ((n j : ℝ) - p) = (p : ℝ) / ((n j : ℝ) - p) + 1 := by field_simp; ring
    linarith [eqn, Real.add_one_le_exp (((p : ℝ) * ((p : ℝ) + 1)) * (n j : ℝ)⁻¹)]
  calc
    _ ≤ ∏ j ∈ S, Real.exp (((p : ℝ) * ((p : ℝ) + 1)) * (n j : ℝ)⁻¹) := by
      apply Finset.prod_le_prod _ cmp
      intro i hi
      exact div_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast (tail i hi).le))
    _ = Real.exp (((p : ℝ) * ((p : ℝ) + 1)) * ∑ j ∈ S, (n j : ℝ)⁻¹) := by
      rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left
        (gaps.2.sum_le_tsum _ fun j _ => by positivity) (by positivity)

private theorem backward_product_bound {n : ℕ → ℕ} (gaps : HasFejerGaps n)
    (m₀ k₀ : ℕ) (S : Finset ℕ) (hk₀ : k₀ < m₀)
    (tail : ∀ j ∈ S, 6 * m₀ + 1 < n j) :
    ∏ j ∈ S, (1 + (5 * (m₀ : ℝ)) / (((n j - k₀ : ℕ) : ℝ) - 2 * (m₀ : ℝ) + 2)) ^ m₀ ≤
      Real.exp ((10 * (m₀ : ℝ) ^ 2) * (∑' j, (n j : ℝ)⁻¹)) := by
  have cmp (j : ℕ) (hj : j ∈ S) :
      (1 + (5 * (m₀ : ℝ)) / (((n j - k₀ : ℕ) : ℝ) - 2 * (m₀ : ℝ) + 2)) ^ m₀ ≤
        Real.exp ((10 * (m₀ : ℝ) ^ 2) * (n j : ℝ)⁻¹) := by
    have hnj : 6 * m₀ + 1 < n j := tail j hj
    have hnjR : 6 * (m₀ : ℝ) + 1 < (n j : ℝ) := by exact_mod_cast hnj
    have hk₀R : (k₀ : ℝ) < (m₀ : ℝ) := by exact_mod_cast hk₀
    have hsub_cast : ((n j - k₀ : ℕ) : ℝ) = (n j : ℝ) - (k₀ : ℝ) := Nat.cast_sub (by omega)
    rw [hsub_cast]
    have hden_ge : (n j : ℝ) / 2 ≤ (n j : ℝ) - (k₀ : ℝ) - 2 * (m₀ : ℝ) + 2 := by linarith
    have hnj_pos : (0 : ℝ) < (n j : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) m₀]
    have hfrac : (5 * (m₀ : ℝ)) / ((n j : ℝ) - (k₀ : ℝ) - 2 * (m₀ : ℝ) + 2) ≤
        (10 * (m₀ : ℝ)) * (n j : ℝ)⁻¹ := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ (by linarith) hnj_pos]
      nlinarith
    have hbase : 1 + (5 * (m₀ : ℝ)) / ((n j : ℝ) - (k₀ : ℝ) - 2 * (m₀ : ℝ) + 2) ≤
        Real.exp ((10 * (m₀ : ℝ)) * (n j : ℝ)⁻¹) := by
      have h1 := Real.add_one_le_exp ((10 * (m₀ : ℝ)) * (n j : ℝ)⁻¹)
      linarith
    have hbase_nonneg : 0 ≤ 1 + (5 * (m₀ : ℝ)) / ((n j : ℝ) - (k₀ : ℝ) - 2 * (m₀ : ℝ) + 2) := by
      have : 0 ≤ (5 * (m₀ : ℝ)) / ((n j : ℝ) - (k₀ : ℝ) - 2 * (m₀ : ℝ) + 2) :=
        div_nonneg (by positivity) (by linarith)
      linarith
    calc
      (1 + (5 * (m₀ : ℝ)) / ((n j : ℝ) - (k₀ : ℝ) - 2 * (m₀ : ℝ) + 2)) ^ m₀ ≤
          (Real.exp ((10 * (m₀ : ℝ)) * (n j : ℝ)⁻¹)) ^ m₀ :=
        pow_le_pow_left₀ hbase_nonneg hbase m₀
      _ = Real.exp ((m₀ : ℝ) * ((10 * (m₀ : ℝ)) * (n j : ℝ)⁻¹)) := by
        rw [← Real.exp_nat_mul]
      _ = Real.exp ((10 * (m₀ : ℝ) ^ 2) * (n j : ℝ)⁻¹) := by ring_nf
  calc
    _ ≤ ∏ j ∈ S, Real.exp ((10 * (m₀ : ℝ) ^ 2) * (n j : ℝ)⁻¹) := by
      refine Finset.prod_le_prod (fun j hj => ?_) cmp
      have hnj : 6 * m₀ + 1 < n j := tail j hj
      have hsub_cast : ((n j - k₀ : ℕ) : ℝ) = (n j : ℝ) - (k₀ : ℝ) := Nat.cast_sub (by omega)
      rw [hsub_cast]
      have hnjR : 6 * (m₀ : ℝ) + 1 < (n j : ℝ) := by exact_mod_cast hnj
      have hk₀R : (k₀ : ℝ) < (m₀ : ℝ) := by exact_mod_cast hk₀
      have : 0 ≤ (5 * (m₀ : ℝ)) / ((n j : ℝ) - (k₀ : ℝ) - 2 * (m₀ : ℝ) + 2) :=
        div_nonneg (by positivity) (by linarith)
      exact pow_nonneg (by linarith) m₀
    _ = Real.exp ((10 * (m₀ : ℝ) ^ 2) * ∑ j ∈ S, (n j : ℝ)⁻¹) := by
      rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left
        (gaps.2.sum_le_tsum _ fun j _ => by positivity) (by positivity)

private theorem section_degree {n : ℕ → ℕ} (h : StrictMono n) (a : ℕ → ℂ) (v : ℂ) (s : ℕ)
    (hp : 0 < n s) (ha : a s ≠ 0) :
    ((∑ j ∈ Finset.range (s + 1), monomial (n j) (a j)) - C v).natDegree = n s := by
  have up : ((∑ j ∈ Finset.range (s + 1), monomial (n j) (a j)) - C v).natDegree ≤ n s := by
    apply (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
    apply natDegree_sum_le_of_forall_le
    intro j hj
    exact (natDegree_monomial_le _).trans (h.monotone (by have := mem_range.mp hj; omega))
  apply le_antisymm up
  apply le_natDegree_of_ne_zero
  have eqn : ((∑ j ∈ Finset.range (s + 1), monomial (n j) (a j)) - C v).coeff (n s) = a s := by
    rw [coeff_sub, finsetSum_coeff, coeff_C_of_ne_zero hp.ne', sub_zero, Finset.sum_eq_single s]
    · simp
    · intro b _ ne; exact coeff_monomial_of_ne _ (fun e => ne (h.injective e.symm))
    · simp
  rwa [eqn]

private theorem finite_section_bound {n : ℕ → ℕ} (gaps : HasFejerGaps n) (a : ℕ → ℂ)
    (ha : ∀ k, a k ≠ 0) (v : ℂ) (m : ℕ) :
    ∃ R : ℝ, ∀ᶠ K : ℕ in atTop,
      m ≤ (((∑ j ∈ Finset.range K, monomial (n j) (a j)) - C v).roots.filter
        (fun z => ‖z‖ ≤ R)).card := by
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · exact ⟨0, Eventually.of_forall fun _ => Nat.zero_le _⟩
  let m₀ : ℕ := m
  have hm₀ : 1 ≤ m₀ := hmpos
  let s : ℕ := 6 * m₀ + 1
  have hns_ge : 6 * m₀ + 1 ≤ n s := gaps.1.id_le s
  have hns_pos : 0 < n s := by omega
  set P : ℂ[X] := (∑ j ∈ Finset.range (s + 1), monomial (n j) (a j)) - C v
  have hPdeg : P.natDegree = n s := section_degree gaps.1 a v s hns_pos (ha s)
  have hPne : P ≠ 0 := by intro h; simp [h] at hPdeg; omega
  set k₀ : ℕ := P.rootMultiplicity 0
  have hFk_comb : ∀ K, s < K →
      (∑ j ∈ Finset.range K, monomial (n j) (a j)) - C v =
        P + ∑ j ∈ Ico (s + 1) K, monomial (n j) (a j) := by
    intro K hK
    dsimp [P]
    rw [← Finset.sum_range_add_sum_Ico (fun j => monomial (n j) (a j)) hK]
    abel
  have hFk_ne : ∀ K, s < K → (∑ j ∈ Finset.range K, monomial (n j) (a j)) - C v ≠ 0 := by
    intro K hK heq
    have hc := congrArg (fun p : ℂ[X] => p.coeff (n s)) heq
    rw [coeff_sub, finsetSum_coeff, coeff_C_of_ne_zero hns_pos.ne', sub_zero, coeff_zero,
      Finset.sum_eq_single s] at hc
    · simp only [coeff_monomial, ↓reduceIte] at hc
      exact ha s hc
    · intro b _ hne
      exact coeff_monomial_of_ne _ fun e => hne (gaps.1.injective e.symm)
    · intro hnot; exact (hnot (Finset.mem_range.mpr hK)).elim
  have hXdvdP : X ^ k₀ ∣ P := by
    have h1 := (le_rootMultiplicity_iff hPne (a := (0 : ℂ)) (n := k₀)).mp le_rfl
    simpa using h1
  have hk₀_le_deg : k₀ ≤ n s := by
    have hcnt : k₀ ≤ P.roots.card := by
      have : k₀ = P.roots.count 0 := by rw [count_roots]
      rw [this]
      exact Multiset.count_le_card 0 P.roots
    rw [← (IsAlgClosed.splits P).natDegree_eq_card_roots, hPdeg] at hcnt
    exact hcnt
  by_cases hk₀ : m₀ ≤ k₀
  · refine ⟨1, ?_⟩
    filter_upwards [eventually_gt_atTop s] with K hK
    have hXdvdS : X ^ k₀ ∣ ∑ j ∈ Ico (s + 1) K, monomial (n j) (a j) := by
      refine Finset.dvd_sum fun j hj => ?_
      have hj1 : s < j := by have := (Finset.mem_Ico.mp hj).1; omega
      have hkle : k₀ ≤ n j := le_trans hk₀_le_deg (gaps.1 hj1).le
      refine ⟨monomial (n j - k₀) (a j), ?_⟩
      rw [X_pow_mul_monomial, Nat.sub_add_cancel hkle]
    have hXdvdF : X ^ k₀ ∣ (∑ j ∈ Finset.range K, monomial (n j) (a j)) - C v := by
      rw [hFk_comb K hK]
      exact dvd_add hXdvdP hXdvdS
    have hmult : k₀ ≤ ((∑ j ∈ Finset.range K, monomial (n j) (a j)) - C v).rootMultiplicity 0 := by
      refine (le_rootMultiplicity_iff (hFk_ne K hK)).mpr ?_
      simpa using hXdvdF
    have hcnt : k₀ ≤ (((∑ j ∈ Finset.range K, monomial (n j) (a j)) - C v).roots.filter
        (fun z => ‖z‖ ≤ (1 : ℝ))).card := by
      calc
        k₀ ≤ ((∑ j ∈ Finset.range K, monomial (n j) (a j)) - C v).roots.count 0 := by
          rwa [count_roots]
        _ = (((∑ j ∈ Finset.range K, monomial (n j) (a j)) - C v).roots.filter (fun z => 0 = z)).card := by
          rw [Multiset.count_eq_card_filter_eq]
        _ ≤ _ := Multiset.card_le_card (Multiset.monotone_filter_right _ fun z hz => by
          rw [← hz]; norm_num)
    exact hk₀.trans hcnt
  · push Not at hk₀
    obtain ⟨P₀, hP₀_eq⟩ := hXdvdP
    have hP₀_ne : P₀ ≠ 0 := by intro h; rw [h, mul_zero] at hP₀_eq; exact hPne hP₀_eq
    have hP₀_0 : P₀.eval 0 ≠ 0 := by
      intro h0
      have hXdvd : X ∣ P₀ := by
        simpa using dvd_iff_isRoot.mpr h0
      obtain ⟨Q, rfl⟩ := hXdvd
      have hpow : (X - C (0 : ℂ)) ^ (k₀ + 1) ∣ P := by
        refine ⟨Q, ?_⟩
        rw [hP₀_eq]; simp [pow_succ]; ring
      have hle := (le_rootMultiplicity_iff hPne (a := (0 : ℂ)) (n := k₀ + 1)).mpr hpow
      omega
    have hP₀_deg : P₀.natDegree = n s - k₀ := by
      have h1 : P.natDegree = k₀ + P₀.natDegree := by
        rw [hP₀_eq, natDegree_mul (pow_ne_zero k₀ X_ne_zero) hP₀_ne, natDegree_X_pow]
      omega
    let d₀ : ℕ := n s - k₀
    let N : ℕ → ℕ := fun j => n j - k₀
    have hns_lt_succ : n s < n (s + 1) := gaps.1 (by omega)
    have hN_mono : ∀ i j, s + 1 ≤ i → i < j → N i < N j := by
      intro i j hi hij
      have hni : n s < n i := gaps.1 (by omega)
      have hnij : n i < n j := gaps.1 hij
      dsimp [N]
      omega
    have hm₀d₀ : m₀ ≤ d₀ := by dsimp [d₀]; omega
    have hd₀_lt : d₀ < N (s + 1) := by dsimp [d₀, N]; omega
    have h2m₀_le : 2 * m₀ ≤ N (s + 1) := by dsimp [N]; omega
    let R₀ : ℝ := (∑ z ∈ P₀.roots.toFinset, ‖z‖) + 1
    have hR₀_pos : 0 < R₀ := by
      have : 0 ≤ ∑ z ∈ P₀.roots.toFinset, ‖z‖ := Finset.sum_nonneg fun z _ => norm_nonneg z
      dsimp [R₀]; linarith
    have hP₀_roots : ∀ z ∈ P₀.roots, ‖z‖ ≤ R₀ := by
      intro z hz
      have hle := Finset.single_le_sum (f := fun x : ℂ => ‖x‖)
        (fun _ _ => norm_nonneg _) (Multiset.mem_toFinset.mpr hz)
      dsimp [R₀]; linarith
    let Bfwd : ℝ := Real.exp (((n s : ℝ) * ((n s : ℝ) + 1)) * (∑' j, (n j : ℝ)⁻¹))
    let Bbwd : ℝ := Real.exp ((10 * (m₀ : ℝ) ^ 2) * (∑' j, (n j : ℝ)⁻¹))
    refine ⟨R₀ * Bfwd * Bbwd, ?_⟩
    filter_upwards [eventually_gt_atTop s] with K hK
    set G_K : ℂ[X] := P₀ + ∑ j ∈ Ico (s + 1) K, monomial (N j) (a j)
    have hFk_fac : (∑ j ∈ Finset.range K, monomial (n j) (a j)) - C v = X ^ k₀ * G_K := by
      rw [hFk_comb K hK, hP₀_eq]
      change X ^ k₀ * P₀ + ∑ j ∈ Ico (s + 1) K, monomial (n j) (a j) =
        X ^ k₀ * (P₀ + ∑ j ∈ Ico (s + 1) K, monomial (N j) (a j))
      rw [mul_add, Finset.mul_sum]
      refine congrArg (X ^ k₀ * P₀ + ·) ?_
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj1 : s < j := by have := (Finset.mem_Ico.mp hj).1; omega
      have hnj : n s < n j := gaps.1 hj1
      dsimp [N]
      rw [X_pow_mul_monomial, Nat.sub_add_cancel (by omega)]
    have hGK_ne : G_K ≠ 0 := by
      intro h; rw [h, mul_zero] at hFk_fac; exact hFk_ne K hK hFk_fac
    have hbound := lacunary_roots_bound m₀ s d₀ N hm₀ hm₀d₀ hd₀_lt h2m₀_le hN_mono K hK
      P₀ a R₀ hP₀_0 hP₀_deg hR₀_pos hP₀_roots
    have hpfwd : ∏ j ∈ Ico (s + 1) K, ((N j : ℝ) / ((N j : ℝ) - (d₀ : ℝ))) ≤ Bfwd := by
      calc
        ∏ j ∈ Ico (s + 1) K, ((N j : ℝ) / ((N j : ℝ) - (d₀ : ℝ))) ≤
            ∏ j ∈ Ico (s + 1) K, ((n j : ℝ) / ((n j : ℝ) - (n s : ℝ))) := by
          refine Finset.prod_le_prod (fun j hj => ?_) (fun j hj => ?_)
          · have hnj : n s < n j := gaps.1 (by have := (Finset.mem_Ico.mp hj).1; omega)
            have hsub : (d₀ : ℝ) < (N j : ℝ) := by exact_mod_cast (show d₀ < N j by dsimp [d₀, N]; omega)
            exact div_nonneg (Nat.cast_nonneg _) (by linarith)
          · have hnj : n s < n j := gaps.1 (by have := (Finset.mem_Ico.mp hj).1; omega)
            have hNjR : (N j : ℝ) = (n j : ℝ) - (k₀ : ℝ) := Nat.cast_sub (by omega)
            have hd₀R : (d₀ : ℝ) = (n s : ℝ) - (k₀ : ℝ) := Nat.cast_sub (by omega)
            rw [hNjR, hd₀R, sub_sub_sub_cancel_right]
            have hden : 0 < (n j : ℝ) - (n s : ℝ) := by
              have : (n s : ℝ) < (n j : ℝ) := by exact_mod_cast hnj
              linarith
            exact div_le_div_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) k₀]) hden.le
        _ ≤ Bfwd := forward_product_bound gaps (n s) (Ico (s + 1) K) fun j hj =>
          gaps.1 (by have := (Finset.mem_Ico.mp hj).1; omega)
    have hpbwd : ∏ j ∈ Ico (s + 1) K,
        (1 + (5 * (m₀ : ℝ)) / ((N j : ℝ) - 2 * (m₀ : ℝ) + 2)) ^ m₀ ≤ Bbwd :=
      backward_product_bound gaps m₀ k₀ (Ico (s + 1) K) hk₀ fun j hj =>
        lt_of_le_of_lt hns_ge (gaps.1 (by have := (Finset.mem_Ico.mp hj).1; omega))
    have hpbwd_nonneg : 0 ≤ ∏ j ∈ Ico (s + 1) K,
        (1 + (5 * (m₀ : ℝ)) / ((N j : ℝ) - 2 * (m₀ : ℝ) + 2)) ^ m₀ := by
      refine Finset.prod_nonneg fun j hj => ?_
      have hnj : 6 * m₀ + 1 < n j :=
        lt_of_le_of_lt hns_ge (gaps.1 (by have := (Finset.mem_Ico.mp hj).1; omega))
      have hNjR : (N j : ℝ) = (n j : ℝ) - (k₀ : ℝ) := Nat.cast_sub (by omega)
      rw [hNjR]
      have hnjR : 6 * (m₀ : ℝ) + 1 < (n j : ℝ) := by exact_mod_cast hnj
      have hk₀R : (k₀ : ℝ) < (m₀ : ℝ) := by exact_mod_cast hk₀
      have : 0 ≤ (5 * (m₀ : ℝ)) / ((n j : ℝ) - (k₀ : ℝ) - 2 * (m₀ : ℝ) + 2) :=
        div_nonneg (by positivity) (by linarith)
      exact pow_nonneg (by linarith) m₀
    have hR_le : R₀ * (∏ j ∈ Ico (s + 1) K, ((N j : ℝ) / ((N j : ℝ) - (d₀ : ℝ)))) *
        (∏ j ∈ Ico (s + 1) K, (1 + (5 * (m₀ : ℝ)) / ((N j : ℝ) - 2 * (m₀ : ℝ) + 2)) ^ m₀) ≤
        R₀ * Bfwd * Bbwd := by
      have h1 : R₀ * (∏ j ∈ Ico (s + 1) K, ((N j : ℝ) / ((N j : ℝ) - (d₀ : ℝ)))) ≤ R₀ * Bfwd :=
        mul_le_mul_of_nonneg_left hpfwd hR₀_pos.le
      have h2 : 0 ≤ R₀ * Bfwd := mul_nonneg hR₀_pos.le (Real.exp_pos _).le
      exact (mul_le_mul_of_nonneg_right h1 hpbwd_nonneg).trans (mul_le_mul_of_nonneg_left hpbwd h2)
    have hGK_card : m₀ ≤ (G_K.roots.filter (fun z => ‖z‖ ≤ R₀ * Bfwd * Bbwd)).card :=
      hbound.trans (Multiset.card_le_card (Multiset.monotone_filter_right _ fun z hz => hz.trans hR_le))
    have hroots_le : G_K.roots ≤ ((∑ j ∈ Finset.range K, monomial (n j) (a j)) - C v).roots := by
      rw [hFk_fac, roots_mul (mul_ne_zero (pow_ne_zero k₀ X_ne_zero) hGK_ne)]
      exact Multiset.le_add_left _ _
    exact hGK_card.trans (Multiset.card_le_card (Multiset.filter_le_filter _ hroots_le))

end OMA.Fejer517A

open OMA.Fejer517A

theorem OMA.solution : type_of% @Erdos517.erdos_517.variants.fejer := by
  intro f n gaps a ha hf v
  obtain ⟨uniform, analytic⟩ := section_convergence n a f v hf
  have hinf := zero_transfer
    (fun K : ℕ => (∑ j ∈ Finset.range K, monomial (n j) (a j)) - C v)
    (fun z => f z - v) analytic uniform (finite_section_bound gaps a ha v)
  simpa only [sub_eq_zero] using hinf
