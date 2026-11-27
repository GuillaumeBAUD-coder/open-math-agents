import FormalConjectures.ErdosProblems.«1044»
import Mathlib

/-!
# The least possible maximum boundary length in degrees one and two

Quanyu Tang proved the mathematical result in *On Erdős Problem 1044*.
This formalization uses rigid motions to center the roots, horizontal projection
to bound the nonsingular oval from below, and a rational half-angle substitution
to bound each of the two arcs of a singular lobe from above. Its squared speed
is 4 / (1 + u^4). The local arguments below only require standard Mathlib.

A separate formalization of the same result was previously posted in PR 3059.
-/


namespace CassiniModel

open Set

noncomputable def arc (u : ℝ) : ℂ :=
  let t := (1 - u ^ 2) / (1 + u ^ 2)
  ⟨t * Real.sqrt (1 + t ^ 2), t * (2 * u / (1 + u ^ 2))⟩

def region : Set ℂ := {z | ‖z ^ 2 - 1‖ < 1}

noncomputable def rightCover : Set ℂ :=
  arc '' Icc 0 1 ∪ (fun u => starRingEnd ℂ (arc u)) '' Icc 0 1

private theorem norm_square (z : ℂ) :
    ‖z ^ 2 - 1‖ ^ 2 = (z.re ^ 2 + z.im ^ 2) ^ 2 - 2 * (z.re ^ 2 - z.im ^ 2) + 1 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [pow_two, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
    Complex.mul_re, Complex.mul_im]
  ring

private theorem level_mem_rightCover {z : ℂ} (hz : ‖z ^ 2 - 1‖ = 1) (hx : 0 ≤ z.re) :
    z ∈ rightCover := by
  have heq := norm_square z
  rw [hz] at heq
  let t := Real.sqrt ((z.re ^ 2 + z.im ^ 2) / 2)
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have htsq : t ^ 2 = (z.re ^ 2 + z.im ^ 2) / 2 := Real.sq_sqrt (by positivity)
  have hsum : z.re ^ 2 + z.im ^ 2 = 2 * t ^ 2 := by linarith
  have hrel : 4 * t ^ 4 = 2 * (z.re ^ 2 - z.im ^ 2) := calc
    _ = (2 * t ^ 2) ^ 2 := by ring
    _ = _ := by rw [← hsum]; linarith only [heq]
  have hx2 : z.re ^ 2 = t ^ 2 * (1 + t ^ 2) := by nlinarith only [hsum, hrel]
  have hy2 : z.im ^ 2 = t ^ 2 * (1 - t ^ 2) := by nlinarith only [hsum, hrel]
  have ht1 : t ≤ 1 := by
    by_contra! h
    have hpow : 1 < t ^ 2 := by nlinarith [sq_nonneg (t - 1)]
    have hneg := mul_neg_of_pos_of_neg (pow_pos (by linarith : 0 < t) 2)
      (show 1 - t ^ 2 < 0 by linarith)
    linarith [sq_nonneg z.im]
  let u := Real.sqrt ((1 - t) / (1 + t))
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = (1 - t) / (1 + t) :=
    Real.sq_sqrt (div_nonneg (by linarith) (by positivity))
  have hu1 : u ≤ 1 := by
    have hsq : u ^ 2 ≤ 1 := by
      rw [hu2]
      apply (div_le_iff₀ (by positivity : 0 < 1 + t)).2
      linarith
    by_contra! h
    nlinarith [sq_nonneg (u - 1)]
  have hparam : (1 - u ^ 2) / (1 + u ^ 2) = t := by
    apply (div_eq_iff (by positivity : 1 + u ^ 2 ≠ 0)).2
    rw [hu2]
    field_simp <;> ring
  let s := 2 * u / (1 + u ^ 2)
  have hs : 0 ≤ s := by positivity
  have hs2 : s ^ 2 = 1 - t ^ 2 := by
    have hunit : ((1 - u ^ 2) / (1 + u ^ 2)) ^ 2 + s ^ 2 = 1 := by
      dsimp [s]
      field_simp <;> ring
    rw [hparam] at hunit
    linarith
  have hre : t * Real.sqrt (1 + t ^ 2) = z.re := by
    apply (sq_eq_sq₀ (by positivity) hx).mp
    have hsqrt : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
    rw [mul_pow, hsqrt]
    exact hx2.symm
  have him : t * s = |z.im| := by
    apply (sq_eq_sq₀ (mul_nonneg ht hs) (abs_nonneg _)).mp
    rw [mul_pow, hs2, sq_abs, hy2]
  have hArc : arc u = ⟨z.re, |z.im|⟩ := by
    change (⟨((1 - u ^ 2) / (1 + u ^ 2)) *
      Real.sqrt (1 + ((1 - u ^ 2) / (1 + u ^ 2)) ^ 2),
      ((1 - u ^ 2) / (1 + u ^ 2)) * s⟩ : ℂ) = _
    rw [hparam, hre, him]
  by_cases hi : 0 ≤ z.im
  · left
    refine ⟨u, ⟨hu, hu1⟩, ?_⟩
    rw [hArc, abs_of_nonneg hi]
  · right
    refine ⟨u, ⟨hu, hu1⟩, ?_⟩
    change starRingEnd ℂ (arc u) = z
    apply Complex.ext <;> simp [hArc, abs_of_neg (lt_of_not_ge hi)]

private theorem region_open : IsOpen region :=
  isOpen_lt (by fun_prop : Continuous (fun z : ℂ => ‖z ^ 2 - 1‖)) continuous_const

private theorem region_real_ne_zero {z : ℂ} (hz : z ∈ region) : z.re ≠ 0 := by
  intro h
  have heq := norm_square z
  rw [h] at heq
  change ‖z ^ 2 - 1‖ < 1 at hz
  have hs := pow_lt_pow_left₀ hz (norm_nonneg _) (by decide : 2 ≠ 0)
  have him : 0 ≤ z.im ^ 2 := sq_nonneg _
  simp only [zero_pow (by decide : 2 ≠ 0), zero_add, zero_sub, mul_neg, sub_neg_eq_add] at heq
  nlinarith [sq_nonneg (z.im ^ 2)]

private theorem frontier_level {z w : ℂ} (hz : z ∈ region)
    (hw : w ∈ frontier (connectedComponentIn region z)) : ‖w ^ 2 - 1‖ = 1 := by
  have hwcl := frontier_subset_closure hw
  let closedRegion : Set ℂ := {y | ‖y ^ 2 - 1‖ ≤ 1}
  have hclosed : IsClosed closedRegion :=
    isClosed_le (by fun_prop : Continuous (fun y : ℂ => ‖y ^ 2 - 1‖)) continuous_const
  have hsub : connectedComponentIn region z ⊆ closedRegion := by
    intro y hy
    have hmem := connectedComponentIn_subset region z hy
    exact (show ‖y ^ 2 - 1‖ < 1 from hmem).le
  have hu : ‖w ^ 2 - 1‖ ≤ 1 := closure_minimal hsub hclosed hwcl
  apply le_antisymm hu
  by_contra! h
  let w' : region := ⟨w, h⟩
  have hw' : w' ∈ closure (connectedComponent (⟨z, hz⟩ : region)) := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
      ← connectedComponentIn_eq_image hz]
    exact hwcl
  rw [isClosed_connectedComponent.closure_eq] at hw'
  have hwc : w ∈ connectedComponentIn region z := by
    rw [connectedComponentIn_eq_image hz]
    exact ⟨w', hw', rfl⟩
  apply hw.2
  rw [(region_open.connectedComponentIn).interior_eq]
  exact hwc

/-- Every component frontier lies in one lobe, with the left lobe obtained by negation. -/
theorem frontier_subset_lobe {z : ℂ} (hz : z ∈ region) :
    frontier (connectedComponentIn region z) ⊆ rightCover ∨
      frontier (connectedComponentIn region z) ⊆ (fun w : ℂ => -w) '' rightCover := by
  let C := connectedComponentIn region z
  have hC : C ⊆ {w : ℂ | 0 < w.re} ∪ {w : ℂ | w.re < 0} := by
    intro w hw
    rcases lt_or_gt_of_ne (region_real_ne_zero (connectedComponentIn_subset _ _ hw)) with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hp : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hn : IsOpen {w : ℂ | w.re < 0} := isOpen_lt Complex.continuous_re continuous_const
  have hd : Disjoint {w : ℂ | 0 < w.re} {w : ℂ | w.re < 0} :=
    Set.disjoint_left.mpr (fun w h₁ h₂ =>
      (not_lt_of_ge (show 0 < w.re from h₁).le) h₂)
  rcases isPreconnected_connectedComponentIn.subset_or_subset hp hn hd hC with hpos | hneg
  · left
    intro w hw
    have hsub : C ⊆ {y : ℂ | 0 ≤ y.re} := by
      intro y hy
      exact (show (0 : ℝ) < y.re from hpos hy).le
    have hnonneg : 0 ≤ w.re := closure_minimal hsub
      (isClosed_le continuous_const Complex.continuous_re) (frontier_subset_closure hw)
    exact level_mem_rightCover (frontier_level hz hw) hnonneg
  · right
    intro w hw
    have hsub : C ⊆ {y : ℂ | y.re ≤ 0} := by
      intro y hy
      exact (show y.re < (0 : ℝ) from hneg hy).le
    have hnonpos : w.re ≤ 0 := closure_minimal hsub
      (isClosed_le Complex.continuous_re continuous_const) (frontier_subset_closure hw)
    refine ⟨-w, level_mem_rightCover ?_ (by simpa using neg_nonneg.mpr hnonpos), neg_neg _⟩
    simpa only [neg_sq] using frontier_level hz hw

end CassiniModel

namespace CassiniModel

private noncomputable def t (u : ℝ) : ℝ := (1-u^2)/(1+u^2)
private noncomputable def s (u : ℝ) : ℝ := 2*u/(1+u^2)

private theorem t_deriv (u : ℝ) : HasDerivAt t (-2*s u/(1+u^2)) u := by
  have hd : 1+u^2 ≠ 0 := by positivity
  have h := ((hasDerivAt_const u (1:ℝ)).sub ((hasDerivAt_id u).pow 2)).div
    ((hasDerivAt_const u (1:ℝ)).add ((hasDerivAt_id u).pow 2)) hd
  apply h.congr_deriv
  dsimp [s]
  field_simp
  <;> ring

private theorem s_deriv (u : ℝ) : HasDerivAt s (2*t u/(1+u^2)) u := by
  have hd : 1+u^2 ≠ 0 := by positivity
  have h := ((hasDerivAt_id u).const_mul 2).div
    ((hasDerivAt_const u (1:ℝ)).add ((hasDerivAt_id u).pow 2)) hd
  apply h.congr_deriv
  dsimp [t]
  field_simp
  <;> ring

private noncomputable def dx (u : ℝ) := -2*s u/(1+u^2) * ((1+2*(t u)^2) / Real.sqrt (1+(t u)^2))
private noncomputable def dy (u : ℝ) := 2/(1+u^2) * ((t u)^2-(s u)^2)

private theorem arc_deriv (u : ℝ) : HasDerivAt arc (⟨dx u,dy u⟩ : ℂ) u := by
  have hr : 0 < Real.sqrt (1+(t u)^2) := Real.sqrt_pos.mpr (by positivity)
  have he := Real.sq_sqrt (show 0 ≤ 1+(t u)^2 by positivity)
  have e := (t_deriv u).mul (((hasDerivAt_const u (1:ℝ)).add ((t_deriv u).pow 2)).sqrt (by dsimp; positivity))
  have hx : HasDerivAt (fun z => t z * Real.sqrt (1+(t z)^2)) (dx u) u := by
    apply e.congr_deriv
    dsimp [dx]
    field_simp
    <;> ring_nf
    <;> rw [he]
    <;> ring
  have hy : HasDerivAt (fun z => t z*s z) (dy u) u := by
    apply ((t_deriv u).mul (s_deriv u)).congr_deriv
    dsimp [dy]
    ring
  have h := hx.ofReal_comp.add (hy.ofReal_comp.mul_const Complex.I)
  have hf : arc = (fun z => ((t z * Real.sqrt (1+(t z)^2):ℝ):ℂ)) +
      (fun z => ((t z*s z : ℝ):ℂ) * Complex.I) := by
    funext z
    exact (Complex.re_add_im (arc z)).symm
  rw [hf]
  exact h.congr_deriv (Complex.re_add_im (⟨dx u,dy u⟩:ℂ))

private theorem speed (u : ℝ) : ‖(⟨dx u,dy u⟩:ℂ)‖ ≤ 2 := by
  have hc : (s u)^2 = 1 - (t u)^2 := by
    dsimp [s,t]
    field_simp
    <;> ring
  have hr : 0 < Real.sqrt (1+(t u)^2) := Real.sqrt_pos.mpr (by positivity)
  have he := Real.sq_sqrt (show 0 ≤ 1+(t u)^2 by positivity)
  have hx : dx u * (1+u^2) * Real.sqrt (1+(t u)^2) = -2*s u*(1+2*(t u)^2) := by
    dsimp [dx]
    field_simp
  have hy : dy u * (1+u^2) = 2*((t u)^2-(s u)^2) := by
    dsimp [dy]
    field_simp
  have hid : ((dx u)^2 + (dy u)^2) * ((1+u^2)^2 * (1+(t u)^2)) = 8 := by
    calc
      _ = (dx u * (1+u^2) * Real.sqrt (1+(t u)^2))^2
          + (dy u*(1+u^2))^2 * (1+(t u)^2) := by
            ring_nf
            rw [he]
            ring
      _ = 4*((s u)^2*(1+2*(t u)^2)^2+((t u)^2-(s u)^2)^2*(1+(t u)^2)) := by
            rw [hx,hy]
            ring
      _ = 8 := by rw [hc]; ring
  have hden : (1+u^2)^2 * (1+(t u)^2) = 2*(1+u^4) := by
    dsimp [t]
    field_simp
    <;> ring
  rw [hden] at hid
  have hnorm := Complex.sq_norm (⟨dx u,dy u⟩:ℂ)
  rw [Complex.normSq_apply] at hnorm
  dsimp at hnorm
  nlinarith [sq_nonneg (dx u*u^2),sq_nonneg (dy u*u^2)]

theorem arc_lipschitz : LipschitzOnWith 2 arc (Set.Icc 0 1) := by
  apply (convex_Icc (0:ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun u _ => (arc_deriv u).hasDerivWithinAt)
  intro u _
  exact_mod_cast speed u

end CassiniModel

open Set Polynomial MeasureTheory

namespace OMA.CassiniLower

private theorem meets_frontier {U T : Set ℂ} (hU : IsOpen U) (hT : IsPreconnected T)
    {p q : ℂ} (hp : p ∈ T) (hpU : p ∈ U) (hq : q ∈ T) (hqU : q ∉ closure U) :
    ∃ z ∈ T, z ∈ frontier U := by
  by_contra! h
  have hcover : T ⊆ U ∪ (closure U)ᶜ := by
    intro z hz
    by_cases hc : z ∈ closure U
    · left
      by_contra hn
      exact h z hz (by simpa only [frontier, hU.interior_eq, mem_sdiff] using And.intro hc hn)
    · exact Or.inr hc
  have hd : Disjoint U (closure U)ᶜ := disjoint_compl_right.mono_left subset_closure
  rcases hT.subset_or_subset hU isClosed_closure.isOpen_compl hd hcover with hu | hc
  · exact hqU (subset_closure (hu hq))
  · exact hc hp (subset_closure hpU)

private theorem slice_meets {U : Set ℂ} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    (x d : ℝ) (hd : |d| = 1) (hx : (x : ℂ) ∈ U) :
    ∃ z ∈ frontier U, z.re = x ∧ 0 < d * z.im := by
  let v (t : ℝ) : ℂ := ⟨x, d * t⟩
  have hv : Continuous v := by simp only [v, Complex.mk_eq_add_mul_I]; fun_prop
  let T := v '' Ici 0
  have hT : IsPreconnected T := isPreconnected_Ici.image _ hv.continuousOn
  obtain ⟨M, hM, hB⟩ := hb.closure.exists_pos_norm_le
  have h0 : v 0 ∈ U := by simpa [v, Complex.ofReal] using hx
  have hlarge : v (M + 1) ∉ closure U := by
    intro h
    have hi := (Complex.abs_im_le_norm (v (M + 1))).trans (hB _ h)
    change |d * (M + 1)| ≤ M at hi
    rw [abs_mul, hd, one_mul, abs_of_pos (by linarith)] at hi
    linarith
  obtain ⟨z, ⟨t, ht, rfl⟩, hz⟩ := meets_frontier hU hT
    (mem_image_of_mem v (show (0 : ℝ) ∈ Ici 0 by simp)) h0
    (mem_image_of_mem v (show M + 1 ∈ Ici 0 by change 0 ≤ M + 1; linarith)) hlarge
  have htpos : 0 < t := by
    apply lt_of_le_of_ne ht
    rintro rfl
    exact (show v 0 ∉ U from by simpa [frontier, hU.interior_eq] using hz.2) h0
  have hd2 : d ^ 2 = 1 := by rw [← sq_abs, hd]; norm_num
  refine ⟨v t, hz, rfl, ?_⟩
  change 0 < d * (d * t)
  nlinarith only [htpos, congrArg (fun a : ℝ => a * t) hd2]

private theorem length_ge_four {U : Set ℂ} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    (hi : ∀ x ∈ Ioo (-1 : ℝ) 1, (x : ℂ) ∈ U) :
    4 ≤ Erdos1041.length (frontier U) := by
  let half (d : ℝ) := frontier U ∩ {z : ℂ | 0 < d * z.im}
  have hm (d : ℝ) : MeasurableSet (half d) := isClosed_frontier.measurableSet.inter
    (isOpen_lt continuous_const (continuous_const.mul Complex.continuous_im)).measurableSet
  have h2 (d : ℝ) (hd : |d| = 1) : 2 ≤ μH[1] (half d) := by
    have hs : Ioo (-1 : ℝ) 1 ⊆ Complex.re '' half d := by
      intro x hx
      obtain ⟨z, hz, hr, hsign⟩ := slice_meets hU hb x d hd (hi x hx)
      exact ⟨z, ⟨hz, hsign⟩, hr⟩
    have hlip : LipschitzWith 1 Complex.re := LipschitzWith.of_dist_le_mul <| by
      intro x y
      simpa [Real.dist_eq, Complex.dist_eq] using Complex.abs_re_le_norm (x - y)
    have h := (measure_mono (μ := μH[1]) hs).trans (hlip.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1) _)
    norm_num [MeasureTheory.hausdorffMeasure_real, Real.volume_Ioo] at h
    exact h
  have hd : Disjoint (half 1) (half (-1)) := by
    apply Set.disjoint_left.mpr
    intro z hp hn
    have hp' := hp.2
    have hn' := hn.2
    change 0 < 1 * z.im at hp'
    change 0 < -1 * z.im at hn'
    linarith
  calc (4 : ENNReal) = 2 + 2 := by norm_num
    _ ≤ μH[1] (half 1) + μH[1] (half (-1)) := add_le_add (h2 1 (by norm_num)) (h2 (-1) (by norm_num))
    _ = μH[1] (half 1 ∪ half (-1)) := (measure_union hd (hm _)).symm
    _ ≤ _ := measure_mono (union_subset inter_subset_left inter_subset_left)

/-- For `0 ≤ q < 1`, the component through zero has boundary length at least four. -/
theorem lower {q : ℝ} (hq : 0 ≤ q) (hq' : q < 1) :
    4 ≤ Erdos1044.maxBoundaryLength (X ^ 2 - C (q : ℂ)) := by
  let f : ℂ[X] := X ^ 2 - C (q : ℂ)
  let S := {z : ℂ | ‖f.eval z‖ < 1}
  let U := connectedComponentIn S 0
  have hs : IsOpen S := isOpen_lt f.continuous.norm continuous_const
  have hb : Bornology.IsBounded S := by
    apply (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset
    intro z hz
    change ‖f.eval z‖ < 1 at hz
    simp [f] at hz
    have h := norm_sub_norm_le (z ^ 2) (q : ℂ)
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq] at h
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg z]
  let I := Complex.ofReal '' Ioo (-1 : ℝ) 1
  have hI : IsPreconnected I := isPreconnected_Ioo.image _ Complex.continuous_ofReal.continuousOn
  have hI0 : (0 : ℂ) ∈ I := ⟨0, by norm_num, by simp⟩
  have hIS : I ⊆ S := by
    rintro z ⟨x, hx, rfl⟩
    change ‖f.eval (x : ℂ)‖ < 1
    simp only [f, eval_sub, eval_pow, eval_X, eval_C, ← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    apply abs_lt.mpr
    constructor
    · nlinarith [sq_nonneg x]
    · nlinarith [mul_pos (show 0 < 1-x by linarith [hx.2]) (show 0 < 1+x by linarith [hx.1])]
  have hIU : I ⊆ U := hI.subset_connectedComponentIn hI0 hIS
  have hlen := length_ge_four hs.connectedComponentIn (hb.subset (connectedComponentIn_subset S 0))
    (fun x hx => hIU ⟨x, hx, rfl⟩)
  exact hlen.trans (le_iSup_of_le 0 (le_iSup_of_le (hIS hI0) le_rfl))

end OMA.CassiniLower

open Set MeasureTheory Polynomial Erdos1044
open scoped MeasureTheory
namespace CassiniModel
theorem cover_bound (arc : ℝ → ℂ) (hlip : LipschitzOnWith 2 arc (Icc 0 1)) :
    μH[1] (arc '' Icc 0 1 ∪ (fun u => starRingEnd ℂ (arc u)) '' Icc 0 1) ≤ 4 := by
  have ha := hlip.hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 1)
  norm_num [hausdorffMeasure_real,Real.volume_Icc] at ha
  have hb : μH[1] ((fun u => starRingEnd ℂ (arc u)) '' Icc 0 1) =
      μH[1] (arc '' Icc 0 1) := by
    rw [show (fun u => starRingEnd ℂ (arc u)) '' Icc 0 1 =
      (starRingEnd ℂ) '' (arc '' Icc 0 1) from (Set.image_image ..).symm,
      Complex.isometry_conj.hausdorffMeasure_image (Or.inl (by norm_num))]
  calc
    _ ≤ _ := measure_union_le _ _
    _ = μH[1] (arc '' Icc 0 1) + μH[1] (arc '' Icc 0 1) := by rw [hb]
    _ ≤ 2+2 := add_le_add ha ha
    _ = 4 := by norm_num

theorem upper_of_cover (R : Set ℂ) (hm : μH[1] R ≤ 4)
    (h : ∀ z ∈ {w : ℂ | ‖(X^2-1 : ℂ[X]).eval w‖ < 1},
      let F := frontier (connectedComponentIn {w : ℂ | ‖(X^2-1 : ℂ[X]).eval w‖ < 1} z)
      F ⊆ R ∨ F ⊆ (fun w : ℂ => -w) '' R) :
    maxBoundaryLength (X^2-1) ≤ 4 := by
  apply iSup₂_le
  intro z hz
  rcases h z hz with pos | neg
  · exact (measure_mono pos).trans hm
  · have hi : Isometry (fun z : ℂ => -z) := isometry_neg
    exact (measure_mono neg).trans ((hi.hausdorffMeasure_image (Or.inl (by norm_num : (0:ℝ) ≤ 1)) R).le.trans hm)

end CassiniModel

open Polynomial Erdos1044
namespace OMA.CassiniTransfer

private noncomputable def motion (u c : ℂ) (hu : ‖u‖ = 1) : ℂ ≃ᵢ ℂ where
  toFun z := u * z + c
  invFun w := (w-c)/u
  left_inv z := by
    have h : u ≠ 0 := fun h => by simp [h] at hu
    field_simp
    <;> ring
  right_inv w := by
    have h : u ≠ 0 := fun h => by simp [h] at hu
    field_simp
    <;> ring
  isometry_toFun := Isometry.of_dist_eq fun a b => by
    simp only [dist_eq_norm, add_sub_add_right_eq_sub, ← mul_sub, norm_mul, hu, one_mul]

private theorem rigid (f g : ℂ[X]) (e : ℂ ≃ᵢ ℂ)
    (h : ∀ z, ‖g.eval (e z)‖ = ‖f.eval z‖) :
    maxBoundaryLength f = maxBoundaryLength g := by
  let S : Set ℂ := {z | ‖f.eval z‖ < 1}
  let T : Set ℂ := {z | ‖g.eval z‖ < 1}
  have hi : e '' S = T := by
    ext x
    obtain ⟨w, rfl⟩ := e.surjective x
    simp [S,T,h]
  have boundary (z : ℂ) (hz : z ∈ S) :
      Erdos1041.length (frontier (connectedComponentIn S z)) =
        Erdos1041.length (frontier (connectedComponentIn T (e z))) := by
    have c := e.toHomeomorph.image_connectedComponentIn hz
    change e '' connectedComponentIn S z = connectedComponentIn (e '' S) (e z) at c
    rw [hi] at c
    have fr := e.toHomeomorph.image_frontier (connectedComponentIn S z)
    change e '' frontier (connectedComponentIn S z) = frontier (e '' connectedComponentIn S z) at fr
    rw [c] at fr
    unfold Erdos1041.length
    rw [← fr, e.hausdorffMeasure_image]
  change (⨆ z ∈ S, _) = ⨆ w ∈ T, _
  apply le_antisymm
  · apply iSup₂_le
    intro z hz
    exact (boundary z hz).le.trans (le_iSup₂_of_le (e z) (hi ▸ Set.mem_image_of_mem e hz) le_rfl)
  · apply iSup₂_le
    intro w hw
    rw [← hi] at hw
    obtain ⟨z,hz,rfl⟩ := hw
    exact (boundary z hz).ge.trans (le_iSup₂_of_le z hz le_rfl)

private theorem linear (a : ℂ) :
    maxBoundaryLength (X - C a) = maxBoundaryLength (X - 1) := by
  apply rigid _ _ (motion 1 (1-a) (by simp))
  intro z
  change ‖(X-1 : ℂ[X]).eval (1*z+(1-a))‖ = _
  simp
  ring_nf

private theorem centered (a b : ℂ) :
    maxBoundaryLength ((X-C a)*(X-C b)) =
      maxBoundaryLength (X^2 - C ((‖(a-b)/2‖:ℂ)^2)) := by
  let v := (a-b)/2
  let u := Complex.exp ((Complex.arg v : ℂ)*Complex.I)
  let c := (a+b)/2
  have hu : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have huv : (‖v‖:ℂ)*u = v := Complex.norm_mul_exp_arg_mul_I _
  symm
  apply rigid _ _ (motion u c hu)
  intro z
  change ‖(((X-C a)*(X-C b) : ℂ[X]).eval (u*z+c))‖ = _
  simp only [eval_mul,eval_sub,eval_X,eval_C,eval_pow]
  change ‖(u*z+c-a)*(u*z+c-b)‖ = ‖z^2-(‖v‖:ℂ)^2‖
  have h₁ : u*z+c-a = u*z-(‖v‖:ℂ)*u := by rw [huv]; dsimp [c,v]; ring
  have h₂ : u*z+c-b = u*z+(‖v‖:ℂ)*u := by rw [huv]; dsimp [c,v]; ring
  rw [h₁,h₂,show (u*z-(‖v‖:ℂ)*u)*(u*z+(‖v‖:ℂ)*u) = u^2*(z^2-(‖v‖:ℂ)^2) by ring,
      norm_mul,norm_pow,hu,one_pow,one_mul]

private theorem canonical (n : ℕ) (hn : n=1 ∨ n=2) :
    IsAdmissible (X^n-1) ∧ (X^n-1 : ℂ[X]).natDegree = n := by
  rcases hn with rfl | rfl
  · constructor
    · refine ⟨1, by decide, fun _ => 1, by simp, ?_⟩
      simp
    · simpa using (natDegree_X_sub_C (1 : ℂ))
  · let roots : Fin 2 → ℂ := ![1,-1]
    constructor
    · refine ⟨2, by decide, roots, ?_, ?_⟩
      · intro i; fin_cases i <;> simp [roots]
      · simp [roots,Fin.prod_univ_two]
        ring
    · simpa using (natDegree_X_pow_sub_C (R := ℂ) (n := 2) (r := (1:ℂ)))

/-- The singular Bernoulli lemniscate has individual lobes of perimeter at most four. -/
def H1 : Prop := maxBoundaryLength (X^2-1) ≤ 4

/-- The nonsingular centered Cassini ovals have perimeter at least four. -/
def H2 : Prop := ∀ t : ℝ, 0 ≤ t → t < 1 →
  4 ≤ maxBoundaryLength (X^2-C ((t:ℂ)^2))

theorem main : H1 → H2 → type_of% @Erdos1044.erdos_1044.variants.fixed_degree_of_le_two := by
  intro h₁ h₂ n hn
  obtain ⟨adm,deg⟩ := canonical n hn
  refine ⟨⟨_,adm,deg,rfl⟩,?_⟩
  rintro _ ⟨f,⟨m,hm,z,hz,rfl⟩,hd,rfl⟩
  rw [natDegree_prod_of_monic Finset.univ _ (fun i _ => monic_X_sub_C (z i))] at hd
  simp only [natDegree_X_sub_C,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at hd
  subst m
  rcases hn with rfl | rfl
  · simpa using (linear (z 0)).ge
  · rw [Fin.prod_univ_two,centered]
    let t := ‖(z 0-z 1)/2‖
    have ht : t ≤ 1 := by
      dsimp [t]
      rw [norm_div]
      norm_num
      linarith [norm_sub_le (z 0) (z 1), hz 0,hz 1]
    rcases lt_or_eq_of_le ht with h | h
    · exact h₁.trans (h₂ t (norm_nonneg _) h)
    · change maxBoundaryLength (X^2-1) ≤ maxBoundaryLength (X^2-C ((t:ℂ)^2))
      simp [h]

end OMA.CassiniTransfer


theorem OMA.solution : type_of% @Erdos1044.erdos_1044.variants.fixed_degree_of_le_two := by
  apply OMA.CassiniTransfer.main
  · apply CassiniModel.upper_of_cover CassiniModel.rightCover
      (CassiniModel.cover_bound CassiniModel.arc CassiniModel.arc_lipschitz)
    intro z hz
    have hc : {w : ℂ | ‖(X^2-1 : ℂ[X]).eval w‖ < 1} = CassiniModel.region := by
      ext w
      simp [CassiniModel.region]
    rw [hc] at hz ⊢
    exact CassiniModel.frontier_subset_lobe hz
  · intro t h₀ h₁
    simpa only [← Complex.ofReal_pow] using OMA.CassiniLower.lower (q := t^2)
      (sq_nonneg _) (by nlinarith [mul_pos (sub_pos.mpr h₁) (show 0<1+t by linarith)])
