import FormalConjectures.Paper.DeGiorgi
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# De Giorgi's conjecture in dimension two

Self-contained proof of `DeGiorgi.DeGiorgi_two` following Ghoussoub and Gui (1998):
1. Uniform bound on the transverse derivative (`OMA.DeGiorgiBound.solution`).
2. Weak divergence-form equation for the derivative quotient (`OMA.DeGiorgiWeak.solution`).
3. Planar weighted Liouville theorem (`OMA.PlanarLiouville.constant_of_weak_divergence`).
4. Affine level-set conclusion (`OMA.DeGiorgiTwo.hyperplanes_of_constant_quotient`).

See Ghoussoub and Gui (1998), https://doi.org/10.1007/s002080050196.
-/

namespace OMA.DeGiorgiBound

open EuclideanGeometry InnerProductSpace Metric Filter Set
open scoped Laplacian Topology

private abbrev Plane := ℝ²

private noncomputable def second (u : Plane → ℝ) (x d : Plane) : ℝ :=
  (fderiv ℝ (fderiv ℝ u) x d) d

private theorem line_deriv {u : Plane → ℝ} (hu : ContDiff ℝ 2 u) (x d : Plane) (t : ℝ) :
    HasDerivAt (fun s : ℝ => u (x + s • d)) (fderiv ℝ u (x + t • d) d) t :=
  (hu.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t
    (by simpa using (((hasDerivAt_id t).smul_const d).const_add x))

private theorem line_second {u : Plane → ℝ} (hu : ContDiff ℝ 2 u) (x d : Plane) :
    HasDerivAt (fun t : ℝ => fderiv ℝ u (x + t • d) d) (second u x d) 0 := by
  have hF : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hl : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x)
  have h := (hF.differentiable one_ne_zero (x + (0 : ℝ) • d)).hasFDerivAt.comp_hasDerivAt 0 hl
  have he := h.clm_apply (hasDerivAt_const (0 : ℝ) d)
  simpa [second] using he

private theorem second_neg_dir (u : Plane → ℝ) (x d : Plane) :
    second u x (-d) = second u x d := by simp [second]

private theorem sum_second {u : Plane → ℝ} (b : OrthonormalBasis (Fin 2) ℝ Plane) (x : Plane) :
    (Δ u) x = second u x (b 0) + second u x (b 1) := by
  simp [laplacian_eq_iteratedFDeriv_orthonormalBasis u b, Fin.sum_univ_two,
    iteratedFDeriv_two_apply, second]

private theorem quadratic_deriv (a b c t : ℝ) :
    HasDerivAt (fun s : ℝ => a + b * s + c * s ^ 2) (b + 2 * c * t) t := by
  have h := (((hasDerivAt_id t).const_mul b).const_add a).add
    ((hasDerivAt_pow 2 t).const_mul c)
  change HasDerivAt (fun s : ℝ => a + b * s + c * s ^ 2) _ t at h
  simpa [mul_comm c, mul_assoc, mul_left_comm] using h

private theorem affine_deriv (a b t : ℝ) :
    HasDerivAt (fun s : ℝ => a + b * s) b t := by
  simpa using (((hasDerivAt_id t).const_mul b).const_add a)

private theorem local_max_second_nonpos {f g : ℝ → ℝ} {s : ℝ}
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : HasDerivAt g s 0)
    (hm : IsLocalMax f 0) : s ≤ 0 := by
  by_contra! hs
  let p (t : ℝ) := f t - (0 + 0 * t + (s / 4) * t ^ 2)
  let d (t : ℝ) := g t - (0 + 2 * (s / 4) * t)
  have hp (t : ℝ) : HasDerivAt p (d t) t := (hf t).sub (quadratic_deriv 0 0 (s / 4) t)
  have hd : HasDerivAt d (s - 2 * (s / 4)) 0 := by
    exact hg.sub (affine_deriv 0 (2 * (s / 4)) 0)
  have hpd : deriv p = d := funext fun t => (hp t).deriv
  have hg0 : g 0 = 0 := (hf 0).deriv.symm.trans (hm.deriv_eq_zero)
  have hd0 : deriv p 0 = 0 := by simp [hpd, d, hg0]
  have hpmin : IsLocalMin p 0 := by
    apply isLocalMin_of_deriv_deriv_pos _ hd0 (hp 0).continuousAt
    rw [hpd, hd.deriv]
    linarith
  have hs' : ∀ᶠ t in 𝓝[≠] (0 : ℝ), p 0 ≤ p t ∧ f t ≤ f 0 ∧ t ≠ 0 :=
    (hpmin.filter_mono nhdsWithin_le_nhds).and
      ((hm.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin)
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := hs'.exists
  have hpos : 0 < (s / 4) * t ^ 2 := mul_pos (by positivity) (sq_pos_of_ne_zero ht₃)
  dsimp [p] at ht₁
  linarith

private theorem basis_with_first (d : Plane) (hd : ‖d‖ = 1) :
    ∃ b : OrthonormalBasis (Fin 2) ℝ Plane, b 0 = d := by
  let v : Fin 2 → Plane := fun _ => d
  let s : Set (Fin 2) := {0}
  have hs : Orthonormal ℝ (s.domRestrict v) := by
    let : Subsingleton s := ⟨fun i j => Subtype.ext
      (Set.subsingleton_singleton (a := (0 : Fin 2)) i.property j.property)⟩
    rw [orthonormal_subsingleton_iff]
    exact fun _ => hd
  obtain ⟨b, hb⟩ := hs.exists_orthonormalBasis_extension_of_card_eq
    (by simp [Plane])
  exact ⟨b, hb 0 (by simp [s])⟩

private noncomputable def modulus (L r : ℝ) : ℝ := L * (2 * r - r ^ 2)

private noncomputable def gap (u : Plane → ℝ) (L ε : ℝ) (p : Plane × Plane) : ℝ :=
  u p.2 - u p.1 - modulus L ‖p.2 - p.1‖ - ε * (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2)

private theorem gap_continuous {u : Plane → ℝ} (hu : Continuous u) (L ε : ℝ) :
    Continuous (gap u L ε) := by
  unfold gap modulus
  fun_prop

private theorem line_inequality {u : Plane → ℝ} (hu : ContDiff ℝ 2 u)
    (L ε : ℝ) (x y d e : Plane) (hd : ‖d‖ = 1) (he : ‖e‖ = 1)
    (k : ℝ)
    (hr : ∀ᶠ t : ℝ in 𝓝 0, ‖(y + t • e) - (x + t • d)‖ = ‖y - x‖ + k * t)
    (hm : IsLocalMax (fun t : ℝ => gap u L ε (x + t • d, y + t • e)) 0) :
    second u y e - second u x d ≤ 4*ε - 2 * L * k ^ 2 := by
  let r := ‖y - x‖
  let a := modulus L r + ε * (‖x‖ ^ 2 + ‖y‖ ^ 2)
  let b := L * (2 * k - 2 * r * k) + ε*(2 * inner ℝ x d + 2 * inner ℝ y e)
  let c := 2*ε - L * k ^ 2
  let F (t : ℝ) := u (y + t • e) - u (x + t • d) - (a + b * t + c * t ^ 2)
  let D (t : ℝ) := fderiv ℝ u (y + t • e) e - fderiv ℝ u (x + t • d) d - (b + 2 * c * t)
  have heq : (fun t : ℝ => gap u L ε (x + t • d, y + t • e)) =ᶠ[𝓝 0] F := by
    filter_upwards [hr] with t ht
    change u (y + t • e) - u (x + t • d) - modulus L ‖(y + t • e) - (x + t • d)‖ -
      ε*(‖x + t • d‖ ^ 2 + ‖y + t • e‖ ^ 2) = F t
    rw [ht, norm_add_sq_real, norm_add_sq_real]
    simp only [norm_smul, hd, he, mul_one, Real.norm_eq_abs, sq_abs, real_inner_smul_right]
    simp only [F, a, b, c, r, modulus]
    ring
  have hmF : IsLocalMax F 0 := hm.congr heq
  have hF (t : ℝ) : HasDerivAt F (D t) t :=
    ((line_deriv hu y e t).sub (line_deriv hu x d t)).sub (quadratic_deriv a b c t)
  have hD : HasDerivAt D (second u y e - second u x d - 2 * c) 0 :=
    ((line_second hu y e).sub (line_second hu x d)).sub
      (affine_deriv b (2 * c) 0)
  have hn := local_max_second_nonpos hF hD hmF
  dsimp [c] at hn
  linarith

private theorem gap_nonpos {u : Plane → ℝ} (hu : ContDiff ℝ 2 u)
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hBound : ∀ x, |u x| ≤ C) (hLap : ∀ x, |(Δ u) x| ≤ M)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (p : Plane × Plane) (hp : ‖p.2 - p.1‖ ≤ 1) :
    gap u (2 * C + M + 2) ε p ≤ 0 := by
  let L := 2 * C + M + 2
  have hL : 0 < L := by dsimp [L]; linarith
  by_contra! hpos
  let S : Set (Plane × Plane) := {p | ‖p.2 - p.1‖ ≤ 1 ∧ 0 ≤ gap u L ε p}
  have hmem : p ∈ S := ⟨hp, hpos.le⟩
  have hdiff (x y : Plane) : u y - u x ≤ 2 * C := by
    linarith [(abs_le.mp (hBound x)).1, (abs_le.mp (hBound y)).2]
  have hSclosed : IsClosed S :=
    (isClosed_le (continuous_snd.sub continuous_fst).norm continuous_const).inter
      (isClosed_le continuous_const (gap_continuous hu.continuous L ε))
  let R := Real.sqrt (2 * C/ε)
  have hS : IsCompact S := by
    have hballs : IsCompact (closedBall (0 : Plane) R ×ˢ closedBall (0 : Plane) R) :=
      (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
    apply hballs.of_isClosed_subset hSclosed
    intro q hq
    rcases hq with ⟨hqd, hqg⟩
    have hr : 0 ≤ ‖q.2 - q.1‖ := norm_nonneg _
    have hmod : 0 ≤ modulus L ‖q.2 - q.1‖ := by
      exact mul_nonneg hL.le (by nlinarith)
    have hsum : ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 ≤ 2 * C/ε := by
      apply (le_div_iff₀ hε).2
      dsimp only [gap] at hqg
      linarith [hdiff q.1 q.2]
    change q.1 ∈ closedBall 0 R ∧ q.2 ∈ closedBall 0 R
    constructor <;> rw [mem_closedBall, dist_zero_right] <;>
      apply Real.le_sqrt_of_sq_le <;> linarith [sq_nonneg ‖q.1‖, sq_nonneg ‖q.2‖]
  obtain ⟨⟨x,y⟩, ⟨hxy, _⟩, hmax⟩ := hS.exists_isMaxOn ⟨p, hmem⟩
    (gap_continuous hu.continuous L ε).continuousOn
  have hpmax : 0 < gap u L ε (x, y) := hpos.trans_le (isMaxOn_iff.mp hmax p hmem)
  let r := ‖y - x‖
  have hr0 : 0 < r := by
    by_contra! hn
    have heq : y = x := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))
    subst y
    have hpen : 0 ≤ ε * (‖x‖ ^ 2 + ‖x‖ ^ 2) := by positivity
    simp [gap, modulus, not_lt_of_ge hpen] at hpmax
  have hr1 : r < 1 := by
    by_contra! hn
    have hr1 : r = 1 := le_antisymm hxy hn
    have hmod : modulus L ‖y - x‖ = L := by
      change modulus L r = L
      norm_num [modulus, hr1]
    have hp' : 0 < u y - u x - L - ε*(‖x‖ ^ 2 + ‖y‖ ^ 2) := by
      simpa only [gap, hmod] using hpmax
    have hpen : 0 ≤ ε*(‖x‖ ^ 2 + ‖y‖ ^ 2) := by positivity
    dsimp [L] at hp'
    linarith [hdiff x y]
  have hlocal (d e : Plane) :
      IsLocalMax (fun t : ℝ => gap u L ε (x + t • d, y + t • e)) 0 := by
    have hc : ContinuousAt (fun t : ℝ => ‖(y + t • e) - (x + t • d)‖) 0 := by fun_prop
    have hzero : ‖(y + (0 : ℝ) • e) - (x + (0 : ℝ) • d)‖ < 1 := by simpa using hr1
    have hnear : ∀ᶠ t : ℝ in 𝓝 0, ‖(y + t • e) - (x + t • d)‖ < 1 :=
      hc (gt_mem_nhds hzero)
    change ∀ᶠ t : ℝ in 𝓝 0, gap u L ε (x + t • d, y + t • e) ≤
      gap u L ε (x + (0 : ℝ) • d, y + (0 : ℝ) • e)
    filter_upwards [hnear] with t ht
    simp only [zero_smul, add_zero]
    by_cases hg : 0 ≤ gap u L ε (x + t • d, y + t • e)
    · exact isMaxOn_iff.mp hmax _ ⟨ht.le, hg⟩
    · exact (lt_of_not_ge hg).le.trans hpmax.le
  let v : Plane := r⁻¹ • (y - x)
  have hnv : ‖v‖ = 1 := by
    rw [show v = r⁻¹ • (y - x) by rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr0)]
    exact inv_mul_cancel₀ hr0.ne'
  have hvec : y - x = r • v := by
    simp [v, smul_smul, mul_inv_cancel₀ hr0.ne']
  obtain ⟨b, hb⟩ := basis_with_first v hnv
  have hrad : ∀ᶠ t : ℝ in 𝓝 0, ‖(y + t • v) - (x + t • (-v))‖ = r + 2 * t := by
    have hC : ContinuousAt (fun t : ℝ => r + 2 * t) 0 := by fun_prop
    have hpos0 : 0 < r + 2 * (0 : ℝ) := by simpa using hr0
    filter_upwards [hC (lt_mem_nhds hpos0)] with t ht
    have he : (y + t • v) - (x + t • (-v)) = (y - x) + (2 * t) • v := by module
    rw [he, hvec, ← add_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hnv, mul_one]
  have hL0 := line_inequality hu L ε x y (-v) v (by simpa using hnv) hnv
    2 hrad (hlocal (-v) v)
  rw [second_neg_dir, ← hb] at hL0
  have hnormB : ‖b 1‖ = 1 := b.orthonormal.norm_eq_one 1
  have hparallel : ∀ᶠ t : ℝ in 𝓝 0, ‖(y + t • b 1) - (x + t • b 1)‖ = ‖y - x‖ + 0 * t := by
    exact Eventually.of_forall fun t => by simp [add_sub_add_right_eq_sub]
  have hL1 := line_inequality hu L ε x y (b 1) (b 1) hnormB hnormB
    0 hparallel (hlocal (b 1) (b 1))
  have htraceY := sum_second (u := u) b y
  have htraceX := sum_second (u := u) b x
  have htraceLower : -2 * M ≤ (Δ u) y - (Δ u) x := by
    linarith [(abs_le.mp (hLap y)).1, (abs_le.mp (hLap x)).2]
  norm_num at hL0 hL1
  dsimp only [L] at hL0
  linarith

private theorem modulus_bound {u : Plane → ℝ} (hu : ContDiff ℝ 2 u)
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hBound : ∀ x, |u x| ≤ C) (hLap : ∀ x, |(Δ u) x| ≤ M)
    (x y : Plane) (hxy : ‖y - x‖ ≤ 1) :
    u y - u x ≤ (2 * (2 * C + M + 2)) * ‖y - x‖ := by
  let L := 2 * C + M + 2
  have hL : 0 ≤ L := by dsimp [L]; linarith
  suffices h : u y - u x ≤ modulus L ‖y - x‖ by
    have hs : 0 ≤ L * ‖y - x‖ ^ 2 := by positivity
    unfold modulus at h
    change u y - u x ≤ 2 * L * ‖y - x‖
    linarith
  by_contra! hh
  let δ := u y - u x - modulus L ‖y - x‖
  let E := ‖x‖ ^ 2 + ‖y‖ ^ 2
  have hδ : 0 < δ := sub_pos.mpr hh
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let ε := min 1 (δ/(E + 1) / 2)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hεE : ε * E ≤ δ/2 := by
    calc
      _ ≤ ε*(E + 1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
      _ ≤ (δ/(E + 1) / 2) * (E + 1) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = _ := by field_simp
  have h := gap_nonpos hu hC hM hBound hLap hε (min_le_left _ _) (x, y) hxy
  change δ - ε*E ≤ 0 at h
  linarith

theorem solution (u : Plane → ℝ) (hu : DeGiorgi.IsBoundedSolution u) :
    ∃ D : ℝ, ∀ x, |fderiv ℝ u x (EuclideanSpace.single 1 1)| ≤ D := by
  obtain ⟨C, hC⟩ := hu.bounded
  have hCn : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  let M := C ^ 3 + C
  have hMn : 0 ≤ M := by dsimp [M]; positivity
  have hΔ (x : Plane) : |(Δ u) x| ≤ M := by
    have hPDE : (Δ u) x = u x ^ 3 - u x := by linarith [hu.solution x]
    rw [hPDE]
    calc
      _ ≤ |u x ^ 3| + |u x| := abs_sub _ _
      _ ≤ M := by
        rw [abs_pow]
        exact add_le_add (pow_le_pow_left₀ (abs_nonneg _) (hC x) 3) (hC x)
  let D := 2 * (2 * C + M + 2)
  have hD : 0 ≤ D := by dsimp [D]; linarith
  refine ⟨D, fun x => ?_⟩
  have hf : ‖fderiv ℝ u x‖ ≤ D := by
    apply norm_fderiv_le_of_lip' ℝ hD
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
    have hyx : ‖y - x‖ ≤ 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hy
      exact hy.le
    have hxy : ‖x - y‖ ≤ 1 := by rwa [norm_sub_rev]
    have hp := modulus_bound hu.regular hCn hMn hC hΔ x y hyx
    have hn := modulus_bound hu.regular hCn hMn hC hΔ y x hxy
    rw [norm_sub_rev x y] at hn
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by dsimp [D]; linarith, hp⟩
  calc
    _ ≤ ‖fderiv ℝ u x‖ * ‖EuclideanSpace.single 1 (1 : ℝ)‖ :=
      (fderiv ℝ u x).le_opNorm _
    _ ≤ D := by simpa using hf

end OMA.DeGiorgiBound

namespace OMA.DeGiorgiWeak

open EuclideanGeometry InnerProductSpace MeasureTheory Filter Set Finset
open scoped Gradient Laplacian Topology

private abbrev Plane := ℝ²

private noncomputable def partialDerivative (u : Plane → ℝ) (e : Plane) (x : Plane) : ℝ :=
  fderiv ℝ u x e

private theorem partial_continuous {u : Plane → ℝ} (h : ContDiff ℝ 1 u) (e : Plane) :
    Continuous (partialDerivative u e) :=
  (h.continuous_fderiv one_ne_zero).clm_apply continuous_const

private theorem partial_contDiff {u : Plane → ℝ} (h : ContDiff ℝ 2 u) (e : Plane) :
    ContDiff ℝ 1 (partialDerivative u e) :=
  (h.fderiv_right (by norm_num)).clm_apply contDiff_const

private theorem partial_compact {u : Plane → ℝ} (h : HasCompactSupport u) (e : Plane) :
    HasCompactSupport (partialDerivative u e) :=
  h.fderiv_apply ℝ e

private theorem integrate_compact_mul {a b : Plane → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hs : HasCompactSupport a) :
    Integrable (fun x => a x * b x) :=
  (ha.mul hb).integrable_of_hasCompactSupport (hs.mul_right (f' := b))

private theorem translated_deriv {f : Plane → ℝ} (hf : ContDiff ℝ 1 f)
    (x e : Plane) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • e)) (partialDerivative f e (x + t • e)) t := by
  exact (hf.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
    (by simpa using (((hasDerivAt_id t).smul_const e).const_add x))

private theorem shifted_integral_deriv {a f : Plane → ℝ}
    (ha : Continuous a) (hc : HasCompactSupport a) (hf : ContDiff ℝ 1 f) (e : Plane) :
    HasDerivAt (fun t : ℝ => ∫ x, a x * f (x + t • e))
      (∫ x, a x * partialDerivative f e x) 0 := by
  let F := fun (t : ℝ) (x : Plane) => a x * f (x + t • e)
  let D := fun (t : ℝ) (x : Plane) => a x * partialDerivative f e (x + t • e)
  let S := tsupport a
  let T : Set ℝ := Set.Icc (-1) 1
  have hT : T ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hS : MeasurableSet S := (isClosed_tsupport a).measurableSet
  have hjoint : Continuous (fun p : ℝ × Plane => D p.1 p.2) :=
    (ha.comp continuous_snd).mul
      ((partial_continuous hf e).comp (continuous_snd.add (continuous_fst.smul continuous_const)))
  have hTC : IsCompact T := isCompact_Icc
  obtain ⟨M, hM⟩ := (hTC.prod hc).exists_bound_of_continuousOn hjoint.continuousOn
  let bound := S.indicator fun _ => M
  have hBound : Integrable bound :=
    (integrableOn_const (μ := volume) (C := M)
      (hs := hc.measure_lt_top.ne)).integrable_indicator hS
  have hDom : ∀ᵐ x : Plane ∂volume, ∀ t ∈ T, ‖D t x‖ ≤ bound x := by
    refine ae_of_all _ fun x t ht => ?_
    by_cases hx : x ∈ S
    · rw [show bound x = M from indicator_of_mem hx _]
      exact hM (t, x) ⟨ht, hx⟩
    · have he : a x = 0 := by
        by_contra h
        exact hx (subset_closure h)
      rw [show bound x = 0 from indicator_of_notMem hx _]
      simp [D, he]
  have hF (t : ℝ) : Continuous (F t) :=
    ha.mul (hf.continuous.comp (continuous_id.add continuous_const))
  have hD (t : ℝ) : Continuous (D t) :=
    ha.mul ((partial_continuous hf e).comp (continuous_id.add continuous_const))
  have hFint : Integrable (F 0) := integrate_compact_mul ha
    (hf.continuous.comp (continuous_id.add continuous_const)) hc
  have hd (x : Plane) (t : ℝ) : HasDerivAt (F · x) (D t x) t :=
    (translated_deriv hf x e t).const_mul _
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hT
    (Eventually.of_forall fun t => (hF t).aestronglyMeasurable) hFint
    (hD 0).aestronglyMeasurable hDom hBound
    (ae_of_all _ fun x t _ => hd x t)).2
  simpa only [F, D, zero_smul, add_zero] using h

private theorem derivative_of_partial {u : Plane → ℝ} (hu : ContDiff ℝ 2 u)
    (e d x : Plane) :
    partialDerivative (partialDerivative u e) d x =
      (fderiv ℝ (fderiv ℝ u) x d) e := by
  have hF : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  unfold partialDerivative
  rw [fderiv_clm_apply (hF.differentiable one_ne_zero x) (differentiableAt_const e)]
  simp

private theorem partial_comm {u : Plane → ℝ} (hu : ContDiff ℝ 2 u)
    (x e d : Plane) :
    partialDerivative (partialDerivative u e) d x =
      partialDerivative (partialDerivative u d) e x := by
  rw [derivative_of_partial hu, derivative_of_partial hu]
  exact (hu.contDiffAt.isSymmSndFDerivAt (by simp)) d e

private theorem laplacian_as_partials {u : Plane → ℝ} (hu : ContDiff ℝ 2 u)
    (b : OrthonormalBasis (Fin 2) ℝ Plane) (x : Plane) :
    (Δ u) x = ∑ i, partialDerivative (partialDerivative u (b i)) (b i) x := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis u b]
  exact sum_congr rfl fun i _ => by
    rw [iteratedFDeriv_two_apply, derivative_of_partial hu]
    simp

private theorem inner_gradient_as_partials (u v : Plane → ℝ)
    (b : OrthonormalBasis (Fin 2) ℝ Plane) (x : Plane) :
    inner ℝ (∇ u x) (∇ v x) =
      ∑ i, partialDerivative u (b i) x * partialDerivative v (b i) x := by
  rw [← b.sum_inner_mul_inner]
  apply sum_congr rfl
  intro i _
  have h (f : Plane → ℝ) : inner ℝ (∇ f x) (b i) = partialDerivative f (b i) x := by
    rw [← toDual_apply_apply, toDual_gradient]
    rfl
  rw [h u, real_inner_comm (∇ v x) (b i), h v]

private theorem shifted_partial {g : Plane → ℝ} (hg : ContDiff ℝ 1 g)
    (s d x : Plane) :
    partialDerivative (fun y => g (y + s)) d x = partialDerivative g d (x + s) := by
  have hh := ((hg.differentiable one_ne_zero (x + s)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).add_const s)).fderiv
  change fderiv ℝ (fun y : Plane => g (y + s)) x =
    (fderiv ℝ g (x + s)).comp (ContinuousLinearMap.id ℝ Plane) at hh
  rw [ContinuousLinearMap.comp_id] at hh
  exact congrArg (fun L : Plane →L[ℝ] ℝ => L d) hh

private theorem integrate_shifted_by_parts {g η : Plane → ℝ} (hg : ContDiff ℝ 1 g)
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (s e : Plane) :
    (∫ x, partialDerivative η e x * g (x + s)) =
      -∫ x, η x * partialDerivative g e (x + s) := by
  let g' := fun x => g (x + s)
  have hg' : ContDiff ℝ 1 g' := hg.comp (contDiff_id.add contDiff_const)
  have h1 := integrate_compact_mul hη.continuous (partial_continuous hg' e) hηc
  have h2 := integrate_compact_mul (partial_continuous hη e) hg'.continuous (partial_compact hηc e)
  have h3 := integrate_compact_mul hη.continuous hg'.continuous hηc
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h2 h1 h3
    (fun x _ => hη.differentiable one_ne_zero x)
    (fun x _ => hg'.differentiable one_ne_zero x)
  change (∫ x, η x * partialDerivative g' e x) =
    -∫ x, partialDerivative η e x * g' x at h
  simp only [g', shifted_partial hg] at h ⊢
  linarith

private theorem reaction_derivative {u : Plane → ℝ} (hu : ContDiff ℝ 2 u)
    (e x : Plane) :
    partialDerivative (fun y => u y ^ 3 - u y) e x =
      (3 * (u x)^2 - 1) * partialDerivative u e x := by
  have h := (hu.differentiable (by norm_num) x).hasFDerivAt
  have he := congrArg (fun L : Plane →L[ℝ] ℝ => L e) ((h.pow 3).sub h).fderiv
  unfold partialDerivative
  simp only [sub_apply, smul_apply, smul_eq_mul] at he
  change (fderiv ℝ (fun y => u y ^ 3 - u y) x) e =
    3 • u x ^ (3 - 1) * (fderiv ℝ u x) e - (fderiv ℝ u x) e at he
  rw [he]
  norm_num
  ring

private theorem weak_partial {u : Plane → ℝ} (hu : DeGiorgi.IsBoundedSolution u)
    (e : Plane) {η : Plane → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    (∫ x, inner ℝ (∇ (partialDerivative u e) x) (∇ η x)) +
      (∫ x, η x * ((3 * (u x)^2 - 1) * partialDerivative u e x)) = 0 := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let g (i : Fin 2) := partialDerivative u (b i)
  let a (i : Fin 2) := partialDerivative η (b i)
  let F (x : Plane) := u x ^ 3 - u x
  let W (t : ℝ) := (∑ i, ∫ x, a i x * g i (x + t • e)) + ∫ x, η x * F (x + t • e)
  have hg (i : Fin 2) : ContDiff ℝ 1 (g i) := partial_contDiff hu.regular (b i)
  have ha (i : Fin 2) : Continuous (a i) := partial_continuous hη (b i)
  have hac (i : Fin 2) : HasCompactSupport (a i) := partial_compact hηc (b i)
  have hU : ContDiff ℝ 1 u := hu.regular.of_le (by norm_num)
  have hF : ContDiff ℝ 1 F := (hU.pow 3).sub hU
  have hW : W = fun _ => 0 := by
    funext t
    have hLi (i : Fin 2) : Integrable
        (fun x => η x * partialDerivative (g i) (b i) (x + t • e)) :=
      integrate_compact_mul hη.continuous
        ((partial_continuous (hg i) (b i)).comp (continuous_id.add continuous_const)) hηc
    have hsum : (∑ i, ∫ x, a i x * g i (x + t • e)) = -(∫ x, η x * F (x + t • e)) := by
      calc
        _ = ∑ i, -(∫ x, η x * partialDerivative (g i) (b i) (x + t • e)) :=
          sum_congr rfl fun i _ => integrate_shifted_by_parts (hg i) hη hηc _ _
        _ = -(∫ x, ∑ i, η x * partialDerivative (g i) (b i) (x + t • e)) := by
          rw [sum_neg_distrib, integral_finsetSum _ (fun i _ => hLi i)]
        _ = _ := by
          congr 1
          apply integral_congr_ae
          filter_upwards [] with x
          rw [← mul_sum]
          change η x * (∑ i, partialDerivative (partialDerivative u (b i)) (b i)
            (x + t • e)) = η x * F (x + t • e)
          rw [← laplacian_as_partials hu.regular b]
          congr 1
          have hpde := hu.solution (x + t • e)
          dsimp [F]
          linarith
    change (∑ i, ∫ x, a i x * g i (x + t • e)) + (∫ x, η x * F (x + t • e)) = 0
    rw [hsum, neg_add_cancel]
  have hsumdiff := HasDerivAt.fun_sum (u := (univ : Finset (Fin 2)))
    (fun i _ => shifted_integral_deriv (ha i) (hac i) (hg i) e)
  have hD : HasDerivAt W ((∑ i, ∫ x, a i x * partialDerivative (g i) e x) +
      ∫ x, η x * partialDerivative F e x) 0 :=
    hsumdiff.add (shifted_integral_deriv hη.continuous hηc hF e)
  have hz := hD.deriv
  rw [hW, deriv_const] at hz
  calc
    _ = (∑ i, ∫ x, a i x * partialDerivative (g i) e x) +
        (∫ x, η x * partialDerivative F e x) := ?_
    _ = 0 := hz.symm
  congr 1
  · have hIi (i : Fin 2) : Integrable
        (fun x => a i x * partialDerivative (g i) e x) :=
      integrate_compact_mul (ha i) (partial_continuous (hg i) e) (hac i)
    rw [← integral_finsetSum _ (fun i _ => hIi i)]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [inner_gradient_as_partials _ _ b]
    apply sum_congr rfl
    intro i _
    change partialDerivative (partialDerivative u e) (b i) x * a i x =
      a i x * partialDerivative (partialDerivative u (b i)) e x
    rw [partial_comm hu.regular, mul_comm]
  · apply integral_congr_ae
    filter_upwards [] with x
    change η x * ((3 * u x ^ 2 - 1) * partialDerivative u e x) =
      η x * partialDerivative (fun y => u y ^ 3 - u y) e x
    rw [reaction_derivative hu.regular]

private theorem gradient_product {f g : Plane → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (x : Plane) :
    ∇ (fun y => f y * g y) x = f x • ∇ g x + g x • ∇ f x := by
  unfold gradient
  rw [fderiv_fun_mul (hf.differentiable one_ne_zero x) (hg.differentiable one_ne_zero x)]
  simp only [map_add, map_smul]

private theorem inner_gradient_integrable {f g : Plane → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    Integrable (fun x => inner ℝ (∇ f x) (∇ g x)) := by
  have hGrad {h : Plane → ℝ} (hh : ContDiff ℝ 1 h) : Continuous (∇ h) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hh.continuous_fderiv one_ne_zero)
  apply ((hGrad hf).inner (hGrad hg)).integrable_of_hasCompactSupport
  apply hgc.mono'
  intro x hx
  apply support_fderiv_subset ℝ
  change fderiv ℝ g x ≠ 0
  intro he
  exact hx (by simp [gradient, he])

private theorem quotient_flux {v w η : Plane → ℝ} (hv : ContDiff ℝ 1 v)
    (hw : ContDiff ℝ 1 w) (hη : ContDiff ℝ 1 η) (hne : ∀ x, v x ≠ 0) (x : Plane) :
    (v x)^2 * inner ℝ (∇ (fun y => w y / v y) x) (∇ η x) =
      inner ℝ (∇ w x) (∇ (fun y => v y * η y) x) -
      inner ℝ (∇ v x) (∇ (fun y => w y * η y) x) := by
  let q := fun y => w y / v y
  have hq : ContDiff ℝ 1 q := hw.div hv hne
  have hqv (y : Plane) : v y * q y = w y := by
    dsimp [q]
    field_simp [hne y]
  have hwq : (fun y => v y * q y) = w := funext hqv
  have hgw := gradient_product hv hq x
  rw [hwq] at hgw
  change (v x)^2 * inner ℝ (∇ q x) (∇ η x) = _
  rw [gradient_product hv hη, gradient_product hw hη]
  simp only [inner_add_right, real_inner_smul_right]
  rw [real_inner_comm (∇ w x) (∇ v x)]
  rw [hgw]
  simp only [inner_add_left, real_inner_smul_left]
  rw [← hqv x]
  ring

set_option maxHeartbeats 600000 in
theorem solution (u : Plane → ℝ) (hu : DeGiorgi.IsBoundedSolution u)
    (hpos : DeGiorgi.HasPositiveDeriv u) :
    let v := partialDerivative u (EuclideanSpace.single 0 1)
    let w := partialDerivative u (EuclideanSpace.single 1 1)
    ∀ η : Plane → ℝ, ContDiff ℝ 1 η → HasCompactSupport η →
      (∫ x, (v x)^2 * inner ℝ (∇ (fun y => w y / v y) x) (∇ η x)) = 0 := by
  intro v w η hη hηc
  have hv : ContDiff ℝ 1 v := partial_contDiff hu.regular _
  have hw : ContDiff ℝ 1 w := partial_contDiff hu.regular _
  have hv0 (x : Plane) : v x ≠ 0 := by
    have h := hpos x
    rw [(hu.regular.differentiable (by norm_num) x).lineDeriv_eq_fderiv] at h
    exact h.ne'
  have hvη : ContDiff ℝ 1 (fun x => v x * η x) := hv.mul hη
  have hwη : ContDiff ℝ 1 (fun x => w x * η x) := hw.mul hη
  have hvηc : HasCompactSupport (fun x => v x * η x) := hηc.mul_left (f := v)
  have hwηc : HasCompactSupport (fun x => w x * η x) := hηc.mul_left (f := w)
  have hweakW := weak_partial hu (EuclideanSpace.single 1 1) hvη hvηc
  have hweakV := weak_partial hu (EuclideanSpace.single 0 1) hwη hwηc
  let reaction := fun x => 3 * (u x)^2 - 1
  have hcancel : (∫ x, (v x * η x) * (reaction x * w x)) =
      (∫ x, (w x * η x) * (reaction x * v x)) :=
    integral_congr_ae (ae_of_all _ fun x => by ring)
  change (∫ x, inner ℝ (∇ w x) (∇ (fun y => v y * η y) x)) +
    (∫ x, (v x * η x) * (reaction x * w x)) = 0 at hweakW
  change (∫ x, inner ℝ (∇ v x) (∇ (fun y => w y * η y) x)) +
    (∫ x, (w x * η x) * (reaction x * v x)) = 0 at hweakV
  have hdiff : (∫ x, inner ℝ (∇ w x) (∇ (fun y => v y * η y) x)) =
      (∫ x, inner ℝ (∇ v x) (∇ (fun y => w y * η y) x)) := by
    rw [hcancel] at hweakW
    linarith
  calc
    _ = ∫ x, (inner ℝ (∇ w x) (∇ (fun y => v y * η y) x) -
        inner ℝ (∇ v x) (∇ (fun y => w y * η y) x)) :=
      integral_congr_ae (ae_of_all _ (quotient_flux hv hw hη hv0))
    _ = 0 := by
      rw [integral_sub (inner_gradient_integrable hw hvη hvηc)
        (inner_gradient_integrable hv hwη hwηc), hdiff, sub_self]

end OMA.DeGiorgiWeak

namespace OMA.PlanarLiouville

open EuclideanGeometry InnerProductSpace MeasureTheory Metric Set Filter
open scoped Gradient Topology

private abbrev Plane := ℝ²

private theorem gradient_continuous {u : Plane → ℝ} (hu : ContDiff ℝ 1 u) :
    Continuous (∇ u) :=
  (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hu.continuous_fderiv one_ne_zero)

private theorem gradient_compact {u : Plane → ℝ} (hu : HasCompactSupport u) :
    HasCompactSupport (∇ u) := by
  apply hu.mono'
  intro x hx
  apply support_fderiv_subset ℝ
  change fderiv ℝ u x ≠ 0
  intro he
  exact hx (by simp [gradient, he])

private theorem norm_gradient {u : Plane → ℝ} (x : Plane) :
    ‖∇ u x‖ = ‖fderiv ℝ u x‖ :=
  (InnerProductSpace.toDual ℝ Plane).symm.norm_map _

private noncomputable def baseBump : ContDiffBump (0 : Plane) :=
  ⟨1, 2, by norm_num, by norm_num⟩

private noncomputable def cutoff (r : ℝ) (x : Plane) : ℝ := baseBump (r⁻¹ • x)

private theorem cutoff_smooth (r : ℝ) : ContDiff ℝ 1 (cutoff r) := by
  have h : ContDiff ℝ 1 (fun x : Plane => r⁻¹ • x) := contDiff_id.const_smul _
  exact baseBump.contDiff.comp h

private theorem cutoff_compact {r : ℝ} (hr : 0 < r) : HasCompactSupport (cutoff r) :=
  baseBump.hasCompactSupport.comp_smul (inv_ne_zero hr.ne')

private theorem cutoff_bounds (r : ℝ) (x : Plane) : 0 ≤ cutoff r x ∧ cutoff r x ≤ 1 :=
  ⟨baseBump.nonneg, baseBump.le_one⟩

private theorem cutoff_one {r : ℝ} (hr : 0 < r) {x : Plane}
    (hx : x ∈ closedBall (0 : Plane) r) : cutoff r x = 1 := by
  apply baseBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
    inv_mul_eq_div, div_le_iff₀ hr, show baseBump.rIn = 1 from rfl, one_mul]
  exact mem_closedBall_zero_iff.mp hx

private theorem cutoff_zero {r : ℝ} (hr : 0 < r) {x : Plane}
    (hx : x ∉ closedBall (0 : Plane) (2 * r)) : cutoff r x = 0 := by
  apply baseBump.zero_of_le_dist
  change 2 ≤ dist (r⁻¹ • x) 0
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
    inv_mul_eq_div, le_div_iff₀ hr]
  exact le_of_lt (lt_of_not_ge (fun he => hx (mem_closedBall_zero_iff.mpr he)))

private theorem gradient_zero_of_cutoff_zero {r : ℝ} {x : Plane} (h : cutoff r x = 0) :
    ∇ (cutoff r) x = 0 := by
  have hmin : IsLocalMin (cutoff r) x :=
    Eventually.of_forall fun y => by rw [h]; exact (cutoff_bounds r y).1
  simp [gradient, hmin.fderiv_eq_zero]

private theorem gradient_zero_of_cutoff_one {r : ℝ} {x : Plane} (h : cutoff r x = 1) :
    ∇ (cutoff r) x = 0 := by
  have hmax : IsLocalMax (cutoff r) x :=
    Eventually.of_forall fun y => by rw [h]; exact (cutoff_bounds r y).2
  simp [gradient, hmax.fderiv_eq_zero]

private theorem cutoff_fderiv (r : ℝ) (x : Plane) :
    fderiv ℝ (cutoff r) x =
      (fderiv ℝ (fun y : Plane => baseBump y) (r⁻¹ • x)).comp
        (r⁻¹ • ContinuousLinearMap.id ℝ Plane) := by
  let L : Plane →L[ℝ] Plane := r⁻¹ • ContinuousLinearMap.id ℝ Plane
  have hdiff : Differentiable ℝ (fun y : Plane => baseBump y) :=
    (baseBump.contDiff (n := 1)).differentiable (by norm_num)
  exact ((hdiff (L x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv

private theorem cutoff_gradient_norm {r : ℝ} (hr : 0 < r) (M : ℝ)
    (hM : ∀ x : Plane, ‖fderiv ℝ (fun y : Plane => baseBump y) x‖ ≤ M)
    (x : Plane) : ‖∇ (cutoff r) x‖ ≤ M / r := by
  rw [norm_gradient, cutoff_fderiv]
  apply ContinuousLinearMap.opNorm_comp_le _ _ |>.trans
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, ContinuousLinearMap.norm_id, mul_one,
    div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (hM _) (inv_nonneg.mpr hr.le)

private theorem compact_gradient_square {u : Plane → ℝ} (hu : HasCompactSupport u) :
    HasCompactSupport (fun x => ‖∇ u x‖ ^ 2) := by
  apply (gradient_compact hu).mono'
  intro x hx
  apply subset_closure
  change ∇ u x ≠ 0
  intro he
  exact hx (by simp [he])

private theorem cutoff_energy_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 0 < r → (∫ x, ‖∇ (cutoff r) x‖ ^ 2) ≤ K := by
  obtain ⟨M, hM⟩ := (baseBump.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    ((baseBump.contDiff (n := 1)).continuous_fderiv one_ne_zero)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  let K := 4 * M ^ 2 * (volume : Measure Plane).real (ball 0 1)
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro r hr
  have hcompact := compact_gradient_square (cutoff_compact hr)
  have hcont := (gradient_continuous (cutoff_smooth r)).norm.pow 2
  have hInt := hcont.integrable_of_hasCompactSupport (μ := volume) hcompact
  have hdim : Module.finrank ℝ Plane = 2 := finrank_euclideanSpace_fin
  calc
    _ = ∫ x in closedBall (0 : Plane) (2 * r), ‖∇ (cutoff r) x‖ ^ 2 := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [gradient_zero_of_cutoff_zero (cutoff_zero hr hx)]
      simp
    _ ≤ ∫ _x in closedBall (0 : Plane) (2 * r), (M / r) ^ 2 := by
      apply setIntegral_mono_on hInt.integrableOn
        (integrableOn_const (hs := (isCompact_closedBall _ _).measure_lt_top.ne))
        measurableSet_closedBall
      intro x _
      exact pow_le_pow_left₀ (norm_nonneg _) (cutoff_gradient_norm hr M hM x) 2
    _ = K := by
      rw [setIntegral_const, smul_eq_mul, Measure.addHaar_real_closedBall _ _ (by positivity), hdim]
      dsimp [K]
      field_simp [hr.ne']
      ring

private noncomputable def energy (v q : Plane → ℝ) (x : Plane) : ℝ :=
  (v x) ^ 2 * ‖∇ q x‖ ^ 2

private theorem energy_continuous {v q : Plane → ℝ}
    (hv : ContDiff ℝ 1 v) (hq : ContDiff ℝ 1 q) : Continuous (energy v q) :=
  (hv.continuous.pow 2).mul ((gradient_continuous hq).norm.pow 2)

private theorem energy_nonneg (v q : Plane → ℝ) (x : Plane) : 0 ≤ energy v q x := by
  unfold energy
  positivity

private theorem energy_cutoff_integrable {v q η : Plane → ℝ}
    (hv : ContDiff ℝ 1 v) (hq : ContDiff ℝ 1 q) (hη : ContDiff ℝ 1 η)
    (hs : HasCompactSupport η) : Integrable (fun x => (η x) ^ 2 * energy v q x) := by
  have hx : HasCompactSupport (fun x => (η x) ^ 2 * energy v q x) := by
    apply hs.mono'
    intro x h
    apply subset_closure
    change η x ≠ 0
    intro he
    exact h (by simp [he])
  exact ((hη.continuous.pow 2).mul (energy_continuous hv hq)).integrable_of_hasCompactSupport hx

private theorem young {δ : ℝ} (hδ : 0 < δ) (a b : ℝ) :
    2 * a * b ≤ δ * a ^ 2 + b ^ 2 / δ := by
  apply sub_nonneg.mp
  have he : δ * a ^ 2 + b ^ 2 / δ - 2 * a * b = (δ * a - b) ^ 2 / δ := by
    field_simp [hδ.ne']
    ring
  rw [he]
  exact div_nonneg (sq_nonneg _) hδ.le

private theorem test_gradient {q η : Plane → ℝ} (hq : ContDiff ℝ 1 q)
    (hη : ContDiff ℝ 1 η) (x : Plane) :
    ∇ (fun y => q y * (η y) ^ 2) x =
      (η x) ^ 2 • ∇ q x + (2 * q x * η x) • ∇ η x := by
  have hqd := (hq.differentiable one_ne_zero x)
  have hηd := (hη.differentiable one_ne_zero x)
  have hm := fderiv_fun_mul (c := q) (d := fun y => (η y) ^ 2) hqd (hηd.pow 2)
  have hp := fderiv_fun_pow 2 hηd
  unfold gradient
  rw [hm, hp]
  simp only [map_add, map_smul, show 2 - (1 : ℕ) = 1 by decide, pow_one, nsmul_eq_mul,
    Nat.cast_ofNat, smul_smul]
  rw [add_comm]
  congr 1
  congr 1
  ring

private theorem weak_energy_estimate (v q η A : Plane → ℝ) (C δ : ℝ)
    (hv : ContDiff ℝ 1 v) (hq : ContDiff ℝ 1 q) (hη : ContDiff ℝ 1 η)
    (hηc : HasCompactSupport η) (hvpos : ∀ x, 0 < v x)
    (hη0 : ∀ x, 0 ≤ η x) (hC : ∀ x, |v x * q x| ≤ C) (hδ : 0 < δ)
    (hweak : ∀ ψ : Plane → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, (v x) ^ 2 * inner ℝ (∇ q x) (∇ ψ x)) = 0)
    (hAi : Integrable A) (hA0 : ∀ x, 0 ≤ A x)
    (hA : ∀ x, ∇ η x ≠ 0 → (η x) ^ 2 * energy v q x ≤ A x) :
    (∫ x, (η x) ^ 2 * energy v q x) ≤
      δ * (∫ x, A x) + (C ^ 2 / δ) * (∫ x, ‖∇ η x‖ ^ 2) := by
  let ψ := fun x => q x * (η x) ^ 2
  have hψ : ContDiff ℝ 1 ψ := hq.mul (hη.pow 2)
  have hψc : HasCompactSupport ψ := by
    apply hηc.mono'
    intro x hx
    apply subset_closure
    change η x ≠ 0
    intro he
    exact hx (by simp [ψ, he])
  let F := fun x => (v x) ^ 2 * inner ℝ (∇ q x) (∇ ψ x)
  have hFc : HasCompactSupport F := by
    apply (gradient_compact hψc).mono'
    intro x hx
    apply subset_closure
    change ∇ ψ x ≠ 0
    intro he
    apply hx
    change (v x) ^ 2 * inner ℝ (∇ q x) (∇ ψ x) = 0
    rw [he, inner_zero_right, mul_zero]
  have hFi : Integrable F :=
    ((hv.continuous.pow 2).mul
      ((gradient_continuous hq).inner (gradient_continuous hψ))).integrable_of_hasCompactSupport hFc
  have hFzero : (∫ x, F x) = 0 := hweak ψ hψ hψc
  have hGi : Integrable (fun x => ‖∇ η x‖ ^ 2) :=
    ((gradient_continuous hη).norm.pow 2).integrable_of_hasCompactSupport (compact_gradient_square hηc)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hCross (x : Plane) :
      F x = (η x) ^ 2 * energy v q x +
        2 * (η x) * (v x) ^ 2 * (q x) * inner ℝ (∇ q x) (∇ η x) := by
    simp only [F, ψ, test_gradient hq hη, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, energy]
    ring
  have hpoint (x : Plane) :
      (η x) ^ 2 * energy v q x ≤ F x + δ * A x + (C ^ 2 / δ) * ‖∇ η x‖ ^ 2 := by
    rw [hCross]
    by_cases hz : ∇ η x = 0
    · simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), inner_zero_right, mul_zero,
        add_zero]
      exact le_add_of_nonneg_right (mul_nonneg hδ.le (hA0 x))
    have hb : -(v x * q x * inner ℝ (∇ q x) (∇ η x)) ≤
        C * (‖∇ q x‖ * ‖∇ η x‖) := by
      calc
        _ ≤ |v x * q x * inner ℝ (∇ q x) (∇ η x)| := neg_le_abs _
        _ = |v x * q x| * |inner ℝ (∇ q x) (∇ η x)| := abs_mul _ _
        _ ≤ _ := mul_le_mul (hC x) (abs_real_inner_le_norm _ _) (abs_nonneg _) hC0
    have hxb := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * η x * v x by
      exact mul_nonneg (mul_nonneg (by norm_num) (hη0 x)) (hvpos x).le)
    have hxy := young hδ (η x * v x * ‖∇ q x‖) (C * ‖∇ η x‖)
    have hxa := mul_le_mul_of_nonneg_left (hA x hz) hδ.le
    unfold energy at hxa
    simp only [div_eq_mul_inv] at hxy ⊢
    nlinarith only [hxb, hxy, hxa]
  have hi := integral_mono (energy_cutoff_integrable hv hq hη hηc)
    ((hFi.add (hAi.const_mul δ)).add (hGi.const_mul (C ^ 2 / δ))) hpoint
  simp only [Pi.add_apply] at hi
  have hsum1 : (∫ x, F x + δ * A x) = (∫ x, F x) + ∫ x, δ * A x :=
    integral_add hFi (hAi.const_mul δ)
  have hsum2 : (∫ x, F x + δ * A x + (C ^ 2 / δ) * ‖∇ η x‖ ^ 2) =
      (∫ x, F x + δ * A x) + ∫ x, (C ^ 2 / δ) * ‖∇ η x‖ ^ 2 := by
    simpa only [Pi.add_apply] using
      integral_add (hFi.add (hAi.const_mul δ)) (hGi.const_mul (C ^ 2 / δ))
  rw [hsum2, hsum1, hFzero, zero_add, integral_const_mul, integral_const_mul] at hi
  exact hi

theorem constant_of_weak_divergence (v q : Plane → ℝ)
    (hv : ContDiff ℝ 1 v) (hq : ContDiff ℝ 1 q) (hvpos : ∀ x, 0 < v x)
    (hb : ∃ C : ℝ, ∀ x, |v x * q x| ≤ C)
    (hweak : ∀ η : Plane → ℝ, ContDiff ℝ 1 η → HasCompactSupport η →
      (∫ x, (v x) ^ 2 * inner ℝ (∇ q x) (∇ η x)) = 0) :
    ∃ c : ℝ, ∀ x, q x = c := by
  classical
  obtain ⟨C, hC⟩ := hb
  obtain ⟨K, hK0, hCut⟩ := cutoff_energy_bound
  let E := energy v q
  let r := fun m : ℕ => (m : ℝ) + 1
  let S := fun m => closedBall (0 : Plane) (r m)
  let W := fun m x => (cutoff (r m) x) ^ 2 * E x
  have hp (m : ℕ) : 0 < r m := by dsimp [r]; positivity
  have hS (m : ℕ) : MeasurableSet (S m) := measurableSet_closedBall
  have hEc : Continuous E := energy_continuous hv hq
  have hE0 (x : Plane) : 0 ≤ E x := energy_nonneg _ _ _
  have hWi (m : ℕ) : Integrable (W m) :=
    energy_cutoff_integrable hv hq (cutoff_smooth _) (cutoff_compact (hp m))
  have hW0 (m : ℕ) (x : Plane) : 0 ≤ W m x :=
    mul_nonneg (sq_nonneg _) (hE0 x)
  have hLocal (m : ℕ) : (∫ x in S m, E x) ≤ ∫ x, W m x := by
    calc
      _ = ∫ x in S m, W m x := by
        apply setIntegral_congr_fun (hS m)
        intro x hx
        change E x = (cutoff (r m) x) ^ 2 * E x
        rw [cutoff_one (hp m) hx, one_pow, one_mul]
      _ ≤ _ := setIntegral_le_integral (hWi _) (ae_of_all _ (hW0 _))
  have hBound (m : ℕ) : (∫ x in S m, E x) ≤ 4 * C ^ 2 * K := by
    have h1 := weak_energy_estimate v q (cutoff (r m)) (W m) C (1 / 2)
      hv hq (cutoff_smooth _) (cutoff_compact (hp m)) hvpos
      (fun x => (cutoff_bounds _ x).1) hC (by norm_num) hweak (hWi m) (hW0 m) (by simp [W, E])
    change (∫ x, W m x) ≤ (1 / 2) * (∫ x, W m x) +
      (C ^ 2 / (1 / 2)) * (∫ x, ‖∇ (cutoff (r m)) x‖ ^ 2) at h1
    have h2 := mul_le_mul_of_nonneg_left (hCut (r m) (hp m))
      (by positivity : 0 ≤ C ^ 2 / (1 / 2))
    linarith [hLocal m]
  have hrTop : Tendsto r atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hCover : AECover (volume : Measure Plane) atTop S := aecover_closedBall hrTop
  have hEi : Integrable E := hCover.integrable_of_integral_bounded_of_nonneg_ae
    (4 * C ^ 2 * K)
    (fun m => hEc.continuousOn.integrableOn_compact (isCompact_closedBall _ _))
    (ae_of_all _ hE0) (Eventually.of_forall hBound)
  let I := ∫ x, E x
  have hLimit : Tendsto (fun m : ℕ => ∫ x in S m, E x) atTop (𝓝 I) :=
    hCover.integral_tendsto_of_countably_generated hEi
  have hTail : Tendsto (fun m : ℕ => ∫ x in (S m)ᶜ, E x) atTop (𝓝 (0 : ℝ)) := by
    have hsub : Tendsto (fun m : ℕ => I - ∫ x in S m, E x) atTop (𝓝 (I - I)) :=
      tendsto_const_nhds.sub hLimit
    rw [sub_self] at hsub
    exact hsub.congr fun m => (setIntegral_compl (hS m) hEi).symm
  have hBig (δ : ℝ) (hδ : 0 < δ) : I ≤ (C ^ 2 / δ) * K := by
    have hEst (m : ℕ) : (∫ x in S m, E x) ≤
        δ * (∫ x in (S m)ᶜ, E x) + (C ^ 2 / δ) * K := by
      let A := (S m)ᶜ.indicator E
      have hAi : Integrable A := hEi.indicator (hS m).compl
      have hA0 (x : Plane) : 0 ≤ A x := by
        by_cases hx : x ∈ (S m)ᶜ
        · rw [show A x = E x from indicator_of_mem hx _]
          exact hE0 x
        · rw [show A x = 0 from indicator_of_notMem hx _]
      have hDom (x : Plane) (hx : ∇ (cutoff (r m)) x ≠ 0) : W m x ≤ A x := by
        have hxS : x ∈ (S m)ᶜ := fun h =>
          hx (gradient_zero_of_cutoff_one (cutoff_one (hp m) h))
        rw [show A x = E x from indicator_of_mem hxS _]
        change (cutoff (r m) x) ^ 2 * E x ≤ E x
        have hη := cutoff_bounds (r m) x
        exact mul_le_of_le_one_left (hE0 x) (pow_le_one₀ hη.1 hη.2)
      have h1 := weak_energy_estimate v q (cutoff (r m)) A C δ
        hv hq (cutoff_smooth _) (cutoff_compact (hp m)) hvpos
        (fun x => (cutoff_bounds _ x).1) hC hδ hweak hAi hA0 hDom
      change (∫ x, W m x) ≤ δ * (∫ x, A x) +
        (C ^ 2 / δ) * (∫ x, ‖∇ (cutoff (r m)) x‖ ^ 2) at h1
      rw [show (∫ x, A x) = ∫ x in (S m)ᶜ, E x from integral_indicator (hS m).compl] at h1
      have h2 := mul_le_mul_of_nonneg_left (hCut (r m) (hp m))
        (by positivity : 0 ≤ C ^ 2 / δ)
      linarith [hLocal m]
    have hright : Tendsto (fun m => δ * (∫ x in (S m)ᶜ, E x) + (C ^ 2 / δ) * K)
        atTop (𝓝 ((C ^ 2 / δ) * K)) := by
      simpa only [mul_zero, zero_add] using (tendsto_const_nhds.mul hTail).add
        (tendsto_const_nhds (x := (C ^ 2 / δ) * K))
    exact le_of_tendsto_of_tendsto hLimit hright (Eventually.of_forall hEst)
  have hI : I = 0 := by
    have hI0 : 0 ≤ I := integral_nonneg hE0
    by_contra h
    have hIp : 0 < I := lt_of_le_of_ne hI0 (fun h0 => h h0.symm)
    let δ := (C ^ 2 * K + 1) / I
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have h1 := hBig δ hδ
    have h2 : I * δ ≤ C ^ 2 * K := (le_div_iff₀ hδ).mp (by
      simpa only [div_mul_eq_mul_div] using h1)
    have hd : I * δ = C ^ 2 * K + 1 := by dsimp [δ]; field_simp [hIp.ne']
    linarith
  have hAE : E =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hE0 hEi).mp hI
  have hzero : E = 0 := (hEc.ae_eq_iff_eq volume continuous_zero).mp hAE
  have hfzero (x : Plane) : fderiv ℝ q x = 0 := by
    have hx := congrFun hzero x
    change (v x) ^ 2 * ‖∇ q x‖ ^ 2 = 0 at hx
    have hy : ‖∇ q x‖ ^ 2 = 0 :=
      (mul_eq_zero.mp hx).resolve_left (pow_ne_zero _ (hvpos x).ne')
    have hnorm : ‖∇ q x‖ = 0 := by
      by_contra h
      exact (pow_ne_zero _ h) hy
    have hg : ∇ q x = 0 := norm_eq_zero.mp hnorm
    rw [← toDual_gradient, hg, map_zero]
  exact ⟨q 0, fun x => is_const_of_fderiv_eq_zero (hq.differentiable one_ne_zero) hfzero x 0⟩

end OMA.PlanarLiouville

namespace OMA.DeGiorgiTwo

open EuclideanGeometry InnerProductSpace MeasureTheory Set

theorem hyperplanes_of_constant_quotient (u : ℝ² → ℝ)
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

end OMA.DeGiorgiTwo

section

open EuclideanGeometry

theorem OMA.solution : type_of% @DeGiorgi.DeGiorgi_two := by
  intro u ⟨hu, hup⟩
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
  obtain ⟨C, hC⟩ := OMA.DeGiorgiBound.solution u hu
  have hbounded : ∃ C : ℝ, ∀ x, |v x * q x| ≤ C :=
    ⟨C, fun x => hmul x ▸ hC x⟩
  obtain ⟨c, hc⟩ := OMA.PlanarLiouville.constant_of_weak_divergence v q hvC hqC hv hbounded
    (OMA.DeGiorgiWeak.solution u hu hup)
  refine OMA.DeGiorgiTwo.hyperplanes_of_constant_quotient u hud hv c fun x => ?_
  exact (div_eq_iff (hv x).ne').mp (hc x)

end
