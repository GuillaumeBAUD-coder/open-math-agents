import OMAReductions.R_DeGiorgi_DeGiorgi_two_R1
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# A gradient bound from a bound on the function and its Laplacian

Use a concave quadratic modulus of continuity and maximize the difference of
the function at two points minus that modulus. Move the points oppositely
along their separation and together in the orthogonal direction. The summed
second derivative inequalities are incompatible with a bounded Laplacian.
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

theorem OMA.solution : OMA.R_DeGiorgi_DeGiorgi_two_R1.H1 :=
  OMA.DeGiorgiBound.solution
