import OMAStatements.S_arxiv_2609_13765
import Mathlib

namespace OMA.P_arxiv_2609_13765

open OMA.S_arxiv_2609_13765

/-! ### Part 1: Smooth-convex interpolation `Q(x, y) ≥ 0` and Moreau envelope -/

private lemma hasDerivAt_comp_line {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E}
    (hderiv : ∀ x : E, HasFDerivAt f (innerSL ℝ (g x)) x) (y v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (y + s • v)) (inner ℝ (g (y + t • v)) v) t := by
  have hline : HasDerivAt (fun s : ℝ => y + s • v) v t := by
    have h1 : HasDerivAt (fun s : ℝ => s • v) ((1 : ℝ) • v) t :=
      (hasDerivAt_id t).smul_const v
    simpa only [one_smul] using h1.const_add y
  have hcomp := (hderiv (y + t • v)).comp_hasDerivAt t hline
  exact hcomp

private lemma smooth_convex_subgrad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E} (h : IsSmoothConvex f g) (x y : E) :
    inner ℝ (g y) (x - y) ≤ f x - f y := by
  have hconv := h.1
  have hderiv := hasDerivAt_comp_line h.2.1 y (x - y) 0
  simp only [zero_smul, add_zero] at hderiv
  -- For all t ∈ (0, 1], (f(y + t(x - y)) - f(y)) / t ≤ f(x) - f(y)
  have hslope : ∀ t : ℝ, 0 < t → t ≤ 1 →
      (f (y + t • (x - y)) - f y) / t ≤ f x - f y := by
    intro t ht0 ht1
    have hcomb : y + t • (x - y) = (1 - t) • y + t • x := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [hcomb]
    have hle := hconv.2 (Set.mem_univ y) (Set.mem_univ x) (by linarith : 0 ≤ 1 - t) (le_of_lt ht0)
      (by ring : (1 - t) + t = 1)
    simp only [smul_eq_mul] at hle
    rw [div_le_iff₀ ht0]
    nlinarith
  have htend : Filter.Tendsto (fun t : ℝ => (f (y + t • (x - y)) - f y) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (inner ℝ (g y) (x - y))) := by
    have h1 := hderiv.tendsto_slope_zero_right
    simpa only [zero_add, zero_smul, add_zero, smul_eq_mul, inv_mul_eq_div] using h1
  have hev : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (f (y + t • (x - y)) - f y) / t ≤ f x - f y := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
    exact hslope t ht.1 (le_of_lt ht.2)
  exact le_of_tendsto htend hev

private lemma smooth_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E} (h : IsSmoothConvex f g) (y z : E) :
    f z ≤ f y + inner ℝ (g y) (z - y) + (1 / 2) * ‖z - y‖ ^ 2 := by
  set v : E := z - y
  have hcont_g : Continuous g := h.2.2.continuous
  have hcont_line : Continuous (fun t : ℝ => inner ℝ (g (y + t • v)) v) :=
    Continuous.inner (hcont_g.comp (continuous_const.add (continuous_id.smul continuous_const)))
      continuous_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_comp_line h.2.1 y v t) (hcont_line.intervalIntegrable 0 1)
  have h0 : y + (0 : ℝ) • v = y := by simp
  have h1 : y + (1 : ℝ) • v = z := by simp [v]
  rw [h0, h1] at hftc
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      inner ℝ (g (y + t • v)) v ≤ inner ℝ (g y) v + t * ‖v‖ ^ 2 := by
    intro t ht
    have hdiff : inner ℝ (g (y + t • v)) v - inner ℝ (g y) v =
        inner ℝ (g (y + t • v) - g y) v := by rw [inner_sub_left]
    have hcs : inner ℝ (g (y + t • v) - g y) v ≤ ‖g (y + t • v) - g y‖ * ‖v‖ :=
      real_inner_le_norm _ _
    have hlip : ‖g (y + t • v) - g y‖ ≤ ‖(y + t • v) - y‖ := by
      have hl := h.2.2.norm_sub_le (y + t • v) y
      simpa using hl
    have hnorm : ‖(y + t • v) - y‖ = t * ‖v‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
    rw [hnorm] at hlip
    nlinarith [norm_nonneg v]
  have hint_le :
      ∫ t in (0 : ℝ)..1, inner ℝ (g (y + t • v)) v ≤
      ∫ t in (0 : ℝ)..1, (inner ℝ (g y) v + t * ‖v‖ ^ 2) := by
    apply intervalIntegral.integral_mono_on (by norm_num) (hcont_line.intervalIntegrable 0 1)
      ((continuous_const.add (continuous_id.mul continuous_const)).intervalIntegrable 0 1)
    exact hbound
  have hrhs : ∫ t in (0 : ℝ)..1, (inner ℝ (g y) v + t * ‖v‖ ^ 2) =
      inner ℝ (g y) v + (1 / 2) * ‖v‖ ^ 2 := by
    have hcont2 : Continuous (fun t : ℝ => t * ‖v‖ ^ 2) := continuous_id.mul continuous_const
    rw [intervalIntegral.integral_add intervalIntegrable_const (hcont2.intervalIntegrable 0 1)]
    rw [intervalIntegral.integral_const, intervalIntegral.integral_mul_const]
    have hid : ∫ t in (0 : ℝ)..1, t = (1 : ℝ) / 2 := by
      have := integral_id (a := (0 : ℝ)) (b := 1)
      norm_num at this ⊢
    rw [hid]
    simp [smul_eq_mul]
  linarith

private lemma smooth_convex_Q {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E} (h : IsSmoothConvex f g) (x y : E) :
    0 ≤ 2 * (f x - f y) - 2 * inner ℝ (g y) (x - y) - ‖g x - g y‖ ^ 2 := by
  let fh : E → ℝ := fun z => f z - inner ℝ (g y) z
  let gh : E → E := fun z => g z - g y
  have hfh : IsSmoothConvex fh gh := by
    refine ⟨⟨convex_univ, fun u _ v _ a b ha hb hab => ?_⟩, ?_, ?_⟩
    · dsimp only [fh]
      have hcf := h.1.2 (Set.mem_univ u) (Set.mem_univ v) ha hb hab
      simp only [smul_eq_mul] at hcf ⊢
      rw [inner_add_right, inner_smul_right, inner_smul_right]
      linarith
    · intro z
      have h1 := h.2.1 z
      have h2 : HasFDerivAt (fun w : E => inner ℝ (g y) w) (innerSL ℝ (g y)) z :=
        (innerSL ℝ (g y)).hasFDerivAt
      have hsub := h1.sub h2
      have hlin : innerSL ℝ (g z) - innerSL ℝ (g y) = innerSL ℝ (g z - g y) := by
        ext w; simp
      rwa [hlin] at hsub
    · refine LipschitzWith.of_dist_le_mul (fun u v => ?_)
      simp only [gh, dist_eq_norm, sub_sub_sub_cancel_right, NNReal.coe_one, one_mul]
      simpa using h.2.2.norm_sub_le u v
  have hmin : ∀ z : E, fh y ≤ fh z := by
    intro z
    have hsg := smooth_convex_subgrad hfh z y
    have hgy : gh y = 0 := sub_self _
    rw [hgy, inner_zero_left] at hsg
    linarith
  have hstep := smooth_descent hfh x (x - gh x)
  have hle := hmin (x - gh x)
  have hsubx : x - gh x - x = -gh x := by abel
  rw [hsubx, inner_neg_right, norm_neg, real_inner_self_eq_norm_sq] at hstep
  have hdiff : fh x - fh y = f x - f y - inner ℝ (g y) (x - y) := by
    dsimp only [fh]
    rw [inner_sub_right]
    ring
  dsimp only [gh] at hstep
  linarith

/-! ### Part 2: Proximal subgradient, Moreau envelope smoothness, and Theorem 1 -/

private lemma prox_subgrad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → ℝ} {lam : ℝ} {x z : E}
    (hF : ConvexOn ℝ Set.univ F) (hlam : 0 < lam) (hp : IsProx F lam x z) (w : E) :
    inner ℝ (x - z) (w - z) ≤ lam * (F w - F z) := by
  have hstep : ∀ t : ℝ, 0 < t → t ≤ 1 →
      inner ℝ (x - z) (w - z) - (t / 2) * ‖w - z‖ ^ 2 ≤ lam * (F w - F z) := by
    intro t ht0 ht1
    set y : E := (1 - t) • z + t • w
    have hconv := hF.2 (Set.mem_univ z) (Set.mem_univ w) (by linarith : 0 ≤ 1 - t) (le_of_lt ht0)
      (by ring : (1 - t) + t = 1)
    simp only [smul_eq_mul] at hconv
    have hpy := hp y
    have hy_sub : y - x = (z - x) + t • (w - z) := by
      dsimp only [y]; rw [smul_sub, sub_smul, one_smul]; abel
    have hnorm_sq : ‖y - x‖ ^ 2 =
        ‖z - x‖ ^ 2 + 2 * t * inner ℝ (z - x) (w - z) + t ^ 2 * ‖w - z‖ ^ 2 := by
      rw [hy_sub, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_of_nonneg (le_of_lt ht0)]
      ring
    have hinner_neg : inner ℝ (z - x) (w - z) = -inner ℝ (x - z) (w - z) := by
      rw [← inner_neg_left, neg_sub]
    rw [hnorm_sq, hinner_neg] at hpy
    have hmul : 2 * lam * (F z + (1 / (2 * lam)) * ‖z - x‖ ^ 2) ≤
        2 * lam * (F y + (1 / (2 * lam)) *
          (‖z - x‖ ^ 2 + 2 * t * -inner ℝ (x - z) (w - z) + t ^ 2 * ‖w - z‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hpy (by positivity)
    have h2lam : 2 * lam ≠ 0 := by positivity
    have hcancel : 2 * lam * (1 / (2 * lam)) = 1 := by field_simp
    have hmul' : 2 * lam * F z + ‖z - x‖ ^ 2 ≤
        2 * lam * F y + (‖z - x‖ ^ 2 + 2 * t * -inner ℝ (x - z) (w - z) + t ^ 2 * ‖w - z‖ ^ 2) := by
      rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, hcancel, one_mul, one_mul] at hmul
      exact hmul
    have hsimp : 2 * t * inner ℝ (x - z) (w - z) - t ^ 2 * ‖w - z‖ ^ 2 ≤ 2 * lam * (F y - F z) := by
      linarith
    have hFy : F y - F z ≤ t * (F w - F z) := by
      change F y ≤ (1 - t) * F z + t * F w at hconv
      linarith
    have hdiv : 2 * t * (inner ℝ (x - z) (w - z) - (t / 2) * ‖w - z‖ ^ 2) ≤
        2 * t * (lam * (F w - F z)) := by nlinarith
    have h2t : 0 < 2 * t := by positivity
    exact le_of_mul_le_mul_left hdiv h2t
  by_contra hlt
  push Not at hlt
  set d : ℝ := inner ℝ (x - z) (w - z) - lam * (F w - F z)
  have hd : 0 < d := by linarith
  set t : ℝ := min 1 (d / (‖w - z‖ ^ 2 + 1))
  have ht0 : 0 < t := lt_min (by norm_num) (div_pos hd (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ d / (‖w - z‖ ^ 2 + 1) := min_le_right _ _
  have hcontra := hstep t ht0 ht1
  have hmul : t * (‖w - z‖ ^ 2 + 1) ≤ d := (le_div_iff₀ (by positivity)).mp ht2
  nlinarith [norm_nonneg (w - z)]

/-- Uniqueness of the proximal point for a convex function `F` and `λ > 0`. -/
private lemma prox_unique {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → ℝ} {lam : ℝ} {x z1 z2 : E}
    (hF : ConvexOn ℝ Set.univ F) (hlam : 0 < lam)
    (hp1 : IsProx F lam x z1) (hp2 : IsProx F lam x z2) : z1 = z2 := by
  have h1 := prox_subgrad hF hlam hp1 z2
  have h2 := prox_subgrad hF hlam hp2 z1
  have hsum : inner ℝ (z2 - z1) (z2 - z1) ≤ 0 := by
    have hrew : inner ℝ (x - z1) (z2 - z1) + inner ℝ (x - z2) (z1 - z2) =
        inner ℝ (z2 - z1) (z2 - z1) := by
      have hneg : z1 - z2 = -(z2 - z1) := by abel
      rw [hneg, inner_neg_right, ← sub_eq_add_neg, ← inner_sub_left]
      congr 1; abel
    linarith
  rw [real_inner_self_eq_norm_sq] at hsum
  have hnorm : ‖z2 - z1‖ = 0 := by nlinarith [norm_nonneg (z2 - z1)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm

/-- For a convex function `F`, if `prox_{λ F}(x)` exists everywhere, then the scaled
Moreau envelope `φ(x) = λ F(z(x)) + (1/2) ‖x - z(x)‖^2` is convex and `1`-smooth with
gradient `g(x) = x - z(x)`. -/
private lemma moreau_Q {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → ℝ} {lam : ℝ} {x1 z1 x2 z2 : E}
    (hF : ConvexOn ℝ Set.univ F) (hlam : 0 < lam)
    (hp2 : IsProx F lam x2 z2) :
    let phi1 := lam * F z1 + (1 / 2) * ‖x1 - z1‖ ^ 2
    let phi2 := lam * F z2 + (1 / 2) * ‖x2 - z2‖ ^ 2
    let g1 := x1 - z1
    let g2 := x2 - z2
    0 ≤ 2 * (phi1 - phi2) - 2 * inner ℝ g2 (x1 - x2) - ‖g1 - g2‖ ^ 2 := by
  intro phi1 phi2 g1 g2
  have hsg := prox_subgrad hF hlam hp2 z1
  have hsplit : x1 - x2 = (z1 - z2) + (g1 - g2) := by simp only [g1, g2]; abel
  have hnorm : ‖g1 - g2‖ ^ 2 = ‖g1‖ ^ 2 - 2 * inner ℝ g2 g1 + ‖g2‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm]
  have hinner : inner ℝ g2 (x1 - x2) =
      inner ℝ g2 (z1 - z2) + inner ℝ g2 g1 - ‖g2‖ ^ 2 := by
    rw [hsplit, inner_add_right, inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq]
    ring
  dsimp only [phi1, phi2]
  change 0 ≤ 2 * (lam * F z1 + 1 / 2 * ‖g1‖ ^ 2 - (lam * F z2 + 1 / 2 * ‖g2‖ ^ 2)) -
    2 * inner ℝ g2 (x1 - x2) - ‖g1 - g2‖ ^ 2
  rw [hinner, hnorm]
  dsimp only [g2] at hsg ⊢
  linarith

/-- Any pair `(φ, g)` satisfying `Q(x, y) ≥ 0` everywhere is `IsSmoothConvex φ g`. -/
private lemma isSmoothConvex_of_Q {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {phi : E → ℝ} {g : E → E}
    (hQ : ∀ x y : E, 0 ≤ 2 * (phi x - phi y) - 2 * inner ℝ (g y) (x - y) - ‖g x - g y‖ ^ 2) :
    IsSmoothConvex phi g := by
  have hlip : LipschitzWith 1 g := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    simp only [dist_eq_norm, NNReal.coe_one, one_mul]
    have h1 := hQ x y
    have h2 := hQ y x
    have hneg : y - x = -(x - y) := by abel
    have hnorm_sym : ‖g y - g x‖ = ‖g x - g y‖ := norm_sub_rev _ _
    rw [hneg, inner_neg_right, hnorm_sym] at h2
    have hsum : ‖g x - g y‖ ^ 2 ≤ inner ℝ (g x - g y) (x - y) := by
      rw [inner_sub_left]; linarith
    have hcs : inner ℝ (g x - g y) (x - y) ≤ ‖g x - g y‖ * ‖x - y‖ := real_inner_le_norm _ _
    nlinarith [norm_nonneg (g x - g y), norm_nonneg (x - y)]
  have hconv : ConvexOn ℝ Set.univ phi := by
    refine ⟨convex_univ, fun u _ v _ a b ha hb hab => ?_⟩
    set w : E := a • u + b • v
    have h1 := hQ u w
    have h2 := hQ v w
    have h1' : inner ℝ (g w) (u - w) ≤ phi u - phi w := by nlinarith [norm_nonneg (g u - g w)]
    have h2' : inner ℝ (g w) (v - w) ≤ phi v - phi w := by nlinarith [norm_nonneg (g v - g w)]
    have hzero : a • (u - w) + b • (v - w) = 0 := by
      rw [smul_sub, smul_sub]
      calc a • u - a • w + (b • v - b • w)
          = (a • u + b • v) - (a • w + b • w) := by abel
        _ = w - (a + b) • w := by rw [add_smul]
        _ = w - (1 : ℝ) • w := by rw [hab]
        _ = 0 := by simp
    have hlin : a * inner ℝ (g w) (u - w) + b * inner ℝ (g w) (v - w) = 0 := by
      calc a * inner ℝ (g w) (u - w) + b * inner ℝ (g w) (v - w)
          = inner ℝ (g w) (a • (u - w) + b • (v - w)) := by
            rw [inner_add_right, inner_smul_right, inner_smul_right]
        _ = 0 := by rw [hzero, inner_zero_right]
    simp only [smul_eq_mul]
    change phi w ≤ a * phi u + b * phi v
    have h1a : a * inner ℝ (g w) (u - w) ≤ a * (phi u - phi w) :=
      mul_le_mul_of_nonneg_left h1' ha
    have h2b : b * inner ℝ (g w) (v - w) ≤ b * (phi v - phi w) :=
      mul_le_mul_of_nonneg_left h2' hb
    have hw_comb : a * phi w + b * phi w = phi w := by rw [← add_mul, hab, one_mul]
    linarith
  have hderiv : ∀ x : E, HasFDerivAt phi (innerSL ℝ (g x)) x := by
    intro x
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [Metric.ball_mem_nhds (0 : E) hc] with v hv
    rw [mem_ball_zero_iff] at hv
    simp only [innerSL_apply_apply, Real.norm_eq_abs]
    have h1 := hQ (x + v) x
    have h2 := hQ x (x + v)
    simp only [add_sub_cancel_left] at h1
    have hsub : x - (x + v) = -v := by abel
    rw [hsub, inner_neg_right] at h2
    have hlo : 0 ≤ phi (x + v) - phi x - inner ℝ (g x) v := by
      nlinarith [norm_nonneg (g (x + v) - g x)]
    have hhi : phi (x + v) - phi x - inner ℝ (g x) v ≤ inner ℝ (g (x + v) - g x) v := by
      rw [inner_sub_left]
      nlinarith [norm_nonneg (g x - g (x + v))]
    have hcs : inner ℝ (g (x + v) - g x) v ≤ ‖g (x + v) - g x‖ * ‖v‖ := real_inner_le_norm _ _
    have hl : ‖g (x + v) - g x‖ ≤ ‖v‖ := by
      simpa using hlip.norm_sub_le (x + v) x
    have hbound : phi (x + v) - phi x - inner ℝ (g x) v ≤ ‖v‖ * ‖v‖ := by
      nlinarith [norm_nonneg v]
    rw [abs_of_nonneg hlo]
    nlinarith [norm_nonneg v]
  exact ⟨hconv, hderiv, hlip⟩

/-- Wait: in a general (possibly incomplete) inner product space `E`, `prox_{λ F}(x)` is only
assumed to exist along the trajectory `x_0, ..., x_N`, NOT necessarily at every point `y ∈ E`!
HOWEVER, wait: we can construct the finite-data Moreau envelope on `E` directly via the
infimal convolution `F_λ(y) = inf_w { F(w) + (1/(2λ)) ‖w - y‖^2 }`? No — in an incomplete inner
product space `E`, the infimum might not be attained off the trajectory!
EVEN BETTER: restrict `F` to the FINITE-DIMENSIONAL subspace `W = span {x_star, x_0, ..., x_N, z_0, ..., z_N}`!
On a finite-dimensional real inner product space `W`, EVERY continuous convex function with a
minimizer has a UNIQUE global minimizer of `F(w) + (1/(2λ)) ‖w - y‖^2` on `W` (Wait: convexity on
finite-dimensional space implies continuity AND coercivity of `F(w) + (1/(2λ)) ‖w - y‖^2` since
`F(w) ≥ F(x_star)`, so `IsCompact.exists_isMinOn` proves `∀ y ∈ W, ∃ z ∈ W, IsProx (F|_W) lam y z`!!).
AND since `x_0, ..., x_N, z_0, ..., z_N, x_star ∈ W`, the trajectory is IDENTICAL in `W`!!
Let's prove `exists_prox_finiteDim` right now! -/
private lemma exists_prox_finiteDim {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] {F : W → ℝ} {lam : ℝ} {x_star : W}
    (hF : ConvexOn ℝ Set.univ F) (hmin : ∀ y : W, F x_star ≤ F y) (hlam : 0 < lam)
    (y : W) : ∃ z : W, IsProx F lam y z := by
  have hcontF : Continuous F :=
    continuousOn_univ.mp (by simpa using hF.continuousOn_interior)
  set J : W → ℝ := fun w => F w + (1 / (2 * lam)) * ‖w - y‖ ^ 2
  have hcontJ : Continuous J :=
    hcontF.add (continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2))
  -- Any minimizer must lie in the closed ball around y of radius R where
  -- (1/(2*lam)) * R^2 > J y - F x_star
  set R : ℝ := Real.sqrt (2 * lam * (F y - F x_star) + 1) + 1
  have hR_pos : 0 < R := by positivity
  have hcomp : IsCompact (Metric.closedBall y R) := isCompact_closedBall y R
  have hne : (Metric.closedBall y R).Nonempty := ⟨y, Metric.mem_closedBall_self (le_of_lt hR_pos)⟩
  obtain ⟨z, hz_mem, hz_min⟩ := hcomp.exists_isMinOn hne hcontJ.continuousOn
  refine ⟨z, fun w => ?_⟩
  by_cases hw : w ∈ Metric.closedBall y R
  · exact hz_min hw
  · rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hw
    have hzy : J z ≤ J y := hz_min (Metric.mem_closedBall_self (le_of_lt hR_pos))
    have hJy : J y = F y := by simp [J]
    have hmin_w := hmin w
    have hmin_y := hmin y
    have hRsq : 2 * lam * (F y - F x_star) + 1 ≤ R ^ 2 := by
      have h1 : Real.sqrt (2 * lam * (F y - F x_star) + 1) ≤ R := by linarith
      have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      rwa [Real.sq_sqrt (by nlinarith)] at h2
    have hwsq : R ^ 2 < ‖w - y‖ ^ 2 := by nlinarith [norm_nonneg (w - y)]
    have h2lam : 0 < 2 * lam := by positivity
    have hJw : F y < J w := by
      dsimp only [J]
      have hmul : 2 * lam * (F y - F x_star) < ‖w - y‖ ^ 2 := by linarith
      have hdiv : F y - F x_star < (1 / (2 * lam)) * ‖w - y‖ ^ 2 := by
        rw [one_div, inv_mul_eq_div, lt_div_iff₀ h2lam]; linarith
      linarith
    exact le_trans hzy (by linarith)

/-- Theorem 1 (upper bound): for any positive `s`-composable schedule `h` with rate `η`,
any `λ > 0`, any inner product space `E`, any convex `F : E → ℝ` with minimizer `x_*`,
and any relaxed proximal trajectory `(x, z)` along `h`,
`F (z h.length) - F x_* ≤ η ‖x 0 - x_*‖^2 / (4 λ)`. -/
private lemma theorem1_upper {h : List ℝ} {eta lam : ℝ}
    (hs : IsSComposable h eta) (hlam : 0 < lam)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → ℝ) (x_star : E) (x z : ℕ → E)
    (hF : ConvexOn ℝ Set.univ F) (hmin : ∀ y : E, F x_star ≤ F y)
    (htraj : IsProxTrajectory F lam h x z) :
    F (z h.length) - F x_star ≤ eta * ‖x 0 - x_star‖ ^ 2 / (4 * lam) := by
  -- Restrict to the finite-dimensional span W of {x_star} ∪ {x k | k ≤ N} ∪ {z k | k ≤ N}
  classical
  set N : ℕ := h.length
  let pts : Finset E :=
    insert x_star ((Finset.range (N + 1)).image x ∪ (Finset.range (N + 1)).image z)
  let W : Submodule ℝ E := Submodule.span ℝ (pts : Set E)
  have : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ pts.finite_toSet
  have hx_mem : ∀ k ≤ N, x k ∈ W := fun k hk =>
    Submodule.subset_span (Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩)))
  have hz_mem : ∀ k ≤ N, z k ∈ W := fun k hk =>
    Submodule.subset_span (Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩)))
  have hxs_mem : x_star ∈ W := Submodule.subset_span (Finset.mem_insert_self _ _)
  let FW : W → ℝ := fun w => F w.val
  have hFW : ConvexOn ℝ Set.univ FW := by
    refine ⟨convex_univ, fun u _ v _ a b ha hb hab => ?_⟩
    exact hF.2 (Set.mem_univ u.val) (Set.mem_univ v.val) ha hb hab
  have hminW : ∀ w : W, FW ⟨x_star, hxs_mem⟩ ≤ FW w := fun w => hmin w.val
  -- Choose prox_W(w) for every w : W
  choose zW hzW using fun w : W => exists_prox_finiteDim hFW hminW hlam w
  let phi : W → ℝ := fun w => lam * FW (zW w) + (1 / 2) * ‖w - zW w‖ ^ 2
  let g : W → W := fun w => w - zW w
  have hsmooth : IsSmoothConvex phi g :=
    isSmoothConvex_of_Q (fun u v => moreau_Q hFW hlam (hzW v))
  have hxsW : (⟨x_star, hxs_mem⟩ : W) = zW ⟨x_star, hxs_mem⟩ := by
    have hpxs : IsProx FW lam ⟨x_star, hxs_mem⟩ ⟨x_star, hxs_mem⟩ := by
      intro w
      have h1 := hminW w
      have hnn : 0 ≤ (1 / (2 * lam)) * ‖w - ⟨x_star, hxs_mem⟩‖ ^ 2 := by positivity
      simp only [sub_self, norm_zero, sq, mul_zero, add_zero]
      linarith
    exact prox_unique hFW hlam hpxs (hzW ⟨x_star, hxs_mem⟩)
  have hmin_phi : ∀ w : W, phi ⟨x_star, hxs_mem⟩ ≤ phi w := by
    intro w
    dsimp only [phi]
    rw [← hxsW]
    simp only [sub_self, norm_zero, sq, mul_zero, add_zero]
    have h1 := hminW (zW w)
    have h2 : 0 ≤ (1 / 2 : ℝ) * ‖w - zW w‖ ^ 2 := by positivity
    nlinarith
  -- Trajectory inside W
  let xW : ℕ → W := fun k => if hk : k ≤ N then ⟨x k, hx_mem k hk⟩ else 0
  have hzW_eq : ∀ k (hk : k ≤ N), zW (xW k) = ⟨z k, hz_mem k hk⟩ := by
    intro k hk
    have hpk : IsProx FW lam (xW k) ⟨z k, hz_mem k hk⟩ := by
      intro w
      have hsub1 : ‖(⟨z k, hz_mem k hk⟩ : W) - xW k‖ = ‖z k - x k‖ := by
        simp only [xW, dif_pos hk]; rfl
      have hsub2 : ‖w - xW k‖ = ‖w.val - x k‖ := by
        simp only [xW, dif_pos hk]; rfl
      rw [hsub1, hsub2]
      exact htraj.1 k hk w.val
    exact prox_unique hFW hlam (hzW (xW k)) hpk
  have hgd : IsGDTrajectory g h xW := by
    intro k hk
    have hkN : k ≤ N := le_of_lt hk
    have hk1N : k + 1 ≤ N := hk
    have hzk : zW (xW k) = ⟨z k, hz_mem k hkN⟩ := hzW_eq k hkN
    ext
    dsimp only [g]
    rw [hzk]
    simp only [xW, dif_pos hkN, dif_pos hk1N]
    change x (k + 1) = x k - h[k] • (x k - z k)
    rw [htraj.2 k hk]
    rw [← neg_sub (z k) (x k), smul_neg, sub_neg_eq_add]
  have hpot := hs.2.2.2 W phi g ⟨x_star, hxs_mem⟩ xW hsmooth hmin_phi hgd
  -- Extract the proximal bound from hpot!
  have hS_nn : 0 ≤ h.sum := List.sum_nonneg (fun s hs' => le_of_lt (hs.1 s hs'))
  have h1S_pos : 0 < 1 + h.sum := by linarith
  have heta_eq : eta = (1 + h.sum)⁻¹ := hs.2.1
  have heta_pos : 0 < eta := by rw [heta_eq]; positivity
  have heta_le1 : eta ≤ 1 := by
    rw [heta_eq]; exact inv_le_one_of_one_le₀ (by linarith)
  set S : ℝ := h.sum
  have hS_eta : S = (1 - eta) / eta := by
    rw [heta_eq]; field_simp; ring
  have hS1_eta : S + 1 = eta⁻¹ := by
    rw [heta_eq, inv_inv]; ring
  set eW : W := xW N - ⟨z N, hz_mem N (le_refl N)⟩
  set R : ℝ := ‖x 0 - x_star‖
  set Delta : ℝ := F (z N) - F x_star
  have hgN : g (xW N) = eW := by
    simp only [g, eW, hzW_eq N (le_refl N)]
  have hphiN : phi (xW N) - phi ⟨x_star, hxs_mem⟩ = lam * Delta + (1 / 2) * ‖eW‖ ^ 2 := by
    dsimp only [phi]
    rw [hzW_eq N (le_refl N), ← hxsW]
    simp only [sub_self, norm_zero, sq, mul_zero, add_zero, FW, Delta, eW, xW, dif_pos (le_refl N)]
    ring
  have hx0_norm : ‖xW 0 - ⟨x_star, hxs_mem⟩‖ = R := by
    simp only [xW, dif_pos (Nat.zero_le N), R]
    rfl
  rw [hgN, hphiN, hx0_norm] at hpot
  -- Multiply hpot by 2 / eta^2
  have hdiv :
      ‖xW N - ⟨x_star, hxs_mem⟩‖ ^ 2 + S * (S + 2) * ‖eW‖ ^ 2 + 2 * S * lam * Delta ≤ R ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hpot (show 0 ≤ 2 / eta ^ 2 by positivity)
    have h1 : (2 / eta ^ 2) * ((1 - eta) / 2) = S * (S + 1) := by
      rw [hS_eta]; field_simp; ring
    have h2 : (2 / eta ^ 2) * (eta ^ 2 / 2) = 1 := by field_simp
    have h3 : (2 / eta ^ 2) * (eta * (1 - eta)) = 2 * S := by
      rw [hS_eta]; field_simp
    have hlhs :
        (2 / eta ^ 2) * (((1 - eta) / 2) * ‖eW‖ ^ 2 + (eta ^ 2 / 2) * ‖xW N - ⟨x_star, hxs_mem⟩‖ ^ 2 +
          eta * (1 - eta) * (lam * Delta + 1 / 2 * ‖eW‖ ^ 2)) =
        ‖xW N - ⟨x_star, hxs_mem⟩‖ ^ 2 + S * (S + 2) * ‖eW‖ ^ 2 + 2 * S * lam * Delta := by
      calc (2 / eta ^ 2) * (((1 - eta) / 2) * ‖eW‖ ^ 2 +
              (eta ^ 2 / 2) * ‖xW N - ⟨x_star, hxs_mem⟩‖ ^ 2 +
              eta * (1 - eta) * (lam * Delta + 1 / 2 * ‖eW‖ ^ 2))
          = ((2 / eta ^ 2) * ((1 - eta) / 2)) * ‖eW‖ ^ 2 +
            ((2 / eta ^ 2) * (eta ^ 2 / 2)) * ‖xW N - ⟨x_star, hxs_mem⟩‖ ^ 2 +
            ((2 / eta ^ 2) * (eta * (1 - eta))) * (lam * Delta + 1 / 2 * ‖eW‖ ^ 2) := by ring
        _ = (S * (S + 1)) * ‖eW‖ ^ 2 + 1 * ‖xW N - ⟨x_star, hxs_mem⟩‖ ^ 2 +
            (2 * S) * (lam * Delta + 1 / 2 * ‖eW‖ ^ 2) := by rw [h1, h2, h3]
        _ = ‖xW N - ⟨x_star, hxs_mem⟩‖ ^ 2 + S * (S + 2) * ‖eW‖ ^ 2 + 2 * S * lam * Delta := by ring
    have hrhs : (2 / eta ^ 2) * ((eta ^ 2 / 2) * R ^ 2) = R ^ 2 := by field_simp
    linarith
  -- Subgradient inequality: ⟪eW, zN - x*⟫ ≥ lam * Delta
  have hsg := prox_subgrad hF hlam (htraj.1 N (le_refl N)) x_star
  have hsgW : lam * Delta ≤ inner ℝ eW (⟨z N, hz_mem N (le_refl N)⟩ - ⟨x_star, hxs_mem⟩) := by
    have hneg : inner ℝ (x N - z N) (x_star - z N) = -inner ℝ (x N - z N) (z N - x_star) := by
      rw [← inner_neg_right, neg_sub]
    have hinner_eq : inner ℝ eW (⟨z N, hz_mem N (le_refl N)⟩ - ⟨x_star, hxs_mem⟩) =
        inner ℝ (x N - z N) (z N - x_star) := by
      simp only [eW, xW, dif_pos (le_refl N)]; rfl
    rw [hinner_eq]
    dsimp only [Delta]
    linarith
  -- Algebraic completion of the square without dividing by ‖eW‖!
  -- Multiply hdiv by ‖eW‖^2 and use Cauchy-Schwarz:
  -- ‖xW N - x*‖^2 * ‖eW‖^2 ≥ ⟪eW, xW N - x*⟫^2 = (⟪eW, zN - x*⟫ + ‖eW‖^2)^2 ≥ (lam * Delta + ‖eW‖^2)^2!
  have hDelta_nn : 0 ≤ Delta := by dsimp only [Delta]; linarith [hmin (z N)]
  have hCS : (lam * Delta + ‖eW‖ ^ 2) ^ 2 ≤ ‖xW N - ⟨x_star, hxs_mem⟩‖ ^ 2 * ‖eW‖ ^ 2 := by
    have hdecomp : xW N - ⟨x_star, hxs_mem⟩ = (⟨z N, hz_mem N (le_refl N)⟩ - ⟨x_star, hxs_mem⟩) + eW := by
      dsimp only [eW]; abel
    have hge : lam * Delta + ‖eW‖ ^ 2 ≤ inner ℝ eW (xW N - ⟨x_star, hxs_mem⟩) := by
      rw [hdecomp, inner_add_right, real_inner_self_eq_norm_sq]
      linarith
    have hcs1 := real_inner_le_norm eW (xW N - ⟨x_star, hxs_mem⟩)
    have hnn : 0 ≤ lam * Delta + ‖eW‖ ^ 2 := by positivity
    have hsq := pow_le_pow_left₀ hnn (hge.trans hcs1) 2
    nlinarith [norm_nonneg eW, norm_nonneg (xW N - ⟨x_star, hxs_mem⟩)]
  -- Now: (lam * Delta + (S + 1) * ‖eW‖^2)^2 ≤ R^2 * ‖eW‖^2!
  -- Wait: check that identity!
  -- (lam * Delta + (S + 1) * ‖eW‖^2)^2 = (lam * Delta + ‖eW‖^2)^2 + 2 * S * lam * Delta * ‖eW‖^2 + S * (S + 2) * ‖eW‖^4
  -- ≤ (‖xW N - x*‖^2 + 2 * S * lam * Delta + S * (S + 2) * ‖eW‖^2) * ‖eW‖^2 ≤ R^2 * ‖eW‖^2!!
  have hkey : (lam * Delta + (S + 1) * ‖eW‖ ^ 2) ^ 2 ≤ (R * ‖eW‖) ^ 2 := by
    have hexp : (lam * Delta + (S + 1) * ‖eW‖ ^ 2) ^ 2 =
        (lam * Delta + ‖eW‖ ^ 2) ^ 2 +
        (2 * S * lam * Delta + S * (S + 2) * ‖eW‖ ^ 2) * ‖eW‖ ^ 2 := by ring
    have hmul := mul_le_mul_of_nonneg_right hdiv (sq_nonneg ‖eW‖)
    have hrhs : R ^ 2 * ‖eW‖ ^ 2 = (R * ‖eW‖) ^ 2 := by ring
    linarith
  have hlin : lam * Delta + (S + 1) * ‖eW‖ ^ 2 ≤ R * ‖eW‖ := by
    have h1 : 0 ≤ lam * Delta + (S + 1) * ‖eW‖ ^ 2 := by positivity
    have h2 : 0 ≤ R * ‖eW‖ := by positivity
    nlinarith only [hkey, h1, h2]
  -- By AM-GM / square: 4 * (S + 1) * (lam * Delta) ≤ R^2!
  have hamgm : 4 * (S + 1) * (lam * Delta) ≤ R ^ 2 := by
    have hS1_pos : 0 < S + 1 := by linarith only [h1S_pos]
    have hmul4 : 4 * (S + 1) * (lam * Delta + (S + 1) * ‖eW‖ ^ 2) ≤ 4 * (S + 1) * (R * ‖eW‖) :=
      mul_le_mul_of_nonneg_left hlin (by linarith only [hS1_pos])
    nlinarith only [hmul4, sq_nonneg (2 * (S + 1) * ‖eW‖ - R)]
  -- Divide by 4 * lam * (S + 1) = 4 * lam / eta
  have hfinal : Delta ≤ eta * R ^ 2 / (4 * lam) := by
    rw [le_div_iff₀ (by positivity : 0 < 4 * lam)]
    have hmul : (S + 1) * (Delta * (4 * lam)) ≤ (S + 1) * (eta * R ^ 2) := by
      have hS1e : (S + 1) * eta = 1 := by rw [hS1_eta, inv_mul_cancel₀ (ne_of_gt heta_pos)]
      calc (S + 1) * (Delta * (4 * lam)) = 4 * (S + 1) * (lam * Delta) := by ring
        _ ≤ R ^ 2 := hamgm
        _ = ((S + 1) * eta) * R ^ 2 := by rw [hS1e, one_mul]
        _ = (S + 1) * (eta * R ^ 2) := by ring
    exact le_of_mul_le_mul_left hmul (by linarith)
  exact hfinal

/-- Theorem 1 (tightness): explicit 1D instance `F(t) = a |t|` attaining exact equality. -/
private lemma theorem1_tight {h : List ℝ} {eta lam R : ℝ}
    (hs : IsSComposable h eta) (hlam : 0 < lam) (hR : 0 < R) :
    ∃ (F : ℝ → ℝ) (x_star : ℝ) (x z : ℕ → ℝ),
      ConvexOn ℝ Set.univ F ∧
      (∀ y : ℝ, F x_star ≤ F y) ∧
      IsProxTrajectory F lam h x z ∧
      ‖x 0 - x_star‖ = R ∧
      F (z h.length) - F x_star = eta * R ^ 2 / (4 * lam) := by
  have hS_nn : 0 ≤ h.sum := List.sum_nonneg (fun s hs' => le_of_lt (hs.1 s hs'))
  have h1S_pos : 0 < 1 + h.sum := by linarith
  have heta_eq : eta = (1 + h.sum)⁻¹ := hs.2.1
  have heta_pos : 0 < eta := by rw [heta_eq]; positivity
  set S : ℝ := h.sum
  set a : ℝ := R / (2 * lam * (S + 1))
  have ha_pos : 0 < a := by positivity
  let F : ℝ → ℝ := fun t => a * |t|
  let T : ℕ → ℝ := fun k => (h.take k).sum
  let x : ℕ → ℝ := fun k => R - lam * a * T k
  let z : ℕ → ℝ := fun k => x k - lam * a
  have hconv : ConvexOn ℝ Set.univ F := by
    refine ⟨convex_univ, fun u _ v _ c d hc hd _ => ?_⟩
    dsimp only [F]; simp only [smul_eq_mul]
    have htri : |c * u + d * v| ≤ c * |u| + d * |v| := by
      calc |c * u + d * v| ≤ |c * u| + |d * v| := abs_add_le _ _
        _ = |c| * |u| + |d| * |v| := by rw [abs_mul, abs_mul]
        _ = c * |u| + d * |v| := by rw [abs_of_nonneg hc, abs_of_nonneg hd]
    nlinarith
  have hmin : ∀ y : ℝ, F 0 ≤ F y := by
    intro y; dsimp only [F]; simp only [abs_zero, mul_zero]; positivity
  have hT_le : ∀ k : ℕ, T k ≤ S := by
    intro k
    dsimp only [T, S]
    have hsplit : h = h.take k ++ h.drop k := (List.take_append_drop k h).symm
    have hsum : h.sum = (h.take k).sum + (h.drop k).sum := by
      conv_lhs => rw [hsplit]
      exact List.sum_append
    have hdrop_nn : 0 ≤ (h.drop k).sum :=
      List.sum_nonneg (fun s hs' => le_of_lt (hs.1 s (List.mem_of_mem_drop hs')))
    linarith
  have hz_pos : ∀ k : ℕ, 0 ≤ z k := by
    intro k
    dsimp only [z, x]
    have hTk := hT_le k
    have hprod : lam * a * (S + 1) = R / 2 := by
      dsimp only [a]; field_simp
    have hle : lam * a * (T k + 1) ≤ lam * a * (S + 1) := by nlinarith
    linarith
  have hprox : ∀ k : ℕ, k ≤ h.length → IsProx F lam (x k) (z k) := by
    intro k _ y
    dsimp only [F]
    have hzk := hz_pos k
    rw [abs_of_nonneg hzk]
    have hy : y ≤ |y| := le_abs_self y
    have hnorm1 : ‖z k - x k‖ ^ 2 = (lam * a) ^ 2 := by
      dsimp only [z]; simp [Real.norm_eq_abs, mul_pow, sq_abs]
    have hnorm2 : ‖y - x k‖ ^ 2 = (y - x k) ^ 2 := by simp [Real.norm_eq_abs]
    rw [hnorm1, hnorm2]
    have h2lam : 0 < 2 * lam := by positivity
    -- Goal: a * (x k - lam * a) + 1/(2*lam) * (lam * a)^2 ≤ a * |y| + 1/(2*lam) * (y - x k)^2
    have hsq : 0 ≤ (y - (x k - lam * a)) ^ 2 := sq_nonneg _
    have hid : a * (x k - lam * a) + (1 / (2 * lam)) * (lam * a) ^ 2 +
        (1 / (2 * lam)) * (y - (x k - lam * a)) ^ 2 =
        a * y + (1 / (2 * lam)) * (y - x k) ^ 2 := by
      field_simp; ring
    have hge : a * y ≤ a * |y| := by nlinarith
    dsimp only [z]
    nlinarith [mul_nonneg (show 0 ≤ 1 / (2 * lam) by positivity) hsq]
  have hstep : ∀ (k : ℕ) (hk : k < h.length), x (k + 1) = x k + h[k] • (z k - x k) := by
    intro k hk
    dsimp only [x, z, T]
    rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.sum_append,
      List.sum_singleton]
    simp only [smul_eq_mul]
    ring
  have hx0 : ‖x 0 - 0‖ = R := by
    dsimp only [x, T]; simp [Real.norm_eq_abs, abs_of_pos hR]
  have hval : F (z h.length) - F 0 = eta * R ^ 2 / (4 * lam) := by
    dsimp only [F, z, x, T]
    rw [List.take_length]
    have hprod : lam * a * (S + 1) = R / 2 := by
      dsimp only [a]; field_simp
    have hzN : R - lam * a * S - lam * a = R / 2 := by linarith
    change a * |R - lam * a * S - lam * a| - a * |0| = _
    rw [hzN, abs_of_pos (by positivity : 0 < R / 2), abs_zero, mul_zero, sub_zero]
    rw [heta_eq]
    dsimp only [a, S]
    field_simp
    ring
  exact ⟨F, 0, x, z, hconv, hmin, ⟨hprox, hstep⟩, hx0, hval⟩

/-! ### Part 3: Self-contained proof that `silverSchedule m` is `s`-composable -/

private lemma silverRatio_pos : 0 < silverRatio := by
  unfold silverRatio; positivity

private lemma silverRatio_sq : silverRatio ^ 2 = 2 * silverRatio + 1 := by
  unfold silverRatio
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma silverRatio_mul_conj : silverRatio * (Real.sqrt 2 - 1) = 1 := by
  unfold silverRatio
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma silverSchedule_len (m : ℕ) : (silverSchedule m).length = 2 ^ m - 1 := by
  induction m with
  | zero => simp [silverSchedule]
  | succ m ih =>
    simp only [silverSchedule, List.length_append, List.length_singleton, ih]
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
    have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    omega

private lemma silverSchedule_pos (m : ℕ) : ∀ s ∈ silverSchedule m, 0 < s := by
  induction m with
  | zero => intro s hs; simp [silverSchedule] at hs
  | succ m ih =>
    intro s hs
    simp only [silverSchedule, List.mem_append, List.mem_singleton] at hs
    rcases hs with (hs | rfl) | hs
    · exact ih s hs
    · have h1 : 0 < Real.sqrt 2 - 1 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
      have h2 : 0 < silverRatio ^ m := pow_pos silverRatio_pos m
      nlinarith
    · exact ih s hs

private lemma silverSchedule_sum (m : ℕ) : 1 + (silverSchedule m).sum = silverRatio ^ m := by
  induction m with
  | zero => simp [silverSchedule]
  | succ m ih =>
    simp only [silverSchedule, List.sum_append, List.sum_singleton]
    have hmul : silverRatio ^ m * (Real.sqrt 2 - 1) * silverRatio = silverRatio ^ m := by
      calc silverRatio ^ m * (Real.sqrt 2 - 1) * silverRatio
          = silverRatio ^ m * (silverRatio * (Real.sqrt 2 - 1)) := by ring
        _ = silverRatio ^ m := by rw [silverRatio_mul_conj, mul_one]
    have hstep : 2 * silverRatio ^ m + silverRatio ^ m * (Real.sqrt 2 - 1) =
        silverRatio ^ (m + 1) := by
      have h1 : (2 * silverRatio ^ m + silverRatio ^ m * (Real.sqrt 2 - 1)) * silverRatio =
          silverRatio ^ (m + 1) * silverRatio := by
        calc (2 * silverRatio ^ m + silverRatio ^ m * (Real.sqrt 2 - 1)) * silverRatio
            = 2 * silverRatio ^ m * silverRatio +
                silverRatio ^ m * (Real.sqrt 2 - 1) * silverRatio := by ring
          _ = 2 * silverRatio ^ m * silverRatio + silverRatio ^ m := by rw [hmul]
          _ = silverRatio ^ m * (2 * silverRatio + 1) := by ring
          _ = silverRatio ^ m * silverRatio ^ 2 := by rw [silverRatio_sq]
          _ = silverRatio ^ (m + 1) * silverRatio := by ring
      exact mul_right_cancel₀ (ne_of_gt silverRatio_pos) h1
    linarith

private lemma silverSchedule_prod (m : ℕ) :
    ((silverSchedule m).map (fun s => s - 1)).prod = (silverRatio ^ m)⁻¹ := by
  induction m with
  | zero => simp [silverSchedule]
  | succ m ih =>
    simp only [silverSchedule, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one, ih]
    have hsub : 1 + silverRatio ^ m * (Real.sqrt 2 - 1) - 1 =
        silverRatio ^ m * (Real.sqrt 2 - 1) := by ring
    rw [hsub]
    have hne : silverRatio ^ m ≠ 0 := pow_ne_zero m (ne_of_gt silverRatio_pos)
    have hconj : Real.sqrt 2 - 1 = silverRatio⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      exact silverRatio_mul_conj
    rw [hconj, pow_succ, mul_inv]
    field_simp

/-- The history functional `H(h, η; f, g, x)` from Proposition 6 of Grimmer–Shu–Wang (2025)
/ Lemma 2 of arXiv:2609.13765. -/
private noncomputable def histExpr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h : List ℝ) (eta : ℝ) (f : E → ℝ) (g : E → E) (x : ℕ → E) : ℝ :=
  (∑ i : Fin h.length, h[i.val] *
    (2 * (f (x i.val) - f (x h.length)) + ‖g (x i.val)‖ ^ 2 +
      2 * inner ℝ (g (x i.val)) (x 0 - x i.val))) -
  ‖x h.length - x 0‖ ^ 2 - ((1 - eta) / eta ^ 2) * ‖g (x h.length)‖ ^ 2

private lemma gd_telescope {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : E → E} {h : List ℝ} {x : ℕ → E} (hgd : IsGDTrajectory g h x) :
    x 0 - x h.length = ∑ i : Fin h.length, h[i.val] • g (x i.val) := by
  have hgen : ∀ k ≤ h.length, x 0 - x k =
      ∑ i ∈ Finset.range k, (h.getD i 0) • g (x i) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih (by omega)]
      have hlt : k < h.length := by omega
      have hget : h.getD k 0 = h[k] := by simp [List.getD_eq_getElem?_getD, hlt]
      rw [hget, hgd k hlt]
      abel
  rw [hgen h.length (le_refl _), ← Fin.sum_univ_eq_sum_range (fun i => (h.getD i 0) • g (x i)) h.length]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [List.getD_eq_getElem?_getD, i.isLt]

private lemma histExpr_implies_potential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {h : List ℝ} {eta : ℝ} {f : E → ℝ} {g : E → E} {x_star : E} {x : ℕ → E}
    (hpos : ∀ s ∈ h, 0 < s) (heta_eq : eta = (1 + h.sum)⁻¹)
    (hsmooth : IsSmoothConvex f g) (hmin : ∀ y : E, f x_star ≤ f y)
    (hgd : IsGDTrajectory g h x) (hhist : 0 ≤ histExpr h eta f g x) :
    ((1 - eta) / 2) * ‖g (x h.length)‖ ^ 2 +
      (eta ^ 2 / 2) * ‖x h.length - x_star‖ ^ 2 +
      eta * (1 - eta) * (f (x h.length) - f x_star) ≤
      (eta ^ 2 / 2) * ‖x 0 - x_star‖ ^ 2 := by
  -- Lemma 2 of arXiv:2609.13765: add ∑ h_i Q_{*, i} ≥ 0 to histExpr!
  have hgstar : g x_star = 0 := by
    have h1 := smooth_convex_subgrad hsmooth (x_star - g x_star) x_star
    have h2 := hmin (x_star - g x_star)
    have h3 : x_star - g x_star - x_star = -g x_star := by abel
    -- Better: use smooth_descent at x_star with z = x_star - g x_star!
    have hd := smooth_descent hsmooth x_star (x_star - g x_star)
    rw [h3, inner_neg_right, norm_neg, real_inner_self_eq_norm_sq] at hd
    have h0 : ‖g x_star‖ ^ 2 ≤ 0 := by linarith
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (g x_star)])
  have hQ_sum : 0 ≤ ∑ i : Fin h.length, h[i.val] *
      (2 * (f x_star - f (x i.val)) - 2 * inner ℝ (g (x i.val)) (x_star - x i.val) -
        ‖g (x i.val)‖ ^ 2) := by
    refine Finset.sum_nonneg (fun i _ => ?_)
    have hi_pos : 0 < h[i.val] := hpos h[i.val] (List.getElem_mem i.isLt)
    have hQ := smooth_convex_Q hsmooth x_star (x i.val)
    rw [hgstar, zero_sub, norm_neg] at hQ
    exact mul_nonneg (le_of_lt hi_pos) hQ
  have hsum_h : (∑ i : Fin h.length, h[i.val]) = (1 - eta) / eta := by
    have h1 : (∑ i : Fin h.length, h[i.val]) = h.sum := by
      rw [← List.sum_ofFn]
      congr 1
      exact List.ofFn_getElem
    have hSn : 0 ≤ h.sum := List.sum_nonneg (fun s hs' => le_of_lt (hpos s hs'))
    have h1S : 0 < 1 + h.sum := by linarith
    rw [h1, heta_eq]; field_simp; ring
  have htel := gd_telescope hgd
  have hcombine :
      histExpr h eta f g x +
      (∑ i : Fin h.length, h[i.val] *
        (2 * (f x_star - f (x i.val)) - 2 * inner ℝ (g (x i.val)) (x_star - x i.val) -
          ‖g (x i.val)‖ ^ 2)) =
      (2 * (1 - eta) / eta) * (f x_star - f (x h.length)) +
      ‖x 0 - x_star‖ ^ 2 - ‖x h.length - x_star‖ ^ 2 -
      ((1 - eta) / eta ^ 2) * ‖g (x h.length)‖ ^ 2 := by
    unfold histExpr
    have hinner_add :
        (∑ i : Fin h.length, h[i.val] *
          (2 * (f (x i.val) - f (x h.length)) + ‖g (x i.val)‖ ^ 2 +
            2 * inner ℝ (g (x i.val)) (x 0 - x i.val))) +
        (∑ i : Fin h.length, h[i.val] *
          (2 * (f x_star - f (x i.val)) - 2 * inner ℝ (g (x i.val)) (x_star - x i.val) -
            ‖g (x i.val)‖ ^ 2)) =
        (∑ i : Fin h.length, h[i.val] * (2 * (f x_star - f (x h.length)))) +
        2 * inner ℝ (∑ i : Fin h.length, h[i.val] • g (x i.val)) (x 0 - x_star) := by
      rw [← Finset.sum_add_distrib, sum_inner, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [inner_smul_left]
      simp only [conj_trivial]
      have hinner_id : inner ℝ (g (x i.val)) (x 0 - x_star) =
          inner ℝ (g (x i.val)) (x 0 - x i.val) - inner ℝ (g (x i.val)) (x_star - x i.val) := by
        rw [← inner_sub_right]; congr 1; abel
      rw [hinner_id]
      ring
    rw [← htel] at hinner_add
    have hconst : (∑ i : Fin h.length, h[i.val] * (2 * (f x_star - f (x h.length)))) =
        (2 * (1 - eta) / eta) * (f x_star - f (x h.length)) := by
      rw [← Finset.sum_mul, hsum_h]; ring
    have hnorm_id : 2 * inner ℝ (x 0 - x h.length) (x 0 - x_star) - ‖x h.length - x 0‖ ^ 2 =
        ‖x 0 - x_star‖ ^ 2 - ‖x h.length - x_star‖ ^ 2 := by
      set u : E := x 0 - x_star
      set v : E := x 0 - x h.length
      have h1 : x h.length - x_star = u - v := by dsimp only [u, v]; abel
      have h2 : x h.length - x 0 = -v := by dsimp only [v]; abel
      rw [h1, h2, norm_neg, norm_sub_sq_real u v, real_inner_comm v u]
      ring
    linarith
  have htot : 0 ≤ (2 * (1 - eta) / eta) * (f x_star - f (x h.length)) +
      ‖x 0 - x_star‖ ^ 2 - ‖x h.length - x_star‖ ^ 2 -
      ((1 - eta) / eta ^ 2) * ‖g (x h.length)‖ ^ 2 := by linarith
  have hSn : 0 ≤ h.sum := List.sum_nonneg (fun s hs' => le_of_lt (hpos s hs'))
  have heta_pos : 0 < eta := by rw [heta_eq]; positivity
  have hmul := mul_le_mul_of_nonneg_left htot (show 0 ≤ eta ^ 2 / 2 by positivity)
  have h1 : (eta ^ 2 / 2) * (2 * (1 - eta) / eta) = eta * (1 - eta) := by field_simp
  have h2 : (eta ^ 2 / 2) * ((1 - eta) / eta ^ 2) = (1 - eta) / 2 := by field_simp
  have hdist : (eta ^ 2 / 2) * ((2 * (1 - eta) / eta) * (f x_star - f (x h.length)) +
      ‖x 0 - x_star‖ ^ 2 - ‖x h.length - x_star‖ ^ 2 -
      ((1 - eta) / eta ^ 2) * ‖g (x h.length)‖ ^ 2) =
      eta * (1 - eta) * (f x_star - f (x h.length)) +
      (eta ^ 2 / 2) * ‖x 0 - x_star‖ ^ 2 - (eta ^ 2 / 2) * ‖x h.length - x_star‖ ^ 2 -
      ((1 - eta) / 2) * ‖g (x h.length)‖ ^ 2 := by
    calc _ = ((eta ^ 2 / 2) * (2 * (1 - eta) / eta)) * (f x_star - f (x h.length)) +
             (eta ^ 2 / 2) * ‖x 0 - x_star‖ ^ 2 - (eta ^ 2 / 2) * ‖x h.length - x_star‖ ^ 2 -
             ((eta ^ 2 / 2) * ((1 - eta) / eta ^ 2)) * ‖g (x h.length)‖ ^ 2 := by ring
      _ = _ := by rw [h1, h2]
  linarith

private lemma silver_alg_identity (a rho fx fy n0 n1s n2 n3 i01 i02 i03 i12 i13 i23 s1 s2 : ℝ)
    (ha : a ≠ 0) (hrho : rho ≠ 0) (hrho_sq : rho ^ 2 = 2 * rho + 1) :
    s1 + (1 + (a * rho)⁻¹) * (2 * (fx - fy) + n1s - 2 * i01) + s2 - n2 -
      (1 - a * rho⁻¹) / (a * rho⁻¹) ^ 2 * n3 =
    s1 + 2 * (1 - a) / a * (fy - fx) - n0 - (1 - a) / a ^ 2 * n1s +
      (1 + 2 * rho) *
        (s2 + (n0 - 2 * (1 + (a * rho)⁻¹) * i01 + (1 + (a * rho)⁻¹) ^ 2 * n1s) - n2 -
          (1 - a) / a ^ 2 * n3) +
      rho *
        (-2 * s2 + 2 * (1 - a) / a * (fx - fy) -
          2 * (n0 - (1 + (a * rho)⁻¹) * i01 - i02) -
          2 * (i02 - (1 + (a * rho)⁻¹) * i12 - n2) - (1 - a) / a * n1s +
          2 * (i01 - (1 + (a * rho)⁻¹) * n1s - i12) - (1 - a) / a * n3 +
          2 * (i03 - (1 + (a * rho)⁻¹) * i13 - i23)) +
      rho *
        (2 * (1 + (a * rho)⁻¹ - 2) * (fy - fx) - 2 * (i03 - i23) - (n1s - 2 * i13 + n3) +
          (1 + (a * rho)⁻¹ - 1) * (-2 * (i12 - i01) - (n1s - 2 * i13 + n3))) := by
  have hpoly : rho ^ 2 - 2 * rho - 1 = 0 := by linarith
  field_simp
  linear_combination
    (-2 * a * rho * (fx - fy) + (a * rho + 1) * n1s - rho ^ 2 * n3) * hpoly

/-- Symmetric `s`-join induction step for the silver schedule (`σ = ρ = 1 + √2`):
exact zero-remainder identity! -/
private lemma silver_histExpr_nonneg (m : ℕ) :
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (f : E → ℝ) (g : E → E) (x : ℕ → E),
      IsSmoothConvex f g →
      IsGDTrajectory g (silverSchedule m) x →
      0 ≤ histExpr (silverSchedule m) (silverRatio ^ m)⁻¹ f g x := by
  induction m with
  | zero =>
    intro E _ _ f g x _ _
    simp [histExpr, silverSchedule]
    exact le_refl 0
  | succ m ih =>
    intro E _ _ f g x hsmooth hgd
    set h1 : List ℝ := silverSchedule m
    set a : ℝ := (silverRatio ^ m)⁻¹
    set rho : ℝ := silverRatio
    set mu : ℝ := 1 + silverRatio ^ m * (Real.sqrt 2 - 1)
    set eta : ℝ := (silverRatio ^ (m + 1))⁻¹
    set n1 : ℕ := h1.length
    set h : List ℝ := h1 ++ [mu] ++ h1
    change IsGDTrajectory g h x at hgd
    change 0 ≤ histExpr h eta f g x
    have hlen : h.length = 2 * n1 + 1 := by
      simp only [h, n1, List.length_append, List.length_singleton]; omega
    have ha_pos : 0 < a := inv_pos.mpr (pow_pos silverRatio_pos m)
    have hrho_pos : 0 < rho := silverRatio_pos
    have hconj : Real.sqrt 2 - 1 = rho⁻¹ := by
      apply eq_inv_of_mul_eq_one_right; exact silverRatio_mul_conj
    have hmu_eq : mu = 1 + (a * rho)⁻¹ := by
      dsimp only [mu, a, rho]
      rw [hconj]
      have h1' : silverRatio ^ m ≠ 0 := pow_ne_zero m (ne_of_gt silverRatio_pos)
      have h2' : silverRatio ≠ 0 := ne_of_gt silverRatio_pos
      change 1 + silverRatio ^ m * silverRatio⁻¹ = 1 + ((silverRatio ^ m)⁻¹ * silverRatio)⁻¹
      field_simp
    have heta_eq : eta = a * rho⁻¹ := by
      dsimp only [eta, a, rho]; rw [pow_succ, mul_inv]
    have hrho_sq : rho ^ 2 = 2 * rho + 1 := silverRatio_sq
    have hsum1 : (∑ i : Fin n1, h1[i.val]) = (1 - a) / a := by
      have h1s : (∑ i : Fin n1, h1[i.val]) = h1.sum := by
        rw [← List.sum_ofFn]; congr 1; exact List.ofFn_getElem
      have hs := silverSchedule_sum m
      have hne : silverRatio ^ m ≠ 0 := pow_ne_zero m (ne_of_gt silverRatio_pos)
      have hratio : (1 - a) / a = silverRatio ^ m - 1 := by
        dsimp only [a]; field_simp
      rw [h1s, hratio]; dsimp only [h1]; linarith
    -- Sub-trajectories: first block x_0..x_{n1}, middle step x_{n1+1} = x_{n1} - mu * g(x_{n1}),
    -- second block y_k = x_{n1 + 1 + k} for k = 0..n1
    have hgd1 : IsGDTrajectory g h1 x := by
      intro k hk
      have hk' : k < h.length := by rw [hlen]; omega
      have hget : h[k]'hk' = h1[k]'hk := by
        simp only [h, List.append_assoc]
        rw [List.getElem_append_left hk]
      simpa only [hget] using hgd k hk'
    have hmid : x (n1 + 1) = x n1 - mu • g (x n1) := by
      have hk' : n1 < h.length := by rw [hlen]; omega
      have hget : h[n1]'hk' = mu := by
        simp only [h, List.append_assoc]
        rw [List.getElem_append_right (le_refl n1)]
        simp [n1]
      simpa only [hget] using hgd n1 hk'
    let y : ℕ → E := fun k => x (n1 + 1 + k)
    have hgd2 : IsGDTrajectory g h1 y := by
      intro k hk
      have hk' : n1 + 1 + k < h.length := by rw [hlen]; omega
      have hget : h[n1 + 1 + k]'hk' = h1[k]'hk := by
        simp only [h, List.append_assoc]
        rw [List.getElem_append_right (by omega : h1.length ≤ n1 + 1 + k)]
        have hsub : n1 + 1 + k - h1.length = k + 1 := by dsimp [n1]; omega
        simp only [hsub, List.cons_append, List.nil_append, List.getElem_cons_succ]
      have hstep := hgd (n1 + 1 + k) hk'
      rw [hget] at hstep
      simpa only [y, Nat.add_assoc] using hstep
    -- Nonnegative ingredients:
    have hP1 : 0 ≤ histExpr h1 a f g x := ih f g x hsmooth hgd1
    have hP2 : 0 ≤ histExpr h1 a f g y := ih f g y hsmooth hgd2
    have hP3 : 0 ≤ ∑ i : Fin n1, h1[i.val] *
        ((2 * (f (x n1) - f (y i.val)) - 2 * inner ℝ (g (y i.val)) (x n1 - y i.val) -
          ‖g (x n1) - g (y i.val)‖ ^ 2) +
         (2 * (f (y n1) - f (y i.val)) - 2 * inner ℝ (g (y i.val)) (y n1 - y i.val) -
          ‖g (y n1) - g (y i.val)‖ ^ 2)) := by
      refine Finset.sum_nonneg (fun i _ => mul_nonneg (le_of_lt (silverSchedule_pos m _ (List.getElem_mem i.isLt)))
        (add_nonneg (smooth_convex_Q hsmooth (x n1) (y i.val))
          (smooth_convex_Q hsmooth (y n1) (y i.val))))
    have hmu1_nn : 0 ≤ mu - 1 := by
      dsimp only [mu]
      have h1' : 0 < Real.sqrt 2 - 1 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
      have h2' : 0 < silverRatio ^ m := pow_pos silverRatio_pos m
      nlinarith
    have hP4 : 0 ≤
        (2 * (f (x n1) - f (y n1)) - 2 * inner ℝ (g (y n1)) (x n1 - y n1) -
          ‖g (x n1) - g (y n1)‖ ^ 2) +
        (mu - 1) * (2 * (f (y n1) - f (x n1)) - 2 * inner ℝ (g (x n1)) (y n1 - x n1) -
          ‖g (y n1) - g (x n1)‖ ^ 2) :=
      add_nonneg (smooth_convex_Q hsmooth (x n1) (y n1))
        (mul_nonneg hmu1_nn (smooth_convex_Q hsmooth (y n1) (x n1)))
    -- Abbreviations for the 4 vectors Δ₀, Δ₁, Δ₂, Δ₃ and the two block sums S1, S2
    set d0 : E := x n1 - x 0
    set d1 : E := g (x n1)
    set d2 : E := y n1 - x 0
    set d3 : E := g (y n1)
    have hx_end : x h.length = y n1 := by
      dsimp only [y]; congr 1; rw [hlen]; omega
    have htel2 : y 0 - y n1 = ∑ i : Fin n1, h1[i.val] • g (y i.val) := gd_telescope hgd2
    have hy0_eq : y 0 - x 0 = d0 - mu • d1 := by
      dsimp only [y, d0, d1]; rw [Nat.add_zero, hmid]; abel
    have hSb : y 0 - y n1 = d0 - mu • d1 - d2 := by
      have : y 0 - y n1 = (y 0 - x 0) - (y n1 - x 0) := by abel
      rw [this, hy0_eq]
    -- Split the sum in `histExpr h eta f g x` into block 1, middle index `n1`, and block 2
    let term (j : ℕ) (val : ℝ) : ℝ :=
      val * (2 * (f (x j) - f (y n1)) + ‖g (x j)‖ ^ 2 + 2 * inner ℝ (g (x j)) (x 0 - x j))
    have hsum_split :
        (∑ i : Fin h.length, h[i.val] *
          (2 * (f (x i.val) - f (x h.length)) + ‖g (x i.val)‖ ^ 2 +
            2 * inner ℝ (g (x i.val)) (x 0 - x i.val))) =
        (∑ i : Fin n1, term i.val h1[i.val]) +
        term n1 mu +
        (∑ i : Fin n1, term (n1 + 1 + i.val) h1[i.val]) := by
      simp_rw [hx_end]
      have hcast : ∀ (l1 l2 : List ℝ) (F : ℕ → ℝ → ℝ),
          (∑ i : Fin (l1 ++ l2).length, F i.val ((l1 ++ l2)[i.val])) =
          (∑ i : Fin l1.length, F i.val l1[i.val]) +
          (∑ i : Fin l2.length, F (l1.length + i.val) l2[i.val]) := by
        intro l1 l2 F
        have h1 : (∑ i : Fin (l1 ++ l2).length, F i.val ((l1 ++ l2)[i.val])) =
            ∑ i ∈ Finset.range (l1 ++ l2).length, F i ((l1 ++ l2).getD i 0) := by
          rw [← Fin.sum_univ_eq_sum_range]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt, Option.getD_some]
        have h2 : (∑ i : Fin l1.length, F i.val l1[i.val]) =
            ∑ i ∈ Finset.range l1.length, F i (l1.getD i 0) := by
          rw [← Fin.sum_univ_eq_sum_range]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt, Option.getD_some]
        have h3 : (∑ i : Fin l2.length, F (l1.length + i.val) l2[i.val]) =
            ∑ i ∈ Finset.range l2.length, F (l1.length + i) (l2.getD i 0) := by
          rw [← Fin.sum_univ_eq_sum_range]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt, Option.getD_some]
        rw [h1, h2, h3, List.length_append, Finset.sum_range_add]
        congr 1
        · refine Finset.sum_congr rfl (fun j hj => ?_)
          have hlt : j < l1.length := Finset.mem_range.mp hj
          have hlt' : j < (l1 ++ l2).length := by rw [List.length_append]; omega
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hlt', List.getElem?_eq_getElem hlt,
            Option.getD_some, Option.getD_some, List.getElem_append_left hlt]
        · refine Finset.sum_congr rfl (fun j hj => ?_)
          have hlt : j < l2.length := Finset.mem_range.mp hj
          have hlt' : l1.length + j < (l1 ++ l2).length := by rw [List.length_append]; omega
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hlt', List.getElem?_eq_getElem hlt,
            Option.getD_some, Option.getD_some,
            List.getElem_append_right (Nat.le_add_right l1.length j)]
          simp only [Nat.add_sub_cancel_left]
      -- Apply hcast twice to h = (h1 ++ [mu]) ++ h1
      have h12 := hcast (h1 ++ [mu]) h1 term
      have h1m := hcast h1 [mu] term
      change (∑ i : Fin ((h1 ++ [mu]) ++ h1).length, term i.val (((h1 ++ [mu]) ++ h1)[i.val])) = _
      rw [h12, h1m]
      simp only [List.length_append, List.length_singleton, Fin.sum_univ_one, Fin.val_zero,
        add_zero, List.getElem_singleton, n1]
    -- Express the sums in hP1, hP2, hP3 in terms of the two block sums S1, S2 and Δ₀..Δ₃
    set S1 : ℝ := ∑ i : Fin n1, term i.val h1[i.val]
    set S2 : ℝ := ∑ i : Fin n1, term (n1 + 1 + i.val) h1[i.val]
    have hP1_eq : histExpr h1 a f g x =
        S1 + (2 * (1 - a) / a) * (f (y n1) - f (x n1)) - ‖d0‖ ^ 2 -
        ((1 - a) / a ^ 2) * ‖d1‖ ^ 2 := by
      unfold histExpr
      have hdiff :
          (∑ i : Fin n1, h1[i.val] *
            (2 * (f (x i.val) - f (x n1)) + ‖g (x i.val)‖ ^ 2 +
              2 * inner ℝ (g (x i.val)) (x 0 - x i.val))) =
          S1 + (2 * (1 - a) / a) * (f (y n1) - f (x n1)) := by
        dsimp only [S1, term]
        have hrew : (2 * (1 - a) / a) * (f (y n1) - f (x n1)) =
            ∑ i : Fin n1, h1[i.val] * (2 * (f (y n1) - f (x n1))) := by
          rw [← Finset.sum_mul, hsum1]; ring
        rw [hrew, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => by ring)
      rw [hdiff]
    have hP2_eq : histExpr h1 a f g y =
        S2 + ‖d0 - mu • d1‖ ^ 2 - ‖d2‖ ^ 2 - ((1 - a) / a ^ 2) * ‖d3‖ ^ 2 := by
      unfold histExpr
      have hdiff :
          (∑ i : Fin n1, h1[i.val] *
            (2 * (f (y i.val) - f (y n1)) + ‖g (y i.val)‖ ^ 2 +
              2 * inner ℝ (g (y i.val)) (y 0 - y i.val))) =
          S2 + 2 * inner ℝ (y 0 - y n1) (y 0 - x 0) := by
        dsimp only [S2, term, y]
        rw [htel2, sum_inner, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [inner_smul_left]; simp only [conj_trivial]
        have hsub : y 0 - x (n1 + 1 + i.val) = (x 0 - x (n1 + 1 + i.val)) + (y 0 - x 0) := by abel
        rw [hsub, inner_add_right]
        ring
      have hnorm : 2 * inner ℝ (y 0 - y n1) (y 0 - x 0) - ‖y n1 - y 0‖ ^ 2 =
          ‖d0 - mu • d1‖ ^ 2 - ‖d2‖ ^ 2 := by
        set u : E := y 0 - x 0
        set v : E := y 0 - y n1
        have h1 : d2 = u - v := by dsimp only [d2, u, v]; abel
        have h2 : y n1 - y 0 = -v := by dsimp only [v]; abel
        have hu : u = d0 - mu • d1 := hy0_eq
        rw [h1, h2, norm_neg, norm_sub_sq_real u v, real_inner_comm v u, hu]
        ring
      linarith
    have hP3_eq :
        (∑ i : Fin n1, h1[i.val] *
          ((2 * (f (x n1) - f (y i.val)) - 2 * inner ℝ (g (y i.val)) (x n1 - y i.val) -
            ‖g (x n1) - g (y i.val)‖ ^ 2) +
           (2 * (f (y n1) - f (y i.val)) - 2 * inner ℝ (g (y i.val)) (y n1 - y i.val) -
            ‖g (y n1) - g (y i.val)‖ ^ 2))) =
        -2 * S2 + (2 * (1 - a) / a) * (f (x n1) - f (y n1)) -
        2 * inner ℝ (d0 - mu • d1 - d2) d0 - 2 * inner ℝ (d0 - mu • d1 - d2) d2 -
        ((1 - a) / a) * ‖d1‖ ^ 2 + 2 * inner ℝ d1 (d0 - mu • d1 - d2) -
        ((1 - a) / a) * ‖d3‖ ^ 2 + 2 * inner ℝ d3 (d0 - mu • d1 - d2) := by
      -- Expand each summand cleanly!
      have hterm_eq : ∀ i : Fin n1,
          h1[i.val] *
            ((2 * (f (x n1) - f (y i.val)) - 2 * inner ℝ (g (y i.val)) (x n1 - y i.val) -
              ‖g (x n1) - g (y i.val)‖ ^ 2) +
             (2 * (f (y n1) - f (y i.val)) - 2 * inner ℝ (g (y i.val)) (y n1 - y i.val) -
              ‖g (y n1) - g (y i.val)‖ ^ 2)) =
          -2 * term (n1 + 1 + i.val) h1[i.val] +
          h1[i.val] * (2 * (f (x n1) - f (y n1)) - ‖d1‖ ^ 2 - ‖d3‖ ^ 2) +
          (-2 * inner ℝ (h1[i.val] • g (y i.val)) d0 -
           2 * inner ℝ (h1[i.val] • g (y i.val)) d2 +
           2 * inner ℝ d1 (h1[i.val] • g (y i.val)) +
           2 * inner ℝ d3 (h1[i.val] • g (y i.val))) := by
        intro i
        dsimp only [term, y, d0, d1, d2, d3]
        rw [norm_sub_sq_real, norm_sub_sq_real]
        rw [inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right]
        simp only [conj_trivial]
        have hs1 : x n1 - x (n1 + 1 + i.val) = (x n1 - x 0) + (x 0 - x (n1 + 1 + i.val)) := by abel
        have hs2 : x (n1 + 1 + n1) - x (n1 + 1 + i.val) =
            (x (n1 + 1 + n1) - x 0) + (x 0 - x (n1 + 1 + i.val)) := by abel
        rw [hs1, hs2, inner_add_right, inner_add_right]
        ring
      simp_rw [hterm_eq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul, ← sum_inner, ← inner_sum, ← htel2, hSb, hsum1]
      ring
    have hP4_eq :
        (2 * (f (x n1) - f (y n1)) - 2 * inner ℝ (g (y n1)) (x n1 - y n1) -
          ‖g (x n1) - g (y n1)‖ ^ 2) +
        (mu - 1) * (2 * (f (y n1) - f (x n1)) - 2 * inner ℝ (g (x n1)) (y n1 - x n1) -
          ‖g (y n1) - g (x n1)‖ ^ 2) =
        2 * (mu - 2) * (f (y n1) - f (x n1)) -
        2 * inner ℝ d3 (d0 - d2) - ‖d1 - d3‖ ^ 2 +
        (mu - 1) * (-2 * inner ℝ d1 (d2 - d0) - ‖d3 - d1‖ ^ 2) := by
      have hs1 : x n1 - y n1 = d0 - d2 := by dsimp only [d0, d2]; abel
      have hs2 : y n1 - x n1 = d2 - d0 := by dsimp only [d0, d2]; abel
      rw [hs1, hs2]
      dsimp only [d1, d3]
      ring
    -- Now verify the EXACT identity:
    -- histExpr h eta f g x = 1 * hP1 + (1 + 2 * rho) * hP2 + rho * hP3 + rho * hP4!!
    have hident :
        histExpr h eta f g x =
        histExpr h1 a f g x + (1 + 2 * rho) * histExpr h1 a f g y +
        rho * (∑ i : Fin n1, h1[i.val] *
          ((2 * (f (x n1) - f (y i.val)) - 2 * inner ℝ (g (y i.val)) (x n1 - y i.val) -
            ‖g (x n1) - g (y i.val)‖ ^ 2) +
           (2 * (f (y n1) - f (y i.val)) - 2 * inner ℝ (g (y i.val)) (y n1 - y i.val) -
            ‖g (y n1) - g (y i.val)‖ ^ 2))) +
        rho * ((2 * (f (x n1) - f (y n1)) - 2 * inner ℝ (g (y n1)) (x n1 - y n1) -
          ‖g (x n1) - g (y n1)‖ ^ 2) +
          (mu - 1) * (2 * (f (y n1) - f (x n1)) - 2 * inner ℝ (g (x n1)) (y n1 - x n1) -
            ‖g (y n1) - g (x n1)‖ ^ 2)) := by
      rw [hP1_eq, hP2_eq, hP3_eq, hP4_eq]
      unfold histExpr
      rw [hsum_split, hx_end]
      change S1 + term n1 mu + S2 - ‖d2‖ ^ 2 - ((1 - eta) / eta ^ 2) * ‖d3‖ ^ 2 = _
      have hterm_mid : term n1 mu = mu * (2 * (f (x n1) - f (y n1)) + ‖d1‖ ^ 2 - 2 * inner ℝ d1 d0) := by
        dsimp only [term, d0, d1]
        have : x 0 - x n1 = -(x n1 - x 0) := by abel
        rw [this, inner_neg_right]; ring
      rw [hterm_mid]
      -- Expand all inner products and norms into the 10 scalar basis variables:
      -- ‖d0‖², ‖d1‖², ‖d2‖², ‖d3‖², ⟪d0,d1⟫, ⟪d0,d2⟫, ⟪d0,d3⟫, ⟪d1,d2⟫, ⟪d1,d3⟫, ⟪d2,d3⟫!
      have hn1 : ‖d0 - mu • d1‖ ^ 2 = ‖d0‖ ^ 2 - 2 * mu * inner ℝ d0 d1 + mu ^ 2 * ‖d1‖ ^ 2 := by
        rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]; ring
      have hn2 : ‖d1 - d3‖ ^ 2 = ‖d1‖ ^ 2 - 2 * inner ℝ d1 d3 + ‖d3‖ ^ 2 := norm_sub_sq_real d1 d3
      have hn3 : ‖d3 - d1‖ ^ 2 = ‖d1‖ ^ 2 - 2 * inner ℝ d1 d3 + ‖d3‖ ^ 2 := by
        rw [norm_sub_rev, hn2]
      have hi1 : inner ℝ (d0 - mu • d1 - d2) d0 = ‖d0‖ ^ 2 - mu * inner ℝ d0 d1 - inner ℝ d0 d2 := by
        rw [inner_sub_left, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq,
          real_inner_comm d1 d0, real_inner_comm d2 d0]; simp only [conj_trivial]
      have hi2 : inner ℝ (d0 - mu • d1 - d2) d2 = inner ℝ d0 d2 - mu * inner ℝ d1 d2 - ‖d2‖ ^ 2 := by
        rw [inner_sub_left, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq]
        simp only [conj_trivial]
      have hi3 : inner ℝ d1 (d0 - mu • d1 - d2) = inner ℝ d0 d1 - mu * ‖d1‖ ^ 2 - inner ℝ d1 d2 := by
        rw [inner_sub_right, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
          real_inner_comm d1 d0]
      have hi4 : inner ℝ d3 (d0 - mu • d1 - d2) = inner ℝ d0 d3 - mu * inner ℝ d1 d3 - inner ℝ d2 d3 := by
        rw [inner_sub_right, inner_sub_right, inner_smul_right,
          real_inner_comm d3 d0, real_inner_comm d3 d1, real_inner_comm d3 d2]
      have hi5 : inner ℝ d3 (d0 - d2) = inner ℝ d0 d3 - inner ℝ d2 d3 := by
        rw [inner_sub_right, real_inner_comm d3 d0, real_inner_comm d3 d2]
      have hi6 : inner ℝ d1 (d2 - d0) = inner ℝ d1 d2 - inner ℝ d0 d1 := by
        rw [inner_sub_right, real_inner_comm d1 d0]
      have hi7 : inner ℝ d1 d0 = inner ℝ d0 d1 := real_inner_comm d0 d1
      rw [hn1, hn2, hn3, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hmu_eq, heta_eq]
      exact silver_alg_identity a rho (f (x n1)) (f (y n1))
        (‖d0‖ ^ 2) (‖d1‖ ^ 2) (‖d2‖ ^ 2) (‖d3‖ ^ 2)
        (inner ℝ d0 d1) (inner ℝ d0 d2) (inner ℝ d0 d3)
        (inner ℝ d1 d2) (inner ℝ d1 d3) (inner ℝ d2 d3) S1 S2
        (ne_of_gt ha_pos) (ne_of_gt hrho_pos) hrho_sq
    rw [hident]
    exact add_nonneg (add_nonneg (add_nonneg hP1 (mul_nonneg (by linarith only [hrho_pos]) hP2))
      (mul_nonneg (le_of_lt hrho_pos) hP3)) (mul_nonneg (le_of_lt hrho_pos) hP4)

private lemma silverSchedule_isSComposable (m : ℕ) :
    IsSComposable (silverSchedule m) (silverRatio ^ m)⁻¹ := by
  refine ⟨silverSchedule_pos m, ?_, ?_, ?_⟩
  · rw [silverSchedule_sum m]
  · exact (silverSchedule_prod m).symm
  · intro E _ _ f g x_star x hsmooth hmin hgd
    exact histExpr_implies_potential (silverSchedule_pos m)
      (by rw [silverSchedule_sum m]) hsmooth hmin hgd
      (silver_histExpr_nonneg m f g x hsmooth hgd)

theorem main_proof :
    (∀ (h : List ℝ) (eta lam : ℝ),
      IsSComposable h eta → 0 < lam →
      (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        (F : E → ℝ) (x_star : E) (x z : ℕ → E),
        ConvexOn ℝ Set.univ F →
        (∀ y : E, F x_star ≤ F y) →
        IsProxTrajectory F lam h x z →
        F (z h.length) - F x_star ≤ eta * ‖x 0 - x_star‖ ^ 2 / (4 * lam)) ∧
      (∀ R : ℝ, 0 < R →
        ∃ (F : ℝ → ℝ) (x_star : ℝ) (x z : ℕ → ℝ),
          ConvexOn ℝ Set.univ F ∧
          (∀ y : ℝ, F x_star ≤ F y) ∧
          IsProxTrajectory F lam h x z ∧
          ‖x 0 - x_star‖ = R ∧
          F (z h.length) - F x_star = eta * R ^ 2 / (4 * lam))) ∧
    (∀ (m : ℕ) (lam : ℝ),
      1 ≤ m → 0 < lam →
      (silverSchedule m).length = 2 ^ m - 1 ∧
      IsSComposable (silverSchedule m) (silverRatio ^ m)⁻¹ ∧
      (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        (F : E → ℝ) (x_star : E) (x z : ℕ → E),
        ConvexOn ℝ Set.univ F →
        (∀ y : E, F x_star ≤ F y) →
        IsProxTrajectory F lam (silverSchedule m) x z →
        F (z (silverSchedule m).length) - F x_star ≤
          ‖x 0 - x_star‖ ^ 2 / (4 * lam * silverRatio ^ m)) ∧
      (∀ R : ℝ, 0 < R →
        ∃ (F : ℝ → ℝ) (x_star : ℝ) (x z : ℕ → ℝ),
          ConvexOn ℝ Set.univ F ∧
          (∀ y : ℝ, F x_star ≤ F y) ∧
          IsProxTrajectory F lam (silverSchedule m) x z ∧
          ‖x 0 - x_star‖ = R ∧
          F (z (silverSchedule m).length) - F x_star =
            R ^ 2 / (4 * lam * silverRatio ^ m))) := by
  constructor
  · intro h eta lam hs hlam
    exact ⟨fun E _ _ F x_star x z hF hmin htraj => theorem1_upper hs hlam F x_star x z hF hmin htraj,
           fun R hR => theorem1_tight hs hlam hR⟩
  · intro m lam _ hlam
    have hs := silverSchedule_isSComposable m
    refine ⟨silverSchedule_len m, hs, ?_, ?_⟩
    · intro E _ _ F x_star x z hF hmin htraj
      have hup := theorem1_upper hs hlam F x_star x z hF hmin htraj
      have hrew : (silverRatio ^ m)⁻¹ * ‖x 0 - x_star‖ ^ 2 / (4 * lam) =
          ‖x 0 - x_star‖ ^ 2 / (4 * lam * silverRatio ^ m) := by
        have hpos : silverRatio ^ m ≠ 0 := pow_ne_zero m (ne_of_gt silverRatio_pos)
        field_simp
      rwa [hrew] at hup
    · intro R hR
      obtain ⟨F, x_star, x, z, hF, hmin, htraj, hx0, hval⟩ := theorem1_tight hs hlam hR
      have hrew : (silverRatio ^ m)⁻¹ * R ^ 2 / (4 * lam) =
          R ^ 2 / (4 * lam * silverRatio ^ m) := by
        have hpos : silverRatio ^ m ≠ 0 := pow_ne_zero m (ne_of_gt silverRatio_pos)
        field_simp
      rw [hrew] at hval
      exact ⟨F, x_star, x, z, hF, hmin, htraj, hx0, hval⟩

end OMA.P_arxiv_2609_13765

theorem OMA.solution : type_of% @OMA.S_arxiv_2609_13765.main :=
  OMA.P_arxiv_2609_13765.main_proof
