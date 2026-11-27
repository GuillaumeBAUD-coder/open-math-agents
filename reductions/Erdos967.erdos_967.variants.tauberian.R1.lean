import FormalConjectures.ErdosProblems.«967»
/-! Wiener smoothing and the logarithmic character obstruction for the Erdős–Ingham criterion. -/
namespace OMA.R_Erdos967_erdos_967_variants_tauberian_R1
open Filter Set Real MeasureTheory Erdos967
open scoped Topology

/-- The Wiener implication for compact interval averages on the multiplicative scale. -/
def H1 : Prop := ∀ (a : ℕ → ℕ), StrictMono a → 1 < a 0 → Summable (fun k => 1 / (a k : ℝ)) →
  (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) →
  ∀ f : ℝ → ℝ, Monotone f → (∀ x, 0 ≤ f x) → (∀ x < 1, f x = 0) →
    (∀ x y : ℝ, BddAbove (f '' Icc x y)) →
    Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
      (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
    ∀ u v : ℝ, 0 < u → u < v →
      Tendsto (fun x : ℝ => ∫ y in u..v, f (x*y)/x) atTop (𝓝 ((v^2-u^2)/2))

/-- A spectral zero cancels the logarithmic cosine in the convolution.
The cutoff at one only affects a summable reciprocal tail. -/
def H2 : Prop := ∀ (a : ℕ → ℕ), StrictMono a → 1 < a 0 → Summable (fun k => 1 / (a k : ℝ)) →
  ∀ (t c : ℝ), 1 + (∑' k, summand t (a k)) = 0 →
    let f := fun x : ℝ => if 1 ≤ x then x*(1+c*cos (t*log x)) else 0
    Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
      (𝓝 (1 + ∑' k, 1 / (a k : ℝ)))

lemma unsmooth {f : ℝ → ℝ} (hm : Monotone f)
    (hav : ∀ u v : ℝ, 0 < u → u < v →
      Tendsto (fun x : ℝ => ∫ y in u..v, f (x*y)/x) atTop (𝓝 ((v^2-u^2)/2))) :
    Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let δ := min (ε/2) (1/2)
  have hd : 0 < δ := lt_min (by positivity) (by norm_num)
  have hde : δ ≤ ε/2 := min_le_left _ _
  have hdu : δ ≤ 1/2 := min_le_right _ _
  have hright := (hav 1 (1+δ) zero_lt_one (by linarith)).eventually_lt_const
      (show ((1+δ)^2-1^2)/2 < δ*(1+ε) by nlinarith [mul_pos hd (show 0 < ε-δ/2 by linarith)])
  have hleft := (hav (1-δ) 1 (by linarith) (by linarith)).eventually_const_lt
      (show δ*(1-ε) < (1^2-(1-δ)^2)/2 by nlinarith [mul_pos hd (show 0 < ε-δ/2 by linarith)])
  filter_upwards [hright,hleft,eventually_gt_atTop (0:ℝ)] with x hr hl hx
  have hmon : Monotone (fun y : ℝ => f (x*y)/x) := fun y z hyz =>
    div_le_div_of_nonneg_right (hm (mul_le_mul_of_nonneg_left hyz hx.le)) hx.le
  have left := intervalIntegral.integral_mono_on (show 1-δ ≤ 1 by linarith)
    (hmon.intervalIntegrable (μ := volume)) (intervalIntegrable_const (c := f x/x))
    (fun y hy => div_le_div_of_nonneg_right (hm (by nlinarith [mul_le_mul_of_nonneg_left hy.2 hx.le])) hx.le)
  have right := intervalIntegral.integral_mono_on (show 1 ≤ 1+δ by linarith)
    (intervalIntegrable_const (c := f x/x)) (hmon.intervalIntegrable (μ := volume))
    (fun y hy => div_le_div_of_nonneg_right (hm (by nlinarith [mul_le_mul_of_nonneg_left hy.1 hx.le])) hx.le)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at left right
  have hi : δ*(f x/x) < δ*(1+ε) := by linarith only [right.trans_lt hr]
  have lo : δ*(1-ε) < δ*(f x/x) := by linarith only [hl.trans_le left]
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [lt_of_mul_lt_mul_left lo hd.le, lt_of_mul_lt_mul_left hi hd.le]

lemma witness (t : ℝ) :
    ∃ c : ℝ, let f := fun x : ℝ => if 1 ≤ x then x*(1+c*cos (t*log x)) else 0
    Monotone f ∧ (∀ x, 0 ≤ f x) ∧ ¬ Tendsto (fun x => f x / x) atTop (𝓝 1) := by
  let c := (1 + |t|)⁻¹
  let g := fun x : ℝ => x*(1+c*cos (t*log x))
  have hc : 0 < c := by dsimp [c]; positivity
  have hct : c*(1+|t|) = 1 := by dsimp [c]; field_simp
  have hc1 : c ≤ 1 := by nlinarith [mul_nonneg hc.le (abs_nonneg t)]
  have nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ g x := mul_nonneg hx (by
    nlinarith [mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (t*log x)) hc.le])
  have der (x : ℝ) (hx : 0 < x) : HasDerivAt g (1+c*cos (t*log x)-c*t*sin (t*log x)) x := by
    have hd := ((hasDerivAt_id x).mul ((hasDerivAt_const x (1:ℝ)).add
      ((((Real.hasDerivAt_log hx.ne').const_mul t).cos).const_mul c)))
    convert hd using 1 <;> try rfl
    all_goals
      simp [Function.const_def, id]
      field_simp [hx.ne']
      ring
  have gm : MonotoneOn g (Ici 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
      (fun x hx => (der x (zero_lt_one.trans_le hx)).continuousAt.continuousWithinAt)
      (fun x hx => (der x (zero_lt_one.trans_le (interior_subset hx))).hasDerivWithinAt)
    intro x _
    have hbound : t*sin (t*log x) ≤ |t| := calc
      _ ≤ |t * sin (t*log x)| := le_abs_self _
      _ ≤ _ := by rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (t*log x)) (abs_nonneg t)).trans_eq (mul_one _)
    nlinarith [mul_le_mul_of_nonneg_left hbound hc.le,
      mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (t*log x)) hc.le]
  refine ⟨c, ?_, ?_, ?_⟩
  · intro x y hxy
    by_cases hx : 1 ≤ x
    · simpa [hx,hx.trans hxy] using gm hx (hx.trans hxy) hxy
    · by_cases hy : 1 ≤ y
      · simpa [hx,hy] using nonneg (zero_le_one.trans hy)
      · simp [hx,hy]
  · intro x
    dsimp only
    split_ifs with h
    · exact nonneg (zero_le_one.trans h)
    · exact le_rfl
  · intro hlim
    let d := if t = 0 then 1 else 2*π/|t|
    have hd : 0 < d := by dsimp [d]; split_ifs with h <;> positivity
    let X := fun n : ℕ => exp ((n : ℝ)*d)
    have htop : Tendsto X atTop atTop := Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hd)
    have hcos (n : ℕ) : cos (t*log (X n)) = 1 := by
      rw [show log (X n) = n*d from Real.log_exp _]
      rcases lt_trichotomy t 0 with ht | ht | ht
      · have he : t*(n*d) = -(n*(2*π)) := by dsimp [d]; rw [if_neg ht.ne, abs_of_neg ht]; field_simp [ht.ne]
        rw [he,cos_neg,cos_nat_mul_two_pi]
      · simp [ht]
      · have he : t*(n*d) = n*(2*π) := by dsimp [d]; rw [if_neg ht.ne', abs_of_pos ht]; field_simp
        rw [he,cos_nat_mul_two_pi]
    have hcst : Tendsto (fun _ : ℕ => 1+c) atTop (𝓝 1) := (hlim.comp htop).congr fun n => by
      have hX : 1 ≤ X n := Real.one_le_exp (by positivity)
      simp [hX,hcos, (zero_lt_one.trans_le hX).ne']
    have he := tendsto_nhds_unique hcst (tendsto_const_nhds (x := 1+c))
    linarith

theorem main : H1 → H2 → type_of% @Erdos967.erdos_967.variants.tauberian := by
  intro h1 h2 a ha h0 hs
  constructor
  · intro hz f hm hn hf hb hlim
    exact unsmooth hm (h1 a ha h0 hs hz f hm hn hf hb hlim)
  · intro himp t hz
    obtain ⟨c,hm,hn,hbad⟩ := witness t
    apply hbad
    apply himp _ hm hn (fun x hx => if_neg (not_le.2 hx))
    · intro x y
      exact ⟨_, fun _ ⟨u,hu,e⟩ => e ▸ hm hu.2⟩
    · exact h2 a ha h0 hs t c hz
end OMA.R_Erdos967_erdos_967_variants_tauberian_R1
