import OMAReductions.R_Erdos967_erdos_967_variants_tauberian_R1
/-! Character cancellation under a reciprocal-summability assumption. Summand formulas adapted from @Genbox. -/
namespace Cancellation967
open Erdos967 Complex

lemma summand_eq (t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    summand t n = ((1 / (n : ℝ) : ℝ) : ℂ) * Complex.exp (((-(t * Real.log n)) : ℝ) * Complex.I) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold summand
  rw [Complex.cpow_def_of_ne_zero hn0]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hpos.le]
  rw [hlog]
  have : (Real.log n : ℂ) * (1 + t * I) = (Real.log n : ℂ) + (t * Real.log n : ℝ) * I := by
    push_cast; ring
  rw [this, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hpos]
  have h2 : Complex.exp (((-(t * Real.log n)) : ℝ) * I) =
      (Complex.exp ((t * Real.log n : ℝ) * I))⁻¹ := by
    rw [← Complex.exp_neg]; push_cast; ring_nf
  rw [h2]
  push_cast
  field_simp

lemma norm_summand (t : ℝ) {n : ℕ} (hn : 1 ≤ n) : ‖summand t n‖ = 1 / (n : ℝ) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [summand_eq t hn, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
open Real Filter
open scoped Topology
lemma cancellation (a : ℕ → ℕ) (ha : StrictMono a) (h0 : 1 < a 0)
    (hs : Summable (fun k => 1 / (a k : ℝ))) (t c : ℝ) (hz : 1 + (∑' k, summand t (a k)) = 0) :
    let f := fun x : ℝ => if 1 ≤ x then x*(1+c*Real.cos (t*Real.log x)) else 0
    Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
      (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) := by
  let f := fun x : ℝ => if 1 ≤ x then x*(1+c*Real.cos (t*Real.log x)) else 0
  change Tendsto (fun x : ℝ => (f x + ∑' k, f (x/(a k : ℝ)))/x) _ _
  have hn (k : ℕ) : 1 ≤ a k := h0.le.trans (ha.monotone (Nat.zero_le k))
  have hp (k : ℕ) : 0 < (a k : ℝ) := by exact_mod_cast hn k
  have hsum : Summable (fun k => summand t (a k)) := hs.of_norm_bounded fun k => (norm_summand t (hn k)).le
  let P (x : ℝ) := Complex.exp (((t*Real.log x : ℝ) : ℂ)*Complex.I)
  let A (x : ℝ) (k : ℕ) := (1/(a k : ℝ))*(1+c*Real.cos (t*Real.log (x/(a k : ℝ))))
  have phase (x : ℝ) (hx : 0 < x) (k : ℕ) :
      (P x * summand t (a k)).re = (1/(a k : ℝ))*Real.cos (t*Real.log (x/(a k : ℝ))) := by
    rw [summand_eq _ (hn k), mul_left_comm (P x), Complex.re_ofReal_mul]
    dsimp only [P]
    rw [← Complex.exp_add]
    rw [Real.log_div hx.ne' (hp k).ne', ← Complex.exp_ofReal_mul_I_re]
    congr 2
    push_cast
    ring
  have full (x : ℝ) (hx : 0 < x) :
      HasSum (A x) ((∑' k, 1/(a k : ℝ)) - c*Real.cos (t*Real.log x)) := by
    have hval : (∑' k, summand t (a k)) = -1 := by linear_combination hz
    have hr := Complex.hasSum_re (hsum.hasSum.mul_left (P x))
    rw [hval, mul_neg, mul_one, Complex.neg_re] at hr
    change HasSum (fun k => (P x * summand t (a k)).re) (-(P x).re) at hr
    have hpr : (P x).re = Real.cos (t*Real.log x) := Complex.exp_ofReal_mul_I_re _
    rw [hpr] at hr
    convert hs.hasSum.add (hr.mul_left c) using 1
    · ext k
      dsimp [A]
      rw [phase x hx k]
      ring
    · ring
  let err (x : ℝ) (k : ℕ) := if (a k : ℝ) ≤ x then 0 else -A x k
  have hbound (x : ℝ) (k : ℕ) : ‖err x k‖ ≤ (1+|c|)*(1/(a k : ℝ)) := by
    have hc : |c*Real.cos (t*Real.log (x/(a k : ℝ)))| ≤ |c| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg c)).trans_eq (mul_one _)
    dsimp only [err]
    split_ifs
    · simp only [norm_zero]; positivity
    · dsimp only [A]
      rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1/(a k : ℝ)), mul_comm (1+|c|)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (abs_add_le ..).trans (by rw [abs_one]; linarith)
  have hbs := hs.mul_left (1+|c|)
  have htail : Tendsto (fun x : ℝ => ∑' k, err x k) atTop (𝓝 0) := by
    simpa using tendsto_tsum_of_dominated_convergence (f := err) (g := fun _ => (0:ℝ)) hbs
      (fun k => tendsto_const_nhds.congr' ((eventually_ge_atTop (a k : ℝ)).mono (fun x hx => by simp [err,hx])))
      (Filter.Eventually.of_forall hbound)
  have heq (x : ℝ) (hx : 1 ≤ x) : (f x + ∑' k, f (x/(a k : ℝ)))/x =
      (1+∑' k, 1/(a k : ℝ)) + ∑' k, err x k := by
    have hx' : 0 < x := zero_lt_one.trans_le hx
    have hsum' := (full x hx').add ((hbs.of_norm_bounded (hbound x)).hasSum)
    have hadd (k : ℕ) : A x k + err x k = f (x/(a k : ℝ))/x := by
      dsimp only [err, f, A]
      simp only [one_le_div (hp k)]
      split_ifs <;> field_simp [hx'.ne', (hp k).ne'] <;> ring
    have hb := (hsum'.congr_fun (fun k => (hadd k).symm)).tsum_eq
    rw [add_div, ← tsum_div_const, hb]
    simp [f,hx,hx'.ne']
    ring
  have hh := (tendsto_const_nhds (f := atTop) (x := (1+∑' k, 1/(a k : ℝ)))).add htail
  rw [add_zero] at hh
  exact hh.congr'
    ((eventually_ge_atTop (1:ℝ)).mono fun x hx => (heq x hx).symm)
end Cancellation967
theorem OMA.solution : OMA.R_Erdos967_erdos_967_variants_tauberian_R1.H2 := by
  intro a ha h0 hs t c hz
  exact Cancellation967.cancellation a ha h0 hs t c hz
