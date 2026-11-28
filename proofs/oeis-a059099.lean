import OMAStatements.S_oeis_a059099
import Mathlib.Tactic

/-! Multiply the series for exp(2r) and 1/(1-r). Their kth Cauchy
coefficient is r^k times the truncated exponential in the upper gamma
formula. With r=exp(x)/2, differentiation inserts a factor k each time.
A geometric majorant controls every derivative on the same open interval. -/

namespace GammaMoments
open OMA.S_oeis_a059099
open Filter
open scoped Topology

noncomputable def cutoff : ℝ := Real.log (3/2)
noncomputable def ratio (x : ℝ) : ℝ := Real.exp x / 2
noncomputable def piece (n k : ℕ) (x : ℝ) : ℝ :=
  partialExp k * (k : ℝ)^n * ratio x ^ k
noncomputable def moment (n : ℕ) (x : ℝ) : ℝ := ∑' k, piece n k x

lemma expSum (y : ℝ) : HasSum (fun j : ℕ => y^j / (j.factorial : ℝ)) (Real.exp y) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp y

lemma ratio_nonneg (x : ℝ) : 0 ≤ ratio x := by
  unfold ratio
  positivity

lemma zero_lt_cutoff : 0 < cutoff := Real.log_pos (by norm_num)

lemma ratio_small {x : ℝ} (hx : x < cutoff) : ratio x < 3/4 := by
  have h := Real.exp_lt_exp.mpr hx
  rw [cutoff, Real.exp_log (by norm_num : (0:ℝ) < 3/2)] at h
  unfold ratio
  linarith

lemma partial_nonneg (k : ℕ) : 0 ≤ partialExp k := by
  unfold partialExp
  positivity

lemma partial_le (k : ℕ) : partialExp k ≤ Real.exp 2 := by
  rw [← (expSum 2).tsum_eq]
  exact (expSum 2).summable.sum_le_tsum _ (fun j _ => by positivity)

lemma bound (n k : ℕ) {x : ℝ} (hx : x < cutoff) :
    ‖piece n k x‖ ≤ Real.exp 2 * ((k : ℝ)^n * (3/4 : ℝ)^k) := by
  have hk : 0 ≤ (k : ℝ)^n := by positivity
  have hr := ratio_nonneg x
  have ha := partial_nonneg k
  have orders := pow_le_pow_left₀ hr (ratio_small hx).le k
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ piece n k x by unfold piece; positivity)]
  unfold piece
  rw [mul_assoc]
  exact mul_le_mul (partial_le k) (mul_le_mul_of_nonneg_left orders hk)
    (mul_nonneg hk (pow_nonneg hr _)) (Real.exp_pos _).le

lemma bound_summable (n : ℕ) :
    Summable (fun k : ℕ => Real.exp 2 * ((k : ℝ)^n * (3/4 : ℝ)^k)) :=
  (summable_pow_mul_geometric_of_norm_lt_one n (by norm_num : ‖(3/4 : ℝ)‖ < 1)).mul_left _

lemma piece_summable (n : ℕ) {x : ℝ} (hx : x < cutoff) :
    Summable (fun k => piece n k x) :=
  (bound_summable n).of_norm_bounded (fun k => bound n k hx)

lemma piece_deriv (n k : ℕ) (x : ℝ) :
    HasDerivAt (piece n k) (piece (n+1) k x) x := by
  have hr : HasDerivAt ratio (ratio x) x := (Real.hasDerivAt_exp x).div_const 2
  cases k with
  | zero =>
    have hfun : piece n 0 = fun _ => partialExp 0 * (0 : ℝ)^n := by
      funext y
      simp [piece]
    rw [hfun]
    simpa [piece, pow_succ] using hasDerivAt_const x (partialExp 0 * (0 : ℝ)^n)
  | succ k =>
    change HasDerivAt (fun y => (partialExp (k+1) * ((k+1 : ℕ) : ℝ)^n) *
      ratio y^(k+1)) (piece (n+1) (k+1) x) x
    apply ((hr.pow (k+1)).const_mul (partialExp (k+1) * ((k+1 : ℕ) : ℝ)^n)).congr_deriv
    simp [piece, pow_succ]
    ring

lemma moment_deriv (n : ℕ) {x : ℝ} (hx : x < cutoff) :
    HasDerivAt (moment n) (moment (n+1) x) x := by
  apply hasDerivAt_tsum_of_isPreconnected (bound_summable (n+1))
    isOpen_Iio isPreconnected_Iio (fun k y _ => piece_deriv n k y)
    (fun k _ hy => bound (n+1) k hy) (y₀ := (0:ℝ))
    zero_lt_cutoff (piece_summable n zero_lt_cutoff) hx

lemma product_series {r : ℝ} (hr : 0 ≤ r) (hs : r < 1) :
    HasSum (fun k : ℕ => partialExp k * r^k) (Real.exp (2*r) * (1-r)⁻¹) := by
  have he := expSum (2*r)
  have hg := hasSum_geometric_of_lt_one hr hs
  have prod := hasSum_sum_range_mul_of_summable_norm he.summable.norm hg.summable.norm
  rw [he.tsum_eq, hg.tsum_eq] at prod
  apply prod.congr_fun
  intro k
  unfold partialExp
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hle : j ≤ k := by simpa using Finset.mem_range.mp hj
  symm
  calc
    (2*r)^j / (j.factorial : ℝ) * r^(k-j)
        = (2^j / (j.factorial : ℝ)) * (r^j * r^(k-j)) := by rw [mul_pow]; ring
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le hle]

lemma initial_moment {x : ℝ} (hx : x < cutoff) :
    egf x = (Real.exp (-1)/2) * moment 0 x := by
  have hs := (product_series (ratio_nonneg x) (lt_trans (ratio_small hx) (by norm_num))).tsum_eq
  have sm : moment 0 x = Real.exp (2*ratio x) * (1-ratio x)⁻¹ := by
    simpa [moment, piece] using hs
  rw [sm]
  have hn : Real.exp x < 2 := by
    have h := ratio_small hx
    unfold ratio at h
    linarith
  have hz : (2:ℝ) - Real.exp x ≠ 0 := by linarith
  have hz' : (1:ℝ) - Real.exp x/2 ≠ 0 := by linarith
  simp only [egf, ratio, show (2:ℝ) * (Real.exp x/2) = Real.exp x by ring,
    sub_eq_add_neg (Real.exp x) 1, Real.exp_add]
  field_simp

lemma derivatives (n : ℕ) {x : ℝ} (hx : x < cutoff) :
    iteratedDeriv n egf x = (Real.exp (-1)/2) * moment n x := by
  induction n generalizing x with
  | zero => simpa using initial_moment hx
  | succ n ih =>
    have near : iteratedDeriv n egf =ᶠ[𝓝 x] (fun y => (Real.exp (-1)/2) * moment n y) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact ih hy
    rw [iteratedDeriv_succ, near.deriv_eq]
    exact ((moment_deriv n hx).const_mul _).deriv

lemma term_zero (n k : ℕ) : term n k = (Real.exp (-2)/2) * piece n k 0 := by
  have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
  simp only [term, upperGamma, piece, ratio, Real.exp_zero, div_pow, one_pow, pow_succ]
  field_simp

end GammaMoments

open GammaMoments OMA.S_oeis_a059099

theorem OMA.solution : type_of% @OMA.S_oeis_a059099.main := by
  intro n _
  have heq : term n = fun k => (Real.exp (-2)/2) * piece n k 0 := funext (term_zero n)
  have hsum := piece_summable n zero_lt_cutoff
  rw [heq]
  refine ⟨hsum.mul_left _, ?_⟩
  rw [a, derivatives n zero_lt_cutoff, tsum_mul_left]
  change Real.exp (-1)/2 * moment n 0 = Real.exp 1 * ((Real.exp (-2)/2) * moment n 0)
  have h : Real.exp 1 * Real.exp (-2) = Real.exp (-1) := by
    rw [← Real.exp_add]
    norm_num
  linear_combination -(moment n 0)/2 * h
