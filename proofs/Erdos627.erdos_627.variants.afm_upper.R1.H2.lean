import OMAReductions.R_Erdos627_erdos_627_variants_afm_upper_R1
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! A tangent bound after setting t = sqrt ((1-x)/x). -/
namespace EntropyTangent

open Real Set

noncomputable def F (t : ℝ) := log (1+t^2) + t^2 * log (1+1/t^2)
noncomputable def D (t : ℝ) := 2*t * log (1+1/t^2)

theorem derivatives {t : ℝ} (ht : 0 < t) :
    HasDerivAt F (D t) t ∧ HasDerivAt D (2*log (1+1/t^2)-4/(1+t^2)) t := by
  have idh := hasDerivAt_id t
  have one := hasDerivAt_const t (1:ℝ)
  have sqh := idh.fun_pow 2
  have hn : (1:ℝ)+1/t^2 ≠ 0 := by positivity
  have hsq : t^2 ≠ 0 := by positivity
  have h1 := (one.fun_add sqh).log (by positivity : (1:ℝ)+t^2 ≠ 0)
  have h2 := (one.fun_add (one.fun_div sqh hsq)).log hn
  constructor
  · apply (h1.fun_add (sqh.fun_mul h2)).congr_deriv
    dsimp [D]; field_simp; ring
  · apply ((idh.const_mul 2).fun_mul h2).congr_deriv
    dsimp; field_simp; ring

theorem anti : AntitoneOn D (Ici 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact fun t ht => ((derivatives (lt_of_lt_of_le zero_lt_one ht)).2).continuousAt.continuousWithinAt
  · exact fun t ht => ((derivatives (lt_of_lt_of_le zero_lt_one (interior_subset ht))).2).differentiableAt.differentiableWithinAt
  · intro t ht
    have h : 1 ≤ t := interior_subset ht
    have h0 : 0 < t := by linarith
    rw [(derivatives h0).2.deriv]
    have hl := log_le_sub_one_of_pos (show 0 < (1:ℝ)+1/t^2 by positivity)
    have hle : 1/t^2 ≤ 2/(1+t^2) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (t-1)]
    have hlog : log (1+1/t^2) ≤ 2/(1+t^2) := (by simpa using hl : log (1+1/t^2) ≤ 1/t^2).trans hle
    rw [show 4/(1+t^2) = 2*(2/(1+t^2)) by ring]
    exact sub_nonpos.mpr (mul_le_mul_of_nonneg_left hlog (by norm_num))

theorem tangent {a t : ℝ} (ha : 1 ≤ a) (ht : 1 ≤ t) : F t ≤ F a + D a * (t-a) := by
  have mvt {l r : ℝ} (hl : 1 ≤ l) (hlr : l < r) :
      ∃ z ∈ Ioo l r, D z * (r-l) = F r - F l := by
    obtain ⟨z,hz,hd⟩ := exists_hasDerivAt_eq_slope F D hlr
      (fun v hv => ((derivatives (lt_of_lt_of_le zero_lt_one (hl.trans hv.1))).1).continuousAt.continuousWithinAt)
      (fun v hv => (derivatives (lt_of_lt_of_le zero_lt_one (hl.trans hv.1.le))).1)
    exact ⟨z,hz,(eq_div_iff (by linarith)).mp hd⟩
  rcases lt_trichotomy t a with h|rfl|h
  · obtain ⟨z,hz,he⟩ := mvt ht h
    have hh := mul_le_mul_of_nonneg_right (anti (ht.trans hz.1.le) ha hz.2.le) (sub_nonneg.mpr h.le)
    linarith
  · simp
  · obtain ⟨z,hz,he⟩ := mvt ha h
    have hh := mul_le_mul_of_nonneg_right (anti ha (ha.trans hz.1.le) hz.1.le) (sub_nonneg.mpr h.le)
    linarith

abbrev anchor : ℝ := 1.0809235

set_option maxHeartbeats 3000000 in
theorem num1 : 0.773987543 ≤ log (1+anchor^2) ∧ log (1+anchor^2) ≤ 0.773987548 := by
  let u : ℝ := 1 - (1+anchor^2)/2
  have h := abs_le.mp (abs_log_sub_add_sum_range_le (x := u) (by norm_num [u,anchor]) 9)
  have idlog : log (1+anchor^2) = log 2 + log (1-u) := by
    rw [← log_mul (by norm_num) (by norm_num [u,anchor])]
    congr 1; ring
  dsimp [u,anchor] at h
  norm_num [Finset.sum_range_succ] at h
  rw [idlog]
  dsimp [u,anchor]
  norm_num at *
  constructor <;> linarith [log_two_gt_d9, log_two_lt_d9]

set_option maxHeartbeats 3000000 in
theorem num2 : 0.618356006 ≤ log (1+1/anchor^2) ∧ log (1+1/anchor^2) ≤ 0.618356011 := by
  let u : ℝ := 1 - (1+1/anchor^2)/2
  have h := abs_le.mp (abs_log_sub_add_sum_range_le (x := u) (by norm_num [u,anchor]) 9)
  have idlog : log (1+1/anchor^2) = log 2 + log (1-u) := by
    rw [← log_mul (by norm_num) (by norm_num [u,anchor])]
    congr 1; ring
  dsimp [u,anchor] at h
  norm_num [Finset.sum_range_succ] at h
  rw [idlog]
  dsimp [u,anchor]
  norm_num at *
  constructor <;> linarith [log_two_gt_d9, log_two_lt_d9]

theorem bound {t : ℝ} (ht : 1 ≤ t) : F t ≤ 1.3367911 * t + 0.14 / exp 1 := by
  have h := tangent (a := anchor) (by norm_num [anchor]) ht
  have h1 := num1
  have h2 := num2
  have hs : D anchor ≤ 1.3367911 := by unfold D; unfold anchor at *; linarith
  have hi : F anchor - D anchor * anchor ≤ 0.05150312 := by
    unfold F D; unfold anchor at *; linarith
  have hc : 0.05150312 ≤ 0.14 / exp 1 := by
    apply (le_div_iff₀ (exp_pos _)).mpr
    linarith [exp_one_lt_d9]
  calc
    F t ≤ F anchor + D anchor * (t-anchor) := h
    _ = D anchor * t + (F anchor - D anchor * anchor) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hs (by linarith)) (hi.trans hc)

end EntropyTangent

open EntropyTangent Real

theorem OMA.solution : OMA.R_Erdos627_erdos_627_variants_afm_upper_R1.H2 := by
  intro x hx hx'
  rcases hx.eq_or_lt with rfl|hx
  · norm_num
  have hy : 0 < 1-x := by linarith
  let t := sqrt ((1-x)/x)
  have ht : 1 ≤ t := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    apply (le_div_iff₀ hx).mpr
    nlinarith
  have hs : t^2 = (1-x)/x := Real.sq_sqrt (by positivity)
  have hl : 1+t^2 = x⁻¹ := by rw [hs]; field_simp; ring
  have hr : 1+1/t^2 = (1-x)⁻¹ := by rw [hs]; field_simp; ring
  have he : binEntropy x = x * F t := by
    unfold F binEntropy
    rw [hl,hr,hs]; field_simp
  have ht0 : 0 ≤ t := by linarith
  have hsqrt : sqrt (x*(1-x)) = x*t := by
    have h : (x*t)^2 = x*(1-x) := by rw [mul_pow,hs]; field_simp
    rw [← h, sqrt_sq (mul_nonneg hx.le ht0)]
  have htop : binEntropy x - 0.14/exp 1*x ≤ 1.3367911 * sqrt (x*(1-x)) := by
    rw [he,hsqrt]
    nlinarith [mul_le_mul_of_nonneg_left (bound ht) hx.le]
  have hbot : 0 ≤ binEntropy x - 0.14/exp 1*x := by
    have hxinv : 2 ≤ x⁻¹ := by rw [← one_div]; apply (le_div_iff₀ hx).mpr; linarith
    have hlx := log_le_log (by norm_num) hxinv
    have hsmall : 0.14 / exp 1 ≤ log 2 := by
      have : 0.14 / exp 1 ≤ 0.14 := (div_le_iff₀ (exp_pos _)).mpr (by linarith [exp_one_gt_two])
      linarith [log_two_gt_d9]
    have hly : 0 ≤ log (1-x)⁻¹ := log_nonneg (by rw [← one_div]; apply (le_div_iff₀ hy).mpr; linarith)
    unfold binEntropy
    nlinarith [mul_nonneg hy.le hly, mul_le_mul_of_nonneg_left (hsmall.trans hlx) hx.le]
  have hp : 0 < sqrt (x*(1-x)) := sqrt_pos.mpr (mul_pos hx hy)
  have den : 0 < log 2 * sqrt (x*(1-x)) := mul_pos (log_pos (by norm_num)) hp
  have hrat : (binEntropy x - 0.14 / exp 1 * x) / (log 2 * sqrt (x*(1-x))) ≤ 1.928582 := by
    apply (div_le_iff₀ den).mpr
    nlinarith [mul_le_mul_of_nonneg_right log_two_gt_d9.le hp.le]
  have hu := sq_le_sq' (by linarith [div_nonneg hbot den.le] :
    -(1.928582:ℝ) ≤ (binEntropy x - 0.14/exp 1*x)/(log 2 * sqrt (x*(1-x)))) hrat
  exact hu.trans (by norm_num)

