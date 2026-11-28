import OMAReductions.R_DensityHypothesis_density_hypothesis_zeta_zeros_R1

/-!
Proof of `DensityHypothesis.density_hypothesis_zeta_zeros.R1.H2`:
the classical Riemann-von Mangoldt upper bound `N(T) <= C * T * log T` for `T >= 2`.

Adapts the entire-function Jensen counting bound (`vbe`, `vbo`, `vcz`) and the order-one
growth estimate for `xi(s) = s(s - 1) completedRiemannZeta₀ s + 1` (`XiOrderAux`, `vai`, `vef`)
from PR #1399 (`proofs/CramerConjecture.cramer_conjecture.variants.conditional_rh.lean`, by `@senamakel`),
bridged to `Complex.zeroCountOn riemannZeta` on `{0 <= Re s <= 1, 0 < Im s <= T}`.
-/

section
open Filter Function MeromorphicOn Metric Real Set
namespace Function.locallyFinsuppWithin
variable {E : Type*} [NormedAddCommGroup E]
lemma vaz {D : locallyFinsupp E ℤ} {r : ℝ} {z : E}
    (hz : z ∈ (toClosedBall r D).support) : ‖z‖ ≤ |r| := by
  have hz_ball : z ∈ closedBall (0 : E) |r| := (toClosedBall r D).supportWithinDomain hz
  simpa [mem_closedBall, dist_zero_right] using hz_ball
lemma vaM {D : locallyFinsupp E ℤ} {r : ℝ} {z : E}
    (hz : ‖z‖ ≤ |r|) : toClosedBall r D z = D z := by
  have hz_ball : z ∈ closedBall (0 : E) |r| := by
    simpa [mem_closedBall, dist_zero_right] using hz
  simpa using toClosedBall_eval_within (f := D) hz_ball
lemma vaW
    {D : locallyFinsupp E ℤ} {r : ℝ} {z : E} (hzD : z ∈ D.support) (hzR : ‖z‖ ≤ |r|) :
    z ∈ (toClosedBall r D).support := by
  rw [Function.mem_support]
  rw [vaM hzR]
  rwa [Function.mem_support] at hzD
lemma vdh {D : locallyFinsupp E ℤ} {r : ℝ} {z : E}
    (hz : z ∈ (toClosedBall r D).support) : z ∈ D.support := by
  have hnorm : ‖z‖ ≤ |r| := vaz hz
  rw [Function.mem_support] at hz ⊢
  rw [vaM hnorm] at hz
  exact hz
noncomputable def vbe {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (D : locallyFinsupp E ℤ) (R : ℝ) : ℝ := by
  classical
  exact
    (((finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).toFinset).filter
      (fun z => z ≠ (0 : E))).sum fun z => (D z : ℝ)
end Function.locallyFinsuppWithin
namespace Function.locallyFinsuppWithin
theorem vbo
    {R : ℝ} {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hR : R ≠ 0) :
    logCounting (divisor f ⊤) R =
      circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have hmero : Meromorphic f := fun z => (hf.analyticAt z).meromorphicAt
  simpa [top_eq_univ] using
    logCounting_divisor_eq_circleAverage_sub_const (f := f) hmero hR
end Function.locallyFinsuppWithin
end
section
namespace Real
variable {α E : Type*} [SeminormedAddCommGroup E]
theorem veO (w : E) :
    Real.log ‖w‖ ≤ Real.log (1 + ‖w‖) := by
  by_cases h0 : ‖w‖ = 0
  · simp [h0]
  · have hpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm h0)
    exact Real.log_le_log hpos (by linarith [norm_nonneg w])
variable {F : Type*} [NormedAddCommGroup F]
theorem vdY {z : F} {r : ℝ} (hz : ‖z‖ ≤ r) :
    0 ≤ Real.log (r * ‖z‖⁻¹) := by
  by_cases hz0 : z = 0
  · simp [hz0]
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have : (1 : ℝ) ≤ r * ‖z‖⁻¹ := by
      have : (1 : ℝ) ≤ r / ‖z‖ := (one_le_div hzpos).2 hz
      simpa [div_eq_mul_inv] using this
    exact Real.log_nonneg this
theorem vcm {z : F} {R : ℝ} (hz0 : z ≠ 0)
    (hz : ‖z‖ ≤ R) :
    Real.log 2 ≤ Real.log ((2 * R) * ‖z‖⁻¹) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hRdiv : (1 : ℝ) ≤ R / ‖z‖ := (one_le_div hzpos).2 hz
  have hle2 : (2 : ℝ) ≤ (2 * R) * ‖z‖⁻¹ := by
    have : (2 : ℝ) ≤ 2 * (R / ‖z‖) := by nlinarith
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  exact Real.log_le_log (by norm_num) hle2
end Real
end
section
open Filter Function MeromorphicOn Metric Real Set
namespace Function.locallyFinsuppWithin
variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
theorem vcz {D : locallyFinsupp E ℤ} (hDnonneg : 0 ≤ D)
    {R : ℝ} (hR : 1 ≤ R) :
    (log 2) * vbe D R ≤ logCounting D (2 * R) := by
  classical
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
  set r : ℝ := 2 * R
  have hrpos : 0 < r := by dsimp [r]; nlinarith
  let Dr := toClosedBall r D
  have hDr_fin : Set.Finite Dr.support := Dr.finiteSupport (isCompact_closedBall (0 : E) |r|)
  let F : Finset E := hDr_fin.toFinset
  let SR : Finset E :=
    (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).toFinset
  let S : Finset E := SR.filter fun z => z ≠ (0 : E)
  have hS_sub : S ⊆ F := by
    intro z hzS
    have hz_mem_SR : z ∈ SR := (Finset.mem_filter.1 hzS).1
    have hzR : z ∈ (toClosedBall R D).support := by
      exact (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).mem_toFinset.1
        hz_mem_SR
    have hz_norm_le_R : ‖z‖ ≤ R := by
      have := vaz hzR
      simpa [abs_of_pos hR0] using this
    have hz_norm_le_r : ‖z‖ ≤ |r| := by
      have : ‖z‖ ≤ r := le_trans hz_norm_le_R (by dsimp [r]; nlinarith)
      simpa [abs_of_pos hrpos] using this
    have hzD : z ∈ D.support := vdh hzR
    have : z ∈ Dr.support := by
      simpa [Dr] using
        vaW (D := D) (r := r) hzD hz_norm_le_r
    exact hDr_fin.mem_toFinset.2 this
  have hlogCounting :
      logCounting D r
        = (F.sum fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) + (D 0 : ℝ) * log r := by
    have hsupp : Function.support (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) ⊆ F := by
      intro z hz
      have : Dr z ≠ 0 := by
        by_contra h0
        simp [Function.mem_support, h0] at hz
      have : z ∈ Dr.support := by simpa [Function.mem_support] using this
      exact hDr_fin.mem_toFinset.2 this
    simp [logCounting, Dr, r,
      finsum_eq_sum_of_support_subset (f := fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) (s := F) hsupp]
  have hsum_le :
      (log 2) * (S.sum fun z => (D z : ℝ))
        ≤ F.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) := by
    have hterm_nonneg : ∀ z ∈ F, 0 ≤ (Dr z : ℝ) * log (r * ‖z‖⁻¹) := by
      intro z hzF
      have hz_sup : z ∈ Dr.support := hDr_fin.mem_toFinset.1 hzF
      have hDz : 0 ≤ Dr z := by
        have hDz' : 0 ≤ D z := hDnonneg z
        have hDrz : Dr z = D z :=
          vaM (vaz hz_sup)
        simpa [hDrz] using hDz'
      have hlog : 0 ≤ log (r * ‖z‖⁻¹) := by
        have hzle : ‖z‖ ≤ r := by
          have hnorm := vaz hz_sup
          simpa [abs_of_pos hrpos] using hnorm
        exact vdY hzle
      exact mul_nonneg (by exact_mod_cast hDz) hlog
    have hsumSF :
        S.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹))
          ≤ F.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hS_sub (by
        intro z hzF _; exact hterm_nonneg z hzF)
    have hterm_ge : ∀ z ∈ S, (log 2) * (D z : ℝ) ≤ (Dr z : ℝ) * log (r * ‖z‖⁻¹) := by
      intro z hzS
      have hz0 : z ≠ (0 : E) := (Finset.mem_filter.1 hzS).2
      have hz_norm_le_R : ‖z‖ ≤ R := by
        have hz_mem_SR : z ∈ SR := (Finset.mem_filter.1 hzS).1
        have hzRsup : z ∈ (toClosedBall R D).support := by
          exact (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).mem_toFinset.1
            hz_mem_SR
        have hnorm := vaz hzRsup
        simpa [abs_of_pos hR0] using hnorm
      have hlog_le : log 2 ≤ log (r * ‖z‖⁻¹) := by
        simpa [r] using vcm hz0 hz_norm_le_R
      have hDz_nonneg : 0 ≤ D z := hDnonneg z
      have hz_in_ballr : z ∈ closedBall (0 : E) |r| := by
        have : ‖z‖ ≤ r := le_trans hz_norm_le_R (by dsimp [r]; nlinarith)
        simpa [mem_closedBall, dist_zero_right, abs_of_pos hrpos] using this
      have hDrz : Dr z = D z := by
        have hz_norm_le : ‖z‖ ≤ |r| := by
          simpa [mem_closedBall, dist_zero_right] using hz_in_ballr
        simpa [Dr] using vaM (D := D) (r := r) (z := z) hz_norm_le
      have : (log 2) * (D z : ℝ) ≤ (log (r * ‖z‖⁻¹)) * (D z : ℝ) :=
        mul_le_mul_of_nonneg_right hlog_le (by exact_mod_cast hDz_nonneg)
      simpa [hDrz, mul_assoc, mul_left_comm, mul_comm] using this
    calc
      (log 2) * (S.sum fun z => (D z : ℝ))
          = S.sum (fun z => (log 2) * (D z : ℝ)) := by simp [Finset.mul_sum]
      _ ≤ S.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) :=
        Finset.sum_le_sum fun z hz => hterm_ge z hz
      _ ≤ F.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) := hsumSF
  have hcenter_nonneg : 0 ≤ (D 0 : ℝ) * log r := by
    have hD0 : 0 ≤ D 0 := hDnonneg 0
    have hlogr : 0 ≤ log r := log_nonneg (by nlinarith [hR])
    exact mul_nonneg (by exact_mod_cast hD0) hlogr
  have : (log 2) * (S.sum fun z => (D z : ℝ)) ≤ logCounting D r := by
    rw [hlogCounting]
    nlinarith [hsum_le, hcenter_nonneg]
  simpa [vbe, r, S, SR] using this
end Function.locallyFinsuppWithin
end
section
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
theorem Differentiable.divisor_nonneg {f : ℂ → E} (hf : Differentiable ℂ f) :
    0 ≤ MeromorphicOn.divisor f (univ : Set ℂ) :=
  MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hf.differentiableOn.analyticOnNhd isOpen_univ)
end
section
namespace Erdos985.Analytic.XiOrderAux
open Real
def vaq (F : ℂ → ℂ) : Prop :=
  ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * exp (a * ((‖s‖ + b) * log (‖s‖ + b)))
lemma vcx {u : ℝ} (hu : 3 ≤ u) : 1 ≤ log u := by
  have h3 : exp 1 < 3 := lt_of_lt_of_le exp_one_lt_d9 (by norm_num)
  rw [le_log_iff_exp_le (by linarith)]
  linarith
lemma vhR {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) : u * log u ≤ v * log v :=
  mul_le_mul huv (log_le_log (by linarith) huv) (log_nonneg hu) (by linarith)
lemma vim {a a' b b' y y' : ℝ} (ha : 0 ≤ a) (haa : a ≤ a') (hb : 3 ≤ b) (hy : 0 ≤ y)
    (hle : y + b ≤ y' + b') :
    a * ((y + b) * log (y + b)) ≤ a' * ((y' + b') * log (y' + b')) := by
  have h1 : 1 ≤ log (y + b) := vcx (by linarith)
  have h2 : (y + b) * log (y + b) ≤ (y' + b') * log (y' + b') :=
    vhR (by linarith) hle
  have h3 : 0 ≤ (y' + b') * log (y' + b') := by nlinarith
  exact mul_le_mul haa h2 (by nlinarith) (ha.trans haa)
lemma vaq.vgu {F : ℂ → ℂ} {K a b : ℝ}
    (h : ∀ s, ‖F s‖ ≤ K * exp (a * ((‖s‖ + b) * log (‖s‖ + b)))) : 0 ≤ K :=
  nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (h 0)) (exp_pos _)
lemma vaq.mono {F : ℂ → ℂ} {K a b : ℝ} (ha : 0 ≤ a) (hb : 3 ≤ b)
    (h : ∀ s, ‖F s‖ ≤ K * exp (a * ((‖s‖ + b) * log (‖s‖ + b)))) {a' b' : ℝ} (haa : a ≤ a')
    (hbb : b ≤ b') : ∀ s, ‖F s‖ ≤ K * exp (a' * ((‖s‖ + b') * log (‖s‖ + b'))) := by
  intro s
  refine (h s).trans (mul_le_mul_of_nonneg_left ?_ (vaq.vgu h))
  exact exp_le_exp.2 (vim ha haa hb (norm_nonneg _) (by linarith))
lemma vaq.congr {F G : ℂ → ℂ} (hF : vaq F) (h : ∀ s, F s = G s) : vaq G := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  exact ⟨K, a, b, ha, hb, fun s => h s ▸ hK s⟩
lemma vaq.const (c : ℂ) : vaq (fun _ => c) :=
  ⟨‖c‖, 0, 3, le_rfl, le_rfl, fun s => by simp⟩
lemma vaq.add {F G : ℂ → ℂ} (hF : vaq F) (hG : vaq G) :
    vaq (fun s => F s + G s) := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  obtain ⟨K', a', b', ha', hb', hK'⟩ := hG
  refine ⟨K + K', max a a', max b b', le_max_of_le_left ha, le_max_of_le_left hb, fun s => ?_⟩
  have h1 := vaq.mono ha hb hK (le_max_left a a') (le_max_left b b') s
  have h2 := vaq.mono ha' hb' hK' (le_max_right a a') (le_max_right b b') s
  calc ‖F s + G s‖ ≤ ‖F s‖ + ‖G s‖ := norm_add_le _ _
    _ ≤ _ := by rw [add_mul]; exact add_le_add h1 h2
lemma vaq.mul {F G : ℂ → ℂ} (hF : vaq F) (hG : vaq G) :
    vaq (fun s => F s * G s) := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  obtain ⟨K', a', b', ha', hb', hK'⟩ := hG
  refine ⟨K * K', a + a', max b b', add_nonneg ha ha', le_max_of_le_left hb, fun s => ?_⟩
  have h1 := vaq.mono ha hb hK le_rfl (le_max_left b b') s
  have h2 := vaq.mono ha' hb' hK' le_rfl (le_max_right b b') s
  rw [norm_mul]
  calc ‖F s‖ * ‖G s‖ ≤ _ := mul_le_mul h1 h2 (norm_nonneg _)
        (mul_nonneg (vaq.vgu hK) (exp_pos _).le)
    _ = _ := by rw [add_mul a a', exp_add]; ring
lemma vaq.comp {F : ℂ → ℂ} (hF : vaq F) {g : ℂ → ℂ} {d : ℝ} (hd : 0 ≤ d)
    (hg : ∀ s, ‖g s‖ ≤ ‖s‖ + d) : vaq (fun s => F (g s)) := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  refine ⟨K, a, b + d, ha, by linarith, fun s => (hK (g s)).trans ?_⟩
  refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (vaq.vgu hK)
  exact vim ha le_rfl hb (norm_nonneg _) (by linarith [hg s])
end Erdos985.Analytic.XiOrderAux
end
section
namespace Erdos985.Analytic.XiOrderAux
open Real Set MeasureTheory
open scoped Nat
lemma vdF {y : ℝ} (hy : 0 < y) (m : ℕ) : exp (-y) ≤ m ! * y⁻¹ ^ m := by
  have h := pow_div_factorial_le_exp (x := y) (hx := hy.le) (n := m)
  have hpos : 0 < y ^ m / m ! := by positivity
  rw [exp_neg]
  calc (exp y)⁻¹ ≤ (y ^ m / m !)⁻¹ := inv_anti₀ hpos h
    _ = m ! * y⁻¹ ^ m := by rw [inv_div, inv_pow, div_eq_mul_inv]
noncomputable def ved : ℝ → ℝ :=
  (Ioc 0 1).indicator (fun _ => (1 : ℝ)) + (Ioi 1).indicator (fun t => t ^ (-2 : ℝ))
lemma vgS : IntegrableOn ved (Ioi 0) := by
  have h1 : Integrable ((Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Ioc
  have h2 : Integrable ((Ioi (1 : ℝ)).indicator (fun t : ℝ => t ^ (-2 : ℝ))) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).integrable_indicator measurableSet_Ioi
  exact (h1.add h2).integrableOn
lemma vhL (P : WeakFEPair ℂ) {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hf : ∀ t : ℝ, 1 < t → ‖P.f t - P.f₀‖ ≤ C * exp (-p * t))
    (hg : ∀ t : ℝ, 1 < t → ‖P.g t - P.g₀‖ ≤ C * exp (-p * t))
    (s : ℂ) (m : ℕ) (hm : ‖s‖ + P.k + 1 ≤ m) (t : ℝ) (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) • P.f_modif t‖ ≤ (C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m) * ved t := by
  have hsre : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
  have hk := P.hk
  have hA : 0 ≤ C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m := by positivity
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
  rcases lt_trichotomy t 1 with h1 | rfl | h1
  ·
    have hdom : ved t = 1 := by
      simp [ved, indicator, ht, h1.le, not_lt.2 h1.le]
    rw [hdom, mul_one]
    have hfm : P.f_modif t = (P.ε * ((1 / t) ^ P.k : ℝ)) • (P.g (1 / t) - P.g₀) := by
      have hfe := P.h_feq (1 / t) (by simpa using ht)
      rw [one_div_one_div] at hfe
      simp only [WeakFEPair.f_modif, Pi.add_apply, indicator, mem_Ioi, mem_Ioo, ht, h1,
        and_self, ite_true, not_lt.2 h1.le, ite_false, zero_add, hfe, smul_sub]
      congr 2
      rw [one_div, inv_rpow ht.le, rpow_neg ht.le]
    have h1t : 1 < 1 / t := by rw [lt_one_div one_pos ht, div_one]; exact h1
    rw [hfm, norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    have hgb := hg (1 / t) h1t
    have he := vdF (show 0 < p * (1 / t) by positivity) m
    rw [neg_mul] at hgb
    have hcalc : t ^ (s.re - 1) * (1 / t) ^ P.k * ((1 / t) ⁻¹ ^ m) ≤ 1 := by
      rw [one_div, inv_inv, inv_rpow ht.le, ← rpow_neg ht.le, ← rpow_natCast,
        ← rpow_add ht, ← rpow_add ht]
      apply rpow_le_one ht.le h1.le
      have := neg_abs_le s.re
      linarith
    calc t ^ (s.re - 1) * (‖P.ε‖ * (1 / t) ^ P.k * ‖P.g (1 / t) - P.g₀‖)
        ≤ t ^ (s.re - 1) * (‖P.ε‖ * (1 / t) ^ P.k * (C * (m ! * (p * (1 / t))⁻¹ ^ m))) := by
          gcongr
          exact hgb.trans (mul_le_mul_of_nonneg_left he hC)
      _ = C * ‖P.ε‖ * m ! * p⁻¹ ^ m * (t ^ (s.re - 1) * (1 / t) ^ P.k * ((1 / t) ⁻¹ ^ m)) := by
          rw [mul_inv, mul_pow]; ring
      _ ≤ C * ‖P.ε‖ * m ! * p⁻¹ ^ m * 1 := by gcongr
      _ ≤ C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m := by
          rw [mul_one]; gcongr; exact le_max_right _ _
  · have h0 : P.f_modif 1 = 0 := by simp [WeakFEPair.f_modif]
    rw [h0, norm_zero, mul_zero]
    exact mul_nonneg hA (by simp [ved])
  ·
    have hdom : ved t = t ^ (-2 : ℝ) := by
      simp [ved, indicator, h1, not_le.2 h1]
    rw [hdom]
    have hfm : P.f_modif t = P.f t - P.f₀ := by
      simp [WeakFEPair.f_modif, indicator, h1, not_lt.2 h1.le]
    rw [hfm]
    have he := vdF (show 0 < p * t by positivity) m
    have hfb := hf t h1
    rw [neg_mul] at hfb
    have ht0 : 0 < t := ht
    have hcalc : t ^ (s.re - 1) * t⁻¹ ^ m ≤ t ^ (-2 : ℝ) := by
      rw [inv_pow, ← rpow_natCast, ← rpow_neg ht.le, ← rpow_add ht]
      apply rpow_le_rpow_of_exponent_le h1.le
      have := le_abs_self s.re
      linarith
    calc t ^ (s.re - 1) * ‖P.f t - P.f₀‖
        ≤ t ^ (s.re - 1) * (C * (m ! * (p * t)⁻¹ ^ m)) := by
          gcongr
          exact hfb.trans (mul_le_mul_of_nonneg_left he hC)
      _ = C * 1 * m ! * p⁻¹ ^ m * (t ^ (s.re - 1) * t⁻¹ ^ m) := by
          rw [mul_inv, mul_pow]; ring
      _ ≤ C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m * t ^ (-2 : ℝ) := by
          gcongr
          exact le_max_left _ _
lemma viF (P : WeakFEPair ℂ) {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hf : ∀ t : ℝ, 1 < t → ‖P.f t - P.f₀‖ ≤ C * exp (-p * t))
    (hg : ∀ t : ℝ, 1 < t → ‖P.g t - P.g₀‖ ≤ C * exp (-p * t))
    (s : ℂ) (m : ℕ) (hm : ‖s‖ + P.k + 1 ≤ m) :
    ‖P.Λ₀ s‖ ≤ (C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m) * ∫ t in Ioi 0, ved t := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (vgS.const_mul _) ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioi
    (fun t ht => vhL P hp hC hf hg s m hm t ht)
theorem vhO (P : WeakFEPair ℂ) {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hf : ∀ t : ℝ, 1 < t → ‖P.f t - P.f₀‖ ≤ C * exp (-p * t))
    (hg : ∀ t : ℝ, 1 < t → ‖P.g t - P.g₀‖ ≤ C * exp (-p * t)) : vaq P.Λ₀ := by
  set I0 := ∫ t in Ioi 0, ved t
  set Q := max 1 p⁻¹
  have hQ : 1 ≤ Q := le_max_left _ _
  have hk := P.hk
  set b := P.k + 5
  refine ⟨C * max 1 ‖P.ε‖ * I0, 1 + log Q, b, by linarith [log_nonneg hQ], by linarith,
    fun s => ?_⟩
  set m := ⌈‖s‖ + P.k + 1⌉₊
  have hm : ‖s‖ + P.k + 1 ≤ m := Nat.le_ceil _
  have hm' : (m : ℝ) ≤ ‖s‖ + b := by
    have := Nat.ceil_lt_add_one (show 0 ≤ ‖s‖ + P.k + 1 by positivity)
    linarith
  have hm1 : (1 : ℝ) ≤ m := by linarith [norm_nonneg s]
  have hI0 : 0 ≤ I0 := setIntegral_nonneg measurableSet_Ioi (fun t _ => by
    simp only [ved, Pi.add_apply]
    exact add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
      (indicator_nonneg (fun t ht => rpow_nonneg (le_of_lt (lt_trans zero_lt_one ht)) _) _))
  refine (viF P hp hC hf hg s m hm).trans ?_
  have hfac : (m ! : ℝ) * p⁻¹ ^ m ≤ exp ((1 + log Q) * ((‖s‖ + b) * log (‖s‖ + b))) := by
    have h1 : (m ! : ℝ) * p⁻¹ ^ m ≤ ((m : ℝ) * Q) ^ m := by
      rw [mul_pow]
      gcongr
      · exact_mod_cast Nat.factorial_le_pow m
      · exact le_max_right _ _
    have h2 : ((m : ℝ) * Q) ^ m = exp (m * log (m * Q)) := by
      rw [← log_pow, exp_log (by positivity)]
    have hL : 1 ≤ log (‖s‖ + b) := vcx (by linarith [norm_nonneg s])
    have hlogQ : 0 ≤ log Q := log_nonneg hQ
    have h3 : (m : ℝ) * log (m * Q) ≤ (1 + log Q) * ((‖s‖ + b) * log (‖s‖ + b)) := by
      rw [log_mul (by positivity) (by positivity)]
      have e1 : (m : ℝ) * log m ≤ (‖s‖ + b) * log (‖s‖ + b) := vhR hm1 hm'
      have e2 : (m : ℝ) * log Q ≤ (‖s‖ + b) * log (‖s‖ + b) * log Q := by
        have : (m : ℝ) ≤ (‖s‖ + b) * log (‖s‖ + b) := by nlinarith
        exact mul_le_mul_of_nonneg_right this hlogQ
      nlinarith
    rw [h2] at h1
    exact h1.trans (exp_le_exp.2 h3)
  have hE : 0 ≤ C * max 1 ‖P.ε‖ := by positivity
  calc C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m * I0 = C * max 1 ‖P.ε‖ * I0 * (m ! * p⁻¹ ^ m) := by ring
    _ ≤ _ := by gcongr
end Erdos985.Analytic.XiOrderAux
end
section
namespace Erdos985.Analytic.XiOrderAux
open Real Set Filter Asymptotics HurwitzZeta
lemma veG {F : ℝ → ℝ} (hc : ContinuousOn F (Ioi 0)) {p : ℝ} (hp : 0 ≤ p)
    (h : F =O[atTop] fun x => exp (-p * x)) :
    ∃ C, 0 ≤ C ∧ ∀ t, 1 < t → |F t| ≤ C * exp (-p * t) := by
  obtain ⟨c, hc'⟩ := h.bound
  obtain ⟨T, hT⟩ := eventually_atTop.1 hc'
  set T' := max T 1
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := T')).exists_bound_of_continuousOn
    (hc.mono (fun x hx => lt_of_lt_of_le zero_lt_one hx.1))
  refine ⟨max (max c 0) (max M 0 * exp (p * T')), by positivity, fun t ht => ?_⟩
  rcases le_total T' t with h1 | h1
  · have := hT t ((le_max_left _ _).trans h1)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _)] at this
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (exp_pos _).le)
    exact (le_max_left _ _).trans (le_max_left _ _)
  · have h2 := hM t ⟨ht.le, h1⟩
    rw [Real.norm_eq_abs] at h2
    calc |F t| ≤ max M 0 := h2.trans (le_max_left _ _)
      _ ≤ max M 0 * (exp (p * T') * exp (-p * t)) := by
          refine le_mul_of_one_le_right (le_max_right _ _) ?_
          rw [← exp_add, one_le_exp_iff]
          nlinarith
      _ = (max M 0 * exp (p * T')) * exp (-p * t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (exp_pos _).le
lemma vii {f g : ℝ → ℝ} {p₁ p₂ C₁ C₂ : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂)
    (hf : ∀ t, 1 < t → f t ≤ C₁ * exp (-p₁ * t)) (hg : ∀ t, 1 < t → g t ≤ C₂ * exp (-p₂ * t)) :
    ∃ p C, 0 < p ∧ 0 ≤ C ∧ (∀ t, 1 < t → f t ≤ C * exp (-p * t)) ∧
      (∀ t, 1 < t → g t ≤ C * exp (-p * t)) := by
  refine ⟨min p₁ p₂, max C₁ C₂, lt_min hp₁ hp₂, le_max_of_le_left hC₁, fun t ht => ?_,
    fun t ht => ?_⟩
  · refine (hf t ht).trans (mul_le_mul (le_max_left _ _) (exp_le_exp.2 ?_) (exp_pos _).le
      (le_max_of_le_left hC₁))
    nlinarith [min_le_left p₁ p₂]
  · refine (hg t ht).trans (mul_le_mul (le_max_right _ _) (exp_le_exp.2 ?_) (exp_pos _).le
      (le_max_of_le_left hC₁))
    nlinarith [min_le_right p₁ p₂]
lemma vie (a : UnitAddCircle) : vaq (hurwitzEvenFEPair a).Λ₀ := by
  obtain ⟨p₁, hp₁, h₁⟩ := isBigO_atTop_evenKernel_sub a
  obtain ⟨p₂, hp₂, h₂⟩ := isBigO_atTop_cosKernel_sub a
  obtain ⟨C₁, hC₁, hb₁⟩ := veG
    ((continuousOn_evenKernel a).sub continuousOn_const) hp₁.le h₁
  obtain ⟨C₂, hC₂, hb₂⟩ := veG
    ((continuousOn_cosKernel a).sub continuousOn_const) hp₂.le h₂
  obtain ⟨p, C, hp, hC, hf, hg⟩ := vii hp₁ hp₂ hC₁ hC₂ hb₁ hb₂
  refine vhO _ hp hC (fun t ht => ?_) (fun t ht => ?_)
  · have : (hurwitzEvenFEPair a).f t - (hurwitzEvenFEPair a).f₀ =
        ((evenKernel a t - if a = 0 then 1 else 0 : ℝ) : ℂ) := by
      simp only [hurwitzEvenFEPair, Function.comp_apply]
      split_ifs <;> simp
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact hf t ht
  · have : (hurwitzEvenFEPair a).g t - (hurwitzEvenFEPair a).g₀ =
        ((cosKernel a t - 1 : ℝ) : ℂ) := by
      simp [hurwitzEvenFEPair]
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact hg t ht
lemma vdz (a : UnitAddCircle) :
    vaq (completedHurwitzZetaEven₀ a) := by
  refine (((vie a).comp (g := fun s => s / 2) le_rfl (fun s => ?_)).mul
    (vaq.const (1 / 2))).congr (fun s => ?_)
  · rw [norm_div, Complex.norm_two, add_zero]
    linarith [norm_nonneg s]
  · simp only [completedHurwitzZetaEven₀]; ring
end Erdos985.Analytic.XiOrderAux
end
section
open Complex
namespace Erdos985.Analytic
noncomputable def vai (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta₀ s + 1
theorem vbr : Differentiable ℂ vai := by
  unfold vai
  have := differentiable_completedZeta₀
  fun_prop
theorem vhe {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    vai s = s * (s - 1) * completedRiemannZeta s := by
  have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have h2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [vai, completedRiemannZeta_eq]
  field_simp
  ring
theorem vcv : vai 0 = 1 := by simp [vai]
open XiOrderAux in
theorem vgP {F : ℂ → ℂ} (hF : vaq F) :
    ∃ C : ℝ, ∀ s : ℂ, ‖F s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)) := by
  obtain ⟨K, a, b, ha, hb, h⟩ := hF
  have hK : 0 ≤ K := vaq.vgu h
  set lb := Real.log b
  have hlb : 0 ≤ lb := Real.log_nonneg (by linarith)
  set C₀ := a * (2 * lb + 1 + 2 * b)
  set D := a * (b * (lb + 1))
  refine ⟨max (K * Real.exp D) C₀, fun s => (h s).trans ?_⟩
  set u := ‖s‖
  have hu : 0 ≤ u := norm_nonneg s
  set ℓ := Real.log (u + 2)
  have hℓ2 : (1 / 2 : ℝ) ≤ ℓ := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hℓu : ℓ ≤ u + 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < u + 2 by linarith); linarith
  have hL : 0 ≤ u * ℓ := by positivity
  have h1 : Real.log (u + b) ≤ lb + ℓ := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have h2 : u ≤ 2 * (u * ℓ) := by nlinarith
  have key : a * ((u + b) * Real.log (u + b)) ≤ C₀ * (u * ℓ) + D := by
    have e : (u + b) * Real.log (u + b) ≤ (2 * lb + 1 + 2 * b) * (u * ℓ) + b * (lb + 1) := by
      calc (u + b) * Real.log (u + b) ≤ (u + b) * (lb + ℓ) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = lb * u + u * ℓ + b * lb + b * ℓ := by ring
        _ ≤ lb * (2 * (u * ℓ)) + u * ℓ + b * lb + b * (2 * (u * ℓ) + 1) := by
            gcongr; linarith
        _ = _ := by ring
    have := mul_le_mul_of_nonneg_left e ha
    simp only [C₀, D]; nlinarith
  calc K * Real.exp (a * ((u + b) * Real.log (u + b)))
      ≤ K * Real.exp (C₀ * (u * ℓ) + D) := by gcongr
    _ = K * Real.exp D * Real.exp (C₀ * (u * ℓ)) := by
        rw [Real.exp_add]; ring
    _ ≤ max (K * Real.exp D) C₀ * Real.exp (max (K * Real.exp D) C₀ * (u * ℓ)) :=
        mul_le_mul (le_max_left _ _)
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hL))
          (Real.exp_pos _).le (le_max_of_le_left (by positivity))
    _ = _ := by ring_nf
theorem vef :
    ∃ C : ℝ, ∀ s : ℂ, ‖vai s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)) := by
  open XiOrderAux in
  have hid : vaq (fun s : ℂ => s) := by
    refine ⟨1, 1, 3, zero_le_one, le_rfl, fun s => ?_⟩
    have h3 : 1 ≤ Real.log (‖s‖ + 3) := vcx (by linarith [norm_nonneg s])
    have := Real.add_one_le_exp ‖s‖
    have : ‖s‖ ≤ (‖s‖ + 3) * Real.log (‖s‖ + 3) := by nlinarith [norm_nonneg s]
    have : Real.exp ‖s‖ ≤ Real.exp (1 * ((‖s‖ + 3) * Real.log (‖s‖ + 3))) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  open XiOrderAux in
  have h : vaq vai :=
    (((hid.mul (hid.add (vaq.const (-1)))).mul
      (vdz 0)).add (vaq.const 1)).congr fun s => by
        simp only [vai, completedRiemannZeta₀]; ring
  exact vgP h
end Erdos985.Analytic
end

namespace DensityHypothesisH2

open Complex Real Set Metric MeasureTheory Filter MeromorphicOn

private lemma gammaR_analytic_and_ne_zero {s : ℂ} (him : 0 < s.im) :
    AnalyticAt ℂ Complex.Gammaℝ s ∧ Complex.Gammaℝ s ≠ 0 := by
  have hnotneg : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m hm
    have := congrArg Complex.im hm
    simp at this
    linarith
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hG_diff : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
    Complex.differentiableAt_Gamma (s / 2) hnotneg
  have hG_ne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hnotneg
  have hcpow_ne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hpi]
    exact Complex.exp_ne_zero _
  have hdiff_on : DifferentiableOn ℂ Complex.Gammaℝ {z : ℂ | 0 < z.im} := by
    intro z hz
    have hznot : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
      intro m hm
      have := congrArg Complex.im hm
      simp at this
      linarith [show (0 : ℝ) < z.im from hz]
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) z := by
      have harg : DifferentiableAt ℂ (fun w : ℂ => -w / 2) z := by fun_prop
      exact harg.const_cpow (Or.inl hpi)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) z :=
      (Complex.differentiableAt_Gamma (z / 2) hznot).comp z (by fun_prop)
    exact (h1.mul h2).differentiableWithinAt
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have han : AnalyticAt ℂ Complex.Gammaℝ s :=
    (hdiff_on.analyticOnNhd hopen) s him
  exact ⟨han, mul_ne_zero hcpow_ne hG_ne⟩

private lemma analyticOrderNatAt_zeta_eq_vai {s : ℂ} (him : 0 < s.im) :
    analyticOrderNatAt riemannZeta s = analyticOrderNatAt Erdos985.Analytic.vai s := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hnhds : {z : ℂ | 0 < z.im} ∈ nhds s := hopen.mem_nhds him
  have heq : Erdos985.Analytic.vai =ᶠ[nhds s]
      fun z => (z * (z - 1) * Complex.Gammaℝ z) * riemannZeta z := by
    filter_upwards [hnhds] with z hz
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz
    have hz1 : z ≠ 1 := by rintro rfl; simp at hz
    have hnotneg : ∀ n : ℕ, z ≠ -2 * (n : ℂ) := by
      intro n hn
      have := congrArg Complex.im hn
      simp at this
      linarith [show (0 : ℝ) < z.im from hz]
    have hGR_ne : Complex.Gammaℝ z ≠ 0 := (gammaR_analytic_and_ne_zero hz).2
    rw [Erdos985.Analytic.vhe hz0 hz1]
    have hzeta : riemannZeta z = completedRiemannZeta z / Complex.Gammaℝ z := by
      rw [riemannZeta_def_of_ne_zero hz0]
    rw [hzeta]
    field_simp [hGR_ne]
  have ⟨hGR_an, hGR_ne⟩ := gammaR_analytic_and_ne_zero him
  have hs0 : s ≠ 0 := by rintro rfl; simp at him
  have hs1 : s ≠ 1 := by rintro rfl; simp at him
  have hg_an : AnalyticAt ℂ (fun z : ℂ => z * (z - 1) * Complex.Gammaℝ z) s :=
    ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul hGR_an)
  have hg_ne : s * (s - 1) * Complex.Gammaℝ s ≠ 0 :=
    mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) hGR_ne
  have hzeta_an : AnalyticAt ℂ riemannZeta s := by
    have hdiff_on : DifferentiableOn ℂ riemannZeta {z : ℂ | 0 < z.im} := by
      intro z hz
      have hz1 : z ≠ 1 := by rintro rfl; simp at hz
      exact (differentiableAt_riemannZeta hz1).differentiableWithinAt
    exact (hdiff_on.analyticOnNhd hopen) s him
  have hord_g : analyticOrderAt (fun z : ℂ => z * (z - 1) * Complex.Gammaℝ z) s = 0 :=
    hg_an.analyticOrderAt_eq_zero.mpr hg_ne
  have hord_eq : analyticOrderAt Erdos985.Analytic.vai s = analyticOrderAt riemannZeta s := by
    have hmul : analyticOrderAt ((fun z : ℂ => z * (z - 1) * Complex.Gammaℝ z) * riemannZeta) s =
        analyticOrderAt (fun z : ℂ => z * (z - 1) * Complex.Gammaℝ z) s +
          analyticOrderAt riemannZeta s :=
      analyticOrderAt_mul hg_an hzeta_an
    have heq' : Erdos985.Analytic.vai =ᶠ[nhds s]
        ((fun z : ℂ => z * (z - 1) * Complex.Gammaℝ z) * riemannZeta) := heq
    rw [analyticOrderAt_congr heq', hmul, hord_g, zero_add]
  simp only [analyticOrderNatAt, hord_eq]

private lemma vai_divisor_eq_orderNat (s : ℂ) :
    MeromorphicOn.divisor Erdos985.Analytic.vai (Set.univ : Set ℂ) s =
      (analyticOrderNatAt Erdos985.Analytic.vai s : ℤ) := by
  have hmon : MeromorphicOn Erdos985.Analytic.vai (Set.univ : Set ℂ) :=
    fun z _ => (Erdos985.Analytic.vbr.analyticAt z).meromorphicAt
  rw [MeromorphicOn.divisor_apply hmon (Set.mem_univ s)]
  have han : AnalyticAt ℂ Erdos985.Analytic.vai s := Erdos985.Analytic.vbr.analyticAt s
  have hneTop : analyticOrderAt Erdos985.Analytic.vai s ≠ ⊤ := by
    have hnot : ∃ z : ℂ, Erdos985.Analytic.vai z ≠ 0 := ⟨0, by rw [Erdos985.Analytic.vcv]; exact one_ne_zero⟩
    obtain ⟨z1, hz1⟩ := hnot
    have hz1_nt : analyticOrderAt Erdos985.Analytic.vai z1 ≠ ⊤ := by
      rw [(Erdos985.Analytic.vbr.analyticAt z1).analyticOrderAt_eq_zero.mpr hz1]
      simp
    exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
      (Erdos985.Analytic.vbr.differentiableOn.analyticOnNhd isOpen_univ)
      isPreconnected_univ (Set.mem_univ z1) (Set.mem_univ s) hz1_nt
  rw [han.meromorphicOrderAt_eq (𝕜 := ℂ)]
  have hcast : (analyticOrderNatAt Erdos985.Analytic.vai s : ℕ∞) =
      analyticOrderAt Erdos985.Analytic.vai s :=
    Nat.cast_analyticOrderNatAt hneTop
  rw [← hcast]
  simp

private lemma zeroCountOn_le_vbe {T : ℝ} (hT : 2 ≤ T) :
    (Complex.zeroCountOn riemannZeta
      {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 < s.im ∧ s.im ≤ T} : ℝ) ≤
      Function.locallyFinsuppWithin.vbe
        (MeromorphicOn.divisor Erdos985.Analytic.vai (Set.univ : Set ℂ)) (T + 1) := by
  classical
  set S : Set ℂ := {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 < s.im ∧ s.im ≤ T}
  set R : ℝ := T + 1
  set D := MeromorphicOn.divisor Erdos985.Analytic.vai (Set.univ : Set ℂ)
  have hRpos : 0 < R := by dsimp [R]; linarith
  have hfin : {s ∈ S | riemannZeta s = 0}.Finite :=
    (DensityHypothesis.zetaZeroSet_finite 0 T).subset fun s hs =>
      ⟨hs.1.1, hs.1.2.1, hs.1.2.2.1, hs.1.2.2.2, hs.2⟩
  rw [← Complex.zeroCountOn_sep_eq_zero riemannZeta S]
  unfold Complex.zeroCountOn
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  push_cast
  let F1 : Finset ℂ := hfin.toFinset.filter (fun s => analyticOrderNatAt riemannZeta s ≠ 0)
  have hsum_eq :
      ∑ s ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta s : ℝ) =
      ∑ s ∈ F1, (analyticOrderNatAt riemannZeta s : ℝ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro s _ hsnot
    simp only [F1, Finset.mem_filter, not_and, not_not] at hsnot
    have h0 := hsnot (by assumption)
    simp [h0]
  rw [hsum_eq]
  set F2 : Finset ℂ :=
    ((Function.locallyFinsuppWithin.finiteSupport
      (Function.locallyFinsuppWithin.toClosedBall R D)
      (isCompact_closedBall (0 : ℂ) |R|)).toFinset).filter (fun z => z ≠ (0 : ℂ))
  have hsub : F1 ⊆ F2 := by
    intro s hs
    simp only [F1, Finset.mem_filter, Set.Finite.mem_toFinset] at hs
    obtain ⟨⟨hsS, _⟩, hord_ne⟩ := hs
    have hs0 : s ≠ 0 := by
      rintro rfl
      have hpos : (0 : ℝ) < (0 : ℂ).im := hsS.2.2.1
      simp at hpos
    have hnorm : ‖s‖ ≤ |R| := by
      rw [abs_of_pos hRpos, Complex.norm_def]
      have hsq : Complex.normSq s ≤ R ^ 2 := by
        rw [Complex.normSq_apply]
        dsimp [R]
        nlinarith [hsS.1, hsS.2.1, hsS.2.2.1, hsS.2.2.2]
      calc Real.sqrt (Complex.normSq s) ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt hsq
        _ = R := Real.sqrt_sq hRpos.le
    have hord_vai : analyticOrderNatAt Erdos985.Analytic.vai s ≠ 0 := by
      rwa [← analyticOrderNatAt_zeta_eq_vai hsS.2.2.1]
    have hDs : s ∈ D.support := by
      rw [Function.mem_support, vai_divisor_eq_orderNat]
      exact_mod_cast hord_vai
    have hmem_ball : s ∈ (Function.locallyFinsuppWithin.toClosedBall R D).support :=
      Function.locallyFinsuppWithin.vaW hDs hnorm
    exact Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr hmem_ball, hs0⟩
  have hterm : ∀ s ∈ F1, (analyticOrderNatAt riemannZeta s : ℝ) = (D s : ℝ) := by
    intro s hs
    simp only [F1, Finset.mem_filter, Set.Finite.mem_toFinset] at hs
    rw [analyticOrderNatAt_zeta_eq_vai hs.1.1.2.2.1, vai_divisor_eq_orderNat]
    norm_cast
  have hDnonneg : 0 ≤ D := Differentiable.divisor_nonneg Erdos985.Analytic.vbr
  calc ∑ s ∈ F1, (analyticOrderNatAt riemannZeta s : ℝ)
      = ∑ s ∈ F1, (D s : ℝ) := Finset.sum_congr rfl hterm
    _ ≤ ∑ s ∈ F2, (D s : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ => by exact_mod_cast hDnonneg z
    _ = Function.locallyFinsuppWithin.vbe D R := rfl

theorem main_proof : OMA.R_DensityHypothesis_density_hypothesis_zeta_zeros_R1.H2 := by
  obtain ⟨C₀, hC₀⟩ := Erdos985.Analytic.vef
  set C₁ : ℝ := max C₀ 1
  have hC₁ : 1 ≤ C₁ := le_max_right _ _
  have hC₁pos : 0 < C₁ := by linarith
  set Ctrail : ℝ := |Real.log ‖meromorphicTrailingCoeffAt Erdos985.Analytic.vai 0‖|
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  set M : ℝ := (Real.log (2 * C₁) + 9 * C₁ + Ctrail + 1) / Real.log 2
  have hMpos : 0 < M := by
    have h1 : 0 ≤ Real.log (2 * C₁) := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ Ctrail := abs_nonneg _
    dsimp [M]
    positivity
  refine ⟨M, hMpos, fun T hT => ?_⟩
  set R : ℝ := T + 1
  have hR1 : 1 ≤ R := by dsimp [R]; linarith
  have hRpos : 0 < R := by linarith
  have h2Rpos : 0 < 2 * R := by linarith
  have hcnt := zeroCountOn_le_vbe hT
  have hlow : Real.log 2 *
      Function.locallyFinsuppWithin.vbe
        (MeromorphicOn.divisor Erdos985.Analytic.vai (Set.univ : Set ℂ)) R ≤
      Function.locallyFinsuppWithin.logCounting
        (MeromorphicOn.divisor Erdos985.Analytic.vai (Set.univ : Set ℂ)) (2 * R) :=
    Function.locallyFinsuppWithin.vcz
      (Differentiable.divisor_nonneg Erdos985.Analytic.vbr) hR1
  have hEq := Function.locallyFinsuppWithin.vbo Erdos985.Analytic.vbr h2Rpos.ne'
  have hf_sphere : MeromorphicOn Erdos985.Analytic.vai (sphere (0 : ℂ) |2 * R|) :=
    fun z _ => (Erdos985.Analytic.vbr.analyticAt z).meromorphicAt
  have hInt : CircleIntegrable (fun z : ℂ => Real.log ‖Erdos985.Analytic.vai z‖) 0 (2 * R) :=
    MeromorphicOn.circleIntegrable_log_norm hf_sphere
  set B : ℝ := Real.log (2 * C₁) + C₁ * (2 * R) * Real.log (2 * R + 2)
  have hbound_circle : ∀ z ∈ sphere (0 : ℂ) |2 * R|,
      Real.log ‖Erdos985.Analytic.vai z‖ ≤ B := by
    intro z hz
    have hzn : ‖z‖ = 2 * R := by
      have := mem_sphere.mp hz
      rw [dist_zero_right, abs_of_pos h2Rpos] at this
      exact this
    have h1 : ‖Erdos985.Analytic.vai z‖ ≤ C₁ * Real.exp (C₁ * (2 * R) * Real.log (2 * R + 2)) := by
      have h0 := hC₀ z
      rw [hzn] at h0
      have hL : 0 ≤ (2 * R) * Real.log (2 * R + 2) := by
        have : 0 ≤ Real.log (2 * R + 2) := Real.log_nonneg (by linarith)
        positivity
      have hC0_le : C₀ ≤ C₁ := le_max_left _ _
      calc ‖Erdos985.Analytic.vai z‖
          ≤ C₀ * Real.exp (C₀ * (2 * R) * Real.log (2 * R + 2)) := h0
        _ ≤ C₁ * Real.exp (C₁ * (2 * R) * Real.log (2 * R + 2)) := by
            have hE : Real.exp (C₀ * (2 * R) * Real.log (2 * R + 2)) ≤
                Real.exp (C₁ * (2 * R) * Real.log (2 * R + 2)) :=
              Real.exp_le_exp.mpr (by nlinarith)
            have hC0_nn : 0 ≤ C₀ := by
              have := (norm_nonneg (Erdos985.Analytic.vai 0)).trans (hC₀ 0)
              have hpos : 0 < Real.exp (C₀ * ‖(0 : ℂ)‖ * Real.log (‖(0 : ℂ)‖ + 2)) := Real.exp_pos _
              exact nonneg_of_mul_nonneg_left this hpos
            exact mul_le_mul hC0_le hE (Real.exp_pos _).le hC₁pos.le
    have h2 : 1 + ‖Erdos985.Analytic.vai z‖ ≤
        (2 * C₁) * Real.exp (C₁ * (2 * R) * Real.log (2 * R + 2)) := by
      have hE1 : 1 ≤ Real.exp (C₁ * (2 * R) * Real.log (2 * R + 2)) := by
        rw [Real.one_le_exp_iff]
        have : 0 ≤ Real.log (2 * R + 2) := Real.log_nonneg (by linarith)
        positivity
      nlinarith
    calc Real.log ‖Erdos985.Analytic.vai z‖
        ≤ Real.log (1 + ‖Erdos985.Analytic.vai z‖) := Real.veO _
      _ ≤ Real.log ((2 * C₁) * Real.exp (C₁ * (2 * R) * Real.log (2 * R + 2))) :=
          Real.log_le_log (by positivity) h2
      _ = B := by
          rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  have hCircleAvg_le :
      circleAverage (fun z : ℂ => Real.log ‖Erdos985.Analytic.vai z‖) 0 (2 * R) ≤ B :=
    circleAverage_mono_on_of_le_circle (c := (0 : ℂ)) (R := 2 * R)
      (f := fun z => Real.log ‖Erdos985.Analytic.vai z‖) hInt hbound_circle
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hTlogT_ge1 : 1 ≤ T * Real.log T := by
    have := Real.log_two_gt_d9
    nlinarith
  have h2R_le : 2 * R ≤ 3 * T := by dsimp [R]; linarith
  have hlog_2R2 : Real.log (2 * R + 2) ≤ 3 * Real.log T := by
    have hT2 : 4 ≤ T ^ 2 := by nlinarith
    have hpow : 2 * R + 2 ≤ T ^ 3 := by dsimp [R]; nlinarith
    calc Real.log (2 * R + 2) ≤ Real.log (T ^ 3) := Real.log_le_log (by linarith) hpow
      _ = 3 * Real.log T := by rw [Real.log_pow]; norm_num
  have hB_le : B + Ctrail ≤ (Real.log (2 * C₁) + 9 * C₁ + Ctrail + 1) * (T * Real.log T) := by
    have h1 : C₁ * (2 * R) * Real.log (2 * R + 2) ≤ 9 * C₁ * (T * Real.log T) := by
      have hlogR_nn : 0 ≤ Real.log (2 * R + 2) := Real.log_nonneg (by linarith)
      have hlogT_nn : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
      have hm1 : (2 * R) * Real.log (2 * R + 2) ≤ (3 * T) * (3 * Real.log T) :=
        mul_le_mul h2R_le hlog_2R2 hlogR_nn (by linarith)
      nlinarith
    have h2 : 0 ≤ Real.log (2 * C₁) := Real.log_nonneg (by linarith)
    have h3 : 0 ≤ Ctrail := abs_nonneg _
    dsimp [B]
    nlinarith
  have hupp :
      Function.locallyFinsuppWithin.logCounting
        (MeromorphicOn.divisor Erdos985.Analytic.vai (Set.univ : Set ℂ)) (2 * R) ≤ B + Ctrail := by
    have hEq' :
        Function.locallyFinsuppWithin.logCounting
          (MeromorphicOn.divisor Erdos985.Analytic.vai (Set.univ : Set ℂ)) (2 * R) =
        circleAverage (fun x => Real.log ‖Erdos985.Analytic.vai x‖) 0 (2 * R) -
          Real.log ‖meromorphicTrailingCoeffAt Erdos985.Analytic.vai 0‖ := by
      simpa [top_eq_univ] using hEq
    rw [hEq']
    have hneg : -Real.log ‖meromorphicTrailingCoeffAt Erdos985.Analytic.vai 0‖ ≤ Ctrail :=
      neg_le_abs _
    linarith
  have hfinal :
      Function.locallyFinsuppWithin.vbe
        (MeromorphicOn.divisor Erdos985.Analytic.vai (Set.univ : Set ℂ)) R ≤
        M * T * Real.log T := by
    have hmul :
        Function.locallyFinsuppWithin.vbe
          (MeromorphicOn.divisor Erdos985.Analytic.vai (Set.univ : Set ℂ)) R * Real.log 2 ≤
          (Real.log (2 * C₁) + 9 * C₁ + Ctrail + 1) * (T * Real.log T) := by
      linarith
    have hdiv := (le_div_iff₀ hlog2pos).mpr hmul
    have heqM :
        (Real.log (2 * C₁) + 9 * C₁ + Ctrail + 1) * (T * Real.log T) / Real.log 2 =
          M * T * Real.log T := by
      dsimp [M]; ring
    exact hdiv.trans_eq heqM
  exact hcnt.trans hfinal

end DensityHypothesisH2

theorem OMA.solution : OMA.R_DensityHypothesis_density_hypothesis_zeta_zeros_R1.H2 :=
  DensityHypothesisH2.main_proof

