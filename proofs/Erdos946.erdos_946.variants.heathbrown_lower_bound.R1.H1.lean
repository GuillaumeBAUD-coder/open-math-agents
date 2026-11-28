import OMAReductions.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1
import Mathlib

-- Proof of Erdos946.erdos_946.variants.heathbrown_lower_bound.R1.H1
-- Seven-dimensional Richert weighted sieve with Selberg upper bound + Rankin trick,
-- exact CRT inclusion-exclusion + Buchstab telescoping, and 8 rational bins,
-- combined with the CRT progression and large-prime-square removal from upstream children.
-- Mertens block ported from PrimeNumberTheoremAnd (Apache-2.0, @marcusbuffett / Erdos694).
-- Upstream child reductions/proofs credited to their authors (@justusklocke-cloud et al.).

-- Port of the PrimeNumberTheoremAnd project contributors,
-- AlexKontorovich/PrimeNumberTheoremAnd at 55270df80721, Apache-2.0.
-- Mertens contributions include Terence Tao, A. J. Irving, Giuseppe Sorge,
-- Robby Sneiderman and Yan Yablonovskiy. The comparison uses the reciprocal product.
-- The last step inverts the standard prime product to match the target.
-- Credit: @marcusbuffett

section
open Finset Interval MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

end

section
theorem Filter.EventuallyEq.iff_eventually {α : Type _} {β : Type _} {l : Filter α} {f g : α → β} : f =ᶠ[l] g ↔ ∀ᶠ (x : α) in l, f x = g x := by rfl

namespace Real

open Filter Asymptotics

theorem inv_log_eq_o_one : (fun x ↦ 1 / log x) =o[atTop] (fun _ ↦ (1:ℝ)) := by
    rw [isLittleO_one_iff]
    convert tendsto_log_atTop.inv_tendsto_atTop using 1
    ext; simp

end Real

section Issue1584
open MeasureTheory Set Filter Topology

private lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun v : ℝ => Real.log v * Real.exp (-v)) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  · 
    have hlog : IntegrableOn (fun v : ℝ => Real.log v) (Ioc 0 1) volume := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)] at this
    apply Integrable.mono' hlog.norm
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      have h2 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hv.1])
      rw [h1]
      nlinarith [abs_nonneg (Real.log v), Real.exp_pos (-v)]
  · 
    have hexp : IntegrableOn (fun v : ℝ => (2 : ℝ) * Real.exp ((-1/2) * v)) (Ioi 1) volume := by
      exact (integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0) 1).const_mul 2
    apply Integrable.mono' hexp
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
      have hv1 : (1 : ℝ) ≤ v := le_of_lt hv
      have hvpos : (0 : ℝ) < v := by linarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hlogabs : |Real.log v| = Real.log v :=
        abs_of_nonneg (Real.log_nonneg hv1)
      have hexpabs : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      rw [hlogabs, hexpabs]
      
      have hlogv : Real.log v ≤ v := (Real.log_le_sub_one_of_pos hvpos).trans (by linarith)
      
      have hvexp : v ≤ 2 * Real.exp (v/2) := by
        have := Real.add_one_le_exp (v/2)
        nlinarith [Real.exp_pos (v/2)]
      
      have hstep : Real.log v * Real.exp (-v) ≤ 2 * Real.exp (v/2) * Real.exp (-v) := by
        apply mul_le_mul_of_nonneg_right (hlogv.trans hvexp) (le_of_lt (Real.exp_pos _))
      have heq : 2 * Real.exp (v/2) * Real.exp (-v) = 2 * Real.exp ((-1/2) * v) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
      rw [heq] at hstep
      exact hstep

private lemma integral_log_mul_exp_neg_eq_deriv_Gamma :
    ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) = deriv Real.Gamma 1 := by
  set I : ℝ := ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) with hI
  
  have h1 := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)
  
  have hval : (∫ t : ℝ in Ioi 0, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t))))
      = (I : ℂ) := by
    have key : ∀ t : ℝ, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t)))
        = ((Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
      intro t
      rw [sub_self, Complex.cpow_zero, one_mul, Complex.ofReal_mul]
    simp_rw [key]
    rw [integral_complex_ofReal, hI]
  rw [hval] at h1
  
  have h2 : HasDerivAt Complex.Gamma (I : ℂ) 1 := by
    apply h1.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0:ℝ) < (1:ℂ).re by norm_num)] with z hz
    exact Complex.Gamma_eq_integral hz
  
  have h3 := h2.real_of_complex
  have h4 : HasDerivAt Real.Gamma I 1 := by
    have hcongr : (fun x : ℝ => (Complex.Gamma ↑x).re) = Real.Gamma := by
      funext x
      rw [Complex.Gamma_ofReal, Complex.ofReal_re]
    rw [hcongr, Complex.ofReal_re] at h3
    exact h3
  rw [← h4.deriv]

private theorem mul_integ_log_log_eq_aux (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) =
      - Real.log (s - 1) + deriv Real.Gamma 1 := by
  have hs0 : 0 < s - 1 := by linarith
  set f : ℝ → ℝ := fun x => (s - 1) * Real.log x with hf_def
  set f' : ℝ → ℝ := fun x => (s - 1) / x with hf'_def
  set g : ℝ → ℝ := fun u => (Real.log u - Real.log (s - 1)) * Real.exp (-u) with hg_def
  
  have hf1 : f 1 = 0 := by simp [hf_def]
  
  have hf_cont : ContinuousOn f (Ici 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply Real.continuousOn_log.mono
    intro x hx
    simp only [mem_Ici] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  
  have hft : Tendsto f atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop hs0
    exact Real.tendsto_log_atTop
  
  have hff' : ∀ x ∈ Ioi (1:ℝ), HasDerivWithinAt f (f' x) (Ioi x) x := by
    intro x hx
    simp only [mem_Ioi] at hx
    have hxne : x ≠ 0 := by linarith
    have := (Real.hasDerivAt_log hxne).const_mul (s - 1)
    have h2 : HasDerivAt f ((s - 1) * x⁻¹) x := this
    have : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
    rw [this] at h2
    exact h2.hasDerivWithinAt
  
  have hmono : StrictMonoOn f (Ici 1) := by
    intro a ha b hb hab
    simp only [mem_Ici] at ha hb
    apply mul_lt_mul_of_pos_left _ hs0
    exact Real.log_lt_log (by linarith) hab
  have himg_Ioi : f '' Ioi 1 = Ioi 0 := by
    ext y
    simp only [Set.mem_image, mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 < Real.log x := Real.log_pos hx
      positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_lt_exp_iff.mpr (div_pos hy hs0)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  have himg_Ici : f '' Ici 1 = Ici 0 := by
    ext y
    simp only [Set.mem_image, mem_Ici]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 ≤ Real.log x := Real.log_nonneg hx
      rw [hf_def]; positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_le_exp_iff.mpr (div_nonneg hy hs0.le)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  
  have hg_cont : ContinuousOn g (f '' Ioi 1) := by
    rw [himg_Ioi]
    apply ContinuousOn.mul
    · apply ContinuousOn.sub _ continuousOn_const
      apply Real.continuousOn_log.mono
      intro u hu
      simp only [mem_Ioi] at hu
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith
    · exact (Real.continuous_exp.comp continuous_neg).continuousOn
  
  have hg1 : IntegrableOn g (f '' Ici 1) := by
    rw [himg_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have : g = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [this]
    exact e1.sub e2
  
  have hg2 : IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici 1) := by
    
    have hff'_Ici : ∀ x ∈ Ici (1:ℝ), HasDerivWithinAt f (f' x) (Ici 1) x := by
      intro x hx
      simp only [mem_Ici] at hx
      have hxne : x ≠ 0 := by linarith
      have hd : HasDerivAt f ((s - 1) * x⁻¹) x := (Real.hasDerivAt_log hxne).const_mul (s - 1)
      have heq : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
      rw [heq] at hd
      exact hd.hasDerivWithinAt
    
    have hinj : InjOn f (Ici 1) := hmono.injOn
    
    have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Ici (1:ℝ)) (f := f) (f' := f') measurableSet_Ici hff'_Ici hinj g
    rw [hiff] at hg1
    
    apply hg1.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    simp only [mem_Ici] at hx
    have hxpos : (0:ℝ) < x := by linarith
    have hf'pos : 0 < f' x := by rw [hf'_def]; positivity
    simp only [smul_eq_mul, Function.comp, abs_of_pos hf'pos]
    ring
  
  have hcov := integral_comp_mul_deriv_Ioi hf_cont hft hff' hg_cont hg1 hg2
  rw [hf1] at hcov
  
  have hrhs : ∫ u in Ioi (0:ℝ), g u = deriv Real.Gamma 1 - Real.log (s - 1) := by
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have hsplit : (fun u => g u)
        = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [show (∫ u in Ioi (0:ℝ), g u)
        = ∫ u in Ioi (0:ℝ), (Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u))
        from by rw [hsplit]]
    rw [integral_sub e1 e2, integral_log_mul_exp_neg_eq_deriv_Gamma]
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  
  have hlhs : ∫ x in Ioi (1:ℝ), (g ∘ f) x * f' x
      = (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) := by
    have hpt : ∀ x ∈ Ioi (1:ℝ), (g ∘ f) x * f' x
        = (s - 1) * (Real.log (Real.log x) * x ^ (-s)) := by
      intro x hx
      simp only [mem_Ioi] at hx
      have hxpos : (0:ℝ) < x := by linarith
      have hlogpos : 0 < Real.log x := Real.log_pos hx
      have hlogne : Real.log x ≠ 0 := ne_of_gt hlogpos
      have hs1ne : s - 1 ≠ 0 := ne_of_gt hs0
      simp only [Function.comp, hf_def, hg_def, hf'_def]
      
      rw [Real.log_mul hs1ne hlogne]
      
      have hexp : Real.exp (-((s - 1) * Real.log x)) = x ^ (-(s - 1)) := by
        rw [Real.rpow_def_of_pos hxpos]
        ring_nf
      rw [hexp]
      
      have hx1 : x ^ (-(s - 1)) * ((s - 1) / x) = (s - 1) * x ^ (-s) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one x]
        rw [show x ^ (-(s - 1)) * ((s - 1) * x ^ (-1 : ℝ))
            = (s - 1) * (x ^ (-(s - 1)) * x ^ (-1 : ℝ)) by ring]
        rw [← Real.rpow_add hxpos]
        ring_nf
      rw [show (Real.log (s - 1) + Real.log (Real.log x) - Real.log (s - 1))
          = Real.log (Real.log x) by ring]
      linear_combination Real.log (Real.log x) * hx1
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  rw [hlhs, hrhs] at hcov
  rw [hcov]
  ring

end Issue1584

namespace Mertens

open Real Finset Filter Asymptotics Topology
open ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa

theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]

theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

theorem sum_mangoldt_div_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d = log x + E₁Λ x := by
    grind

theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring

theorem sum_mangoldt_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x| ≤ log 4 + 4 := by
  grind [E₁Λ.le hx, E₁Λ.ge hx, log_nonneg]

theorem E₁Λ.bounded' : ∃ c > 0, ∀ x ≥ 1, |E₁Λ x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun x hx ↦ sum_mangoldt_div_eq_log hx⟩

theorem E₁Λ.bounded : E₁Λ =O[atTop] (fun _ ↦ (1:ℝ)) := by
  simp only [isBigO_iff, norm_eq_abs, norm_one, mul_one,
    eventually_atTop]
  exact ⟨log 4 + 4, 1, fun _ hx ↦ sum_mangoldt_div_eq_log hx⟩

noncomputable abbrev E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]

noncomputable abbrev E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp; linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all; linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! summable_nat_add_iff 1|>.mpr this using 2
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq

theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast; ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]

theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩

noncomputable abbrev γ : ℝ := (∫ t in Set.Ioi 2, E₁Λ t / (t * log t^2)) + 1 - log (log 2)

noncomputable abbrev E₂Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ

lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)


private theorem integrable_E₁Λ_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁Λ x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁Λ.bounded'
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

private theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)

theorem E₂Λ.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂Λ x = E₁Λ x / log x - ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) := by
  unfold E₂Λ
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  conv => lhs; arg 1; arg 1; arg 2; ext n; rw [(by field : Λ n / (n * log n) = (Λ n / n) / log n)]
  rw [sum_div_log_eq hx]
  rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, Λ n / n) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁Λ t / (t * log t ^ 2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold γ
    calc
    _ = E₁Λ x / log x + (∫ (x : ℝ) in 2..x, E₁Λ x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁Λ t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁Λ_div_mul_log_sq (by rfl)) (integrable_E₁Λ_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁Λ_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp

theorem E₂Λ.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂Λ.eq hx, abs_le']
    constructor
    · grw [E₁Λ.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≥ - 2 / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2) hx)
            (integrable_E₁Λ_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2) hx
      grw [this]
      grind
    grw [E₁Λ.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁Λ_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind

theorem E₂Λ.bound : E₂Λ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6, 2
    intro x hx
    convert E₂Λ.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]

theorem E₂Λ.bound' : E₂Λ =o[atTop] (fun _ ↦ (1:ℝ)) := E₂Λ.bound.trans_isLittleO inv_log_eq_o_one

theorem log_zeta_eq_sum (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = ∑' n, Λ n / (n^s * log n) := by
  have hsc : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  
  have hep := riemannZeta_eulerProduct_exp_log (s := (s : ℂ)) hsc
  set S : ℂ := ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) with hS
  
  have hcpow : ∀ p : Nat.Primes, (p : ℂ) ^ (-(s : ℂ)) = (((p : ℝ) ^ (-s) : ℝ) : ℂ) := by
    intro p
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  
  set z : Nat.Primes → ℝ := fun p => (p : ℝ) ^ (-s) with hz
  
  have hz_pos : ∀ p : Nat.Primes, 0 < z p := fun p => by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
    positivity
  have hz_lt_one : ∀ p : Nat.Primes, z p < 1 := by
    intro p
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    change (p : ℝ) ^ (-s) < 1
    rw [Real.rpow_neg (by positivity), inv_lt_one_iff₀]
    right
    exact (Real.one_lt_rpow_iff_of_pos (by positivity)).mpr (Or.inl ⟨hp1, by linarith⟩)
  
  have hterm : ∀ p : Nat.Primes,
      -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) = ((-Real.log (1 - z p) : ℝ) : ℂ) := by
    intro p
    rw [hcpow p]
    have h1z : (0 : ℝ) < 1 - z p := by have := hz_lt_one p; linarith
    rw [show (1 : ℂ) - ((z p : ℝ) : ℂ) = (((1 - z p : ℝ)) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_log h1z.le]
    push_cast; ring
  
  set Sr : ℝ := ∑' p : Nat.Primes, -Real.log (1 - z p) with hSr
  have hSeq : S = (Sr : ℂ) := by
    rw [hS, hSr, Complex.ofReal_tsum]
    exact tsum_congr hterm
  have hSim : S.im = 0 := by rw [hSeq]; exact Complex.ofReal_im _
  have hSre : S.re = Sr := by rw [hSeq]; exact Complex.ofReal_re _
  
  have hlog_zeta : Complex.log (riemannZeta (s : ℂ)) = S := by
    rw [← hep, Complex.log_exp (by rw [hSim]; exact neg_lt_zero.mpr Real.pi_pos)
      (by rw [hSim]; exact Real.pi_pos.le)]
  
  have hkey : Real.log (riemannZeta (s : ℂ)).re = Sr := by
    have hζim : (riemannZeta (s : ℂ)).im = 0 := riemannZeta_im_eq_zero_of_one_lt hs
    have hζeq : riemannZeta (s : ℂ) = ((riemannZeta (s : ℂ)).re : ℂ) := by
      apply Complex.ext <;> simp [hζim]
    have : Real.log (riemannZeta (s : ℂ)).re
        = (Complex.log (riemannZeta (s : ℂ))).re := by
      conv_rhs => rw [hζeq]
      rw [Complex.log_ofReal_re]
    rw [this, hlog_zeta, hSre]
  rw [hkey]

  have habs : ∀ p : Nat.Primes, |z p| < 1 := by
    intro p
    rw [abs_of_pos (hz_pos p)]; exact hz_lt_one p
  have htaylor : ∀ p : Nat.Primes,
      HasSum (fun n : ℕ => (z p) ^ (n + 1) / (n + 1)) (-Real.log (1 - z p)) :=
    fun p => hasSum_pow_div_log_of_abs_lt_one (habs p)
  have hSr_double : Sr = ∑' (p : Nat.Primes) (n : ℕ), (z p) ^ (n + 1) / (n + 1) := by
    rw [hSr]
    exact tsum_congr fun p => ((htaylor p).tsum_eq).symm
  
  have hsummable_z : Summable z := Nat.Primes.summable_rpow.mpr (by linarith)
  
  have hsummable_prime : Summable (fun p : Nat.Primes => -Real.log (1 - z p)) := by
    have := Real.summable_log_one_add_of_summable hsummable_z.neg
    convert! this.neg using 1
  
  have hg_nonneg : ∀ pk : Nat.Primes × ℕ, 0 ≤ (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1) := by
    intro pk; positivity [hz_pos pk.1]
  have hsummable_g : Summable (fun pk : Nat.Primes × ℕ => (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1)) := by
    rw [summable_prod_of_nonneg hg_nonneg]
    refine ⟨fun p => (htaylor p).summable, ?_⟩
    refine hsummable_prime.congr (fun p => ?_)
    exact ((htaylor p).tsum_eq).symm
  
  have hpoint : ∀ (p : Nat.Primes) (n : ℕ),
      Λ ((p : ℕ) ^ (n + 1)) /
        ((((p : ℕ) ^ (n + 1) : ℕ) : ℝ) ^ s * Real.log (((p : ℕ) ^ (n + 1) : ℕ) : ℝ))
      = (z p) ^ (n + 1) / (n + 1) := by
    intro p n
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
    rw [vonMangoldt_apply_pow (Nat.succ_ne_zero n), vonMangoldt_apply_prime p.prop]
    have hcast : (((p : ℕ) ^ (n + 1) : ℕ) : ℝ) = (p : ℝ) ^ (n + 1) := by push_cast; ring
    rw [hcast, Real.log_pow]
    rw [show (z p) ^ (n + 1) = ((p : ℝ) ^ (n + 1)) ^ (-s) by
      rw [hz]; rw [← Real.rpow_natCast ((p : ℝ) ^ (-s)) (n + 1),
        ← Real.rpow_natCast ((p : ℝ)) (n + 1), ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul (by positivity)]; ring_nf]
    rw [Real.rpow_neg (by positivity)]
    field_simp
    push_cast
    ring
  
  set F : ℕ → ℝ := fun n => Λ n / ((n : ℝ) ^ s * Real.log n) with hF
  
  have hsupp : Function.support F ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    rw [Function.mem_support] at hn
    simp only [Set.mem_setOf_eq]
    by_contra hpp
    apply hn
    simp only [hF, vonMangoldt_eq_zero_iff.mpr hpp, zero_div]
  
  have hprod_eq : (∑' pk : Nat.Primes × ℕ, (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1))
      = ∑' m : {n : ℕ // IsPrimePow n}, F m.val := by
    rw [← Equiv.tsum_eq Nat.Primes.prodNatEquiv (fun m : {n : ℕ // IsPrimePow n} => F m.val)]
    apply tsum_congr
    intro pk
    rw [Nat.Primes.coe_prodNatEquiv_apply, hF]
    exact (hpoint pk.1 pk.2).symm
  
  rw [hSr_double, ← hsummable_g.tsum_prod' (fun p => (htaylor p).summable), hprod_eq]
  exact tsum_subtype_eq_of_support_subset hsupp

section
open MeasureTheory Set

namespace LogZetaInteg

private noncomputable def c (d : ℕ) : ℝ := Λ d / (d * Real.log d)

private noncomputable def f (s : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
    c d * (Set.Ici (d:ℝ)).indicator (fun x => x ^ (-s)) x

@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]

private lemma c_nonneg (d : ℕ) : 0 ≤ c d := by
  unfold c
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  · apply div_nonneg vonMangoldt_nonneg
    have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    have hlog : 0 ≤ Real.log d := Real.log_natCast_nonneg d
    positivity

private lemma summable_log_rpow_div_rpow (a : ℝ) {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => (Real.log n) ^ a / (n:ℝ) ^ s) := by
  have hε : (0:ℝ) < (s - 1) / 2 := by linarith
  refine summable_of_isBigO_nat (g := fun n : ℕ => (n:ℝ) ^ ((s - 1) / 2 - s)) ?_ ?_
  · rw [Real.summable_nat_rpow]; linarith
  · have ho : (fun x : ℝ => (Real.log x) ^ a) =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2)) :=
      (isLittleO_log_rpow_rpow_atTop a hε).isBigO
    have hmul : (fun x : ℝ => (Real.log x) ^ a / x ^ s)
        =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s) := by
      simpa only [div_eq_mul_inv] using ho.mul (isBigO_refl (fun x : ℝ => (x ^ s)⁻¹) atTop)
    have heq : (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s)
        =ᶠ[atTop] (fun x : ℝ => x ^ ((s - 1) / 2 - s)) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [← Real.rpow_sub hx]
    exact (hmul.trans_eventuallyEq heq).natCast_atTop

private lemma summable_vonMangoldt_div_rpow (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => (Λ n : ℝ) / (n:ℝ) ^ s) := by
  refine Summable.of_nonneg_of_le (fun n => div_nonneg vonMangoldt_nonneg (by positivity)) ?_
    (summable_log_rpow_div_rpow 1 hs)
  intro n
  rw [Real.rpow_one]
  gcongr
  exact vonMangoldt_le_log

private lemma summable_c_term (s : ℝ) (hs : 1 < s) :
    Summable (fun d : ℕ => c d * ((d:ℝ) ^ (1 - s) / (s - 1))) := by
  have hs1 : (0:ℝ) < s - 1 := by linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  
  refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_)
    ((summable_vonMangoldt_div_rpow s hs).mul_left (1 / (Real.log 2 * (s - 1))))
  · 
    refine mul_nonneg (c_nonneg d) (div_nonneg ?_ hs1.le)
    rcases eq_or_ne (d:ℝ) 0 with hd | hd
    · rw [hd, Real.zero_rpow (by linarith : (1 - s) ≠ 0)]
    · positivity
  · 
    rcases lt_or_ge d 2 with hd | hd
    · have hc : c d = 0 := by interval_cases d <;> simp
      rw [hc, zero_mul]
      exact mul_nonneg (by positivity) (div_nonneg vonMangoldt_nonneg (by positivity))
    · have hd2 : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      have hd0 : (0:ℝ) < (d:ℝ) := by linarith
      have hlogge : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) hd2
      have hds : (0:ℝ) < (d:ℝ) ^ s := Real.rpow_pos_of_pos hd0 s
      have hkey : c d * ((d:ℝ) ^ (1 - s) / (s - 1)) = Λ d / ((d:ℝ) ^ s * Real.log d * (s - 1)) := by
        unfold c
        rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hd0, Real.rpow_one, Real.rpow_neg hd0.le]
        field_simp
      
      have hcb : (d:ℝ) ^ s * Real.log 2 * (s - 1) ≤ (d:ℝ) ^ s * Real.log d * (s - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogge hds.le) hs1.le
      rw [hkey, show (1 / (Real.log 2 * (s - 1))) * ((Λ d : ℝ) / (d:ℝ) ^ s)
          = Λ d / ((d:ℝ) ^ s * Real.log 2 * (s - 1)) from by field_simp]
      exact div_le_div_of_nonneg_left vonMangoldt_nonneg (by positivity) hcb

theorem log_zeta_eq_integ_aux (s : ℝ) (hs : 1 < s) :
    Real.log (riemannZeta (s:ℂ)).re =
      (s - 1) * ∫ x in Set.Ioi 1, (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) := by
  rw [Mertens.log_zeta_eq_sum s hs]
  symm
  have hstep1 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s)
        = (∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, c d) * x ^ (-s) := by
    intro x hx
    simp only [Mertens.E₂Λ, c]
    ring
  have hstep2 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) = ∑' d : ℕ, f s d x := by
    intro x hx
    rw [hstep1 x hx]
    simp only [f]
    rw [Finset.sum_mul]
    have hx0 : (0:ℝ) ≤ x := by have := hx; simp only [Set.mem_Ioi] at this; linarith
    rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊x⌋₊) ?_]
    · apply Finset.sum_congr rfl
      intro d hd
      simp only [Finset.mem_Ioc] at hd
      have hdx : (d:ℝ) ≤ x := by
        rw [← Nat.le_floor_iff hx0]; exact hd.2
      rw [Set.indicator_of_mem (by simpa using hdx)]
    · intro d hd
      simp only [Finset.mem_Ioc, not_and, not_le] at hd
      rcases Nat.eq_zero_or_pos d with hd0 | hd0
      · subst hd0; simp
      · have hfloor : ⌊x⌋₊ < d := hd hd0
        have hdx : x < (d:ℝ) := by
          rw [← Nat.floor_lt hx0]; exact hfloor
        rw [Set.indicator_of_notMem (by simpa using not_le.mpr hdx)]
        ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hstep2]
  have hperterm : ∀ d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0; simp [f]
    simp only [f]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_indicator measurableSet_Ici]
    congr 1
    have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd0
    have hdR0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    set A : Set ℝ := Set.Ioi (1:ℝ) ∩ Set.Ici (d:ℝ) with hA
    have hae : A =ᵐ[volume] Set.Ioi (d:ℝ) := by
      have h1 : A =ᵐ[volume] (Set.Ici (1:ℝ) ∩ Set.Ici (d:ℝ) : Set ℝ) :=
        MeasureTheory.ae_eq_set_inter MeasureTheory.Ioi_ae_eq_Ici (ae_eq_refl _)
      rw [Set.Ici_inter_Ici, max_eq_right hdR] at h1
      exact h1.trans MeasureTheory.Ioi_ae_eq_Ici.symm
    rw [MeasureTheory.setIntegral_congr_set hae]
    rw [integral_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) hdR0,
      show (-s + 1 : ℝ) = 1 - s by ring]
    have hs1 : (1 - s) ≠ 0 := by linarith
    have hs2 : (s - 1) ≠ 0 := by linarith
    field_simp
    ring
  have hint : ∀ d : ℕ, MeasureTheory.IntegrableOn (f s d) (Set.Ioi (1:ℝ)) := by
    intro d
    unfold f
    apply MeasureTheory.Integrable.const_mul
    rw [show MeasureTheory.Integrable ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
        (volume.restrict (Set.Ioi (1:ℝ)))
      ↔ MeasureTheory.IntegrableOn ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
          (Set.Ioi (1:ℝ)) volume from Iff.rfl,
      MeasureTheory.integrableOn_indicator_iff measurableSet_Ici]
    apply MeasureTheory.IntegrableOn.mono_set
      (integrableOn_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) (by norm_num : (0:ℝ) < 1/2))
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    linarith [hx.2]
  have hnorm_int : ∀ d : ℕ,
      ∫ x in Set.Ioi (1:ℝ), ‖f s d x‖ = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rw [← hperterm d]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hfnn : 0 ≤ f s d x := by
      simp only [f]
      apply mul_nonneg (c_nonneg d)
      by_cases hxd : (d:ℝ) ≤ x
      · rw [Set.indicator_of_mem (by simpa using hxd)]
        exact le_of_lt (Real.rpow_pos_of_pos (by linarith) _)
      · rw [Set.indicator_of_notMem (by simpa using hxd)]
    change ‖f s d x‖ = f s d x
    rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
  have hinterchange : ∫ x in Set.Ioi (1:ℝ), ∑' d : ℕ, f s d x
      = ∑' d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x := by
    refine (MeasureTheory.integral_tsum_of_summable_integral_norm hint ?_).symm
    apply (summable_c_term s hs).congr
    intro d
    exact (hnorm_int d).symm
  rw [hinterchange]
  simp_rw [hperterm]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro d
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0; simp
  · have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    have hsub : (d:ℝ) ^ (1 - s) = (d:ℝ) ^ (-s) * (d:ℝ) := by
      rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hdR, Real.rpow_one]
    have hs1 : s - 1 ≠ 0 := by linarith
    have hneg : (d:ℝ) ^ (-s) = ((d:ℝ) ^ s)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hdR)]
    unfold c
    rw [hsub, hneg]
    field_simp

end LogZetaInteg
end

private theorem log_zeta_eq_integ (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = (s - 1) * ∫ x in .Ioi 1, (log (log x) + γ + E₂Λ x) * x^(-s) :=
  LogZetaInteg.log_zeta_eq_integ_aux s hs

private theorem mul_integ_log_log_eq (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in .Ioi 1, log (log x) * x^(-s) = - log (s - 1) + deriv Gamma 1 :=
  mul_integ_log_log_eq_aux s hs

private theorem mul_integ_gamma_eq (s) (hs : 1 < s) : (s - 1) * ∫ x in .Ioi 1, γ * x^(-s) = γ := by
  rw [MeasureTheory.integral_const_mul γ (· ^ (-s)), @integral_Ioi_rpow_of_lt (-s), one_rpow] <;>
    grind

private theorem integrableOn_Ioi_mul_rpow_neg_of_abs_le
    {c B a s : ℝ} (hc : 0 < c) (has : a + 1 < s) {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x ∈ Set.Ioi c, |f x| ≤ B * x ^ a) :
    MeasureTheory.IntegrableOn (fun x => f x * x ^ (-s)) (Set.Ioi c) := by
  have hg : MeasureTheory.IntegrableOn (fun x => B * x ^ (a - s)) (Set.Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : a - s < -1) hc).const_mul B
  refine MeasureTheory.Integrable.mono' hg
    (hf.mul (measurable_id.pow_const (-s))).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : (0:ℝ) < x := hc.trans hx
  have hxs : (0:ℝ) < x ^ (-s) := Real.rpow_pos_of_pos hxpos _
  rw [norm_mul, norm_eq_abs, norm_eq_abs, abs_of_pos hxs]
  calc |f x| * x ^ (-s) ≤ B * x ^ a * x ^ (-s) :=
        mul_le_mul_of_nonneg_right (hbound x hx) hxs.le
    _ = B * x ^ (a - s) := by rw [mul_assoc, ← Real.rpow_add hxpos, sub_eq_add_neg]

private theorem integrableOn_log_log_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => log (log x) * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (1:ℝ) ≤ 2)]
  apply MeasureTheory.IntegrableOn.union
  · 
    have hll : MeasureTheory.IntegrableOn (fun x => log (log x)) (Set.Ioc 1 2) := by
      have h : IntervalIntegrable (log ∘ log) MeasureTheory.volume 1 2 := by
        apply MeromorphicOn.intervalIntegrable_log
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hx
        exact (analyticAt_log (by linarith [hx.1] : 0 < x)).meromorphicAt
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h
    have hmul : MeasureTheory.IntegrableOn (fun x => x ^ (-s) * log (log x)) (Set.Ioc 1 2) := by
      apply hll.bdd_mul (c := 1)
      · fun_prop
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        rw [norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x) _)]
        calc x ^ (-s) ≤ (1:ℝ) ^ (-s) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num) hx.1.le (by linarith)
          _ = 1 := Real.one_rpow _
    simpa [mul_comm] using hmul
  · 
    set ε := (s - 1) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := ε) (B := 1 / ε + |log (log 2)|)
      (by norm_num) (by rw [hε]; linarith) (Real.measurable_log.comp Real.measurable_log) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hx1 : (1:ℝ) ≤ x ^ ε := Real.one_le_rpow (by linarith) hεpos.le
    have hlogx : 0 < log x := Real.log_pos (by linarith)
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hmono : log 2 ≤ log x := Real.log_le_log (by norm_num) (by linarith)
    have hub : log (log x) ≤ x ^ ε / ε :=
      calc log (log x) ≤ log x := (Real.log_le_sub_one_of_pos hlogx).trans (by linarith)
        _ ≤ x ^ ε / ε := Real.log_le_rpow_div (by linarith) hεpos
    have hlb : log (log 2) ≤ log (log x) := Real.log_le_log hlog2 hmono
    have hxε : 0 ≤ x ^ ε / ε := by positivity
    calc |log (log x)| ≤ x ^ ε / ε + |log (log 2)| := by
          rw [abs_le]
          exact ⟨by linarith [neg_abs_le (log (log 2))],
            by linarith [abs_nonneg (log (log 2))]⟩
      _ ≤ (1 / ε + |log (log 2)|) * x ^ ε := by
          have h2 : |log (log 2)| ≤ |log (log 2)| * x ^ ε := le_mul_of_one_le_right (abs_nonneg _) hx1
          have h1 : x ^ ε / ε = 1 / ε * x ^ ε := by ring
          rw [add_mul]; linarith

private theorem integrableOn_γ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => γ * x ^ (-s)) (Set.Ioi 1) := by
  exact (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) one_pos).const_mul γ

private theorem integrableOn_E₂Λ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => E₂Λ x * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioo_union_Ici_eq_Ioi (by norm_num : (1:ℝ) < 2)]
  apply MeasureTheory.IntegrableOn.union
  · 
    have hsub : Set.Ioo (1:ℝ) 2 ⊆ Set.Ioi 1 := fun x hx => hx.1
    have h1 := (integrableOn_γ_mul_rpow s hs).mono_set hsub
    have h2 := (integrableOn_log_log_mul_rpow s hs).mono_set hsub
    have hb : MeasureTheory.IntegrableOn
        (fun x => -(log (log x) * x ^ (-s)) - γ * x ^ (-s)) (Set.Ioo 1 2) :=
      h2.neg.sub h1
    apply hb.congr_fun _ measurableSet_Ioo
    intro x hx
    simp only [Set.mem_Ioo] at hx
    have hfloor : ⌊ x ⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      exact ⟨by push_cast; linarith [hx.1], by push_cast; linarith [hx.2]⟩
    have hsum : (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / ((d:ℝ) * log d)) = 0 := by rw [hfloor]; norm_num
    change -(log (log x) * x ^ (-s)) - γ * x ^ (-s)
        = (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ) * x ^ (-s)
    rw [hsum]; ring
  · 
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := 0) (B := (log 4 + 6) / log 2)
      (by norm_num) (by linarith) (by fun_prop) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hc : 0 ≤ log 4 + 6 := by positivity
    rw [Real.rpow_zero, mul_one]
    have hb2 : (log 4 + 6) / log x ≤ (log 4 + 6) / log 2 :=
      div_le_div_of_nonneg_left hc hlog2 (Real.log_le_log (by norm_num) (le_of_lt hx))
    exact (E₂Λ.abs_le (le_of_lt hx)).trans hb2

private theorem log_zeta_eq (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = - log (s - 1) + deriv Gamma 1 + γ + (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x^(-s) := by
  
  rw [log_zeta_eq_integ s hs]
  
  have key : (∫ x in Set.Ioi 1, (log (log x) + γ + E₂Λ x) * x ^ (-s))
      = (∫ x in Set.Ioi 1, log (log x) * x ^ (-s))
        + (∫ x in Set.Ioi 1, γ * x ^ (-s))
        + (∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)) := by
    rw [← MeasureTheory.integral_add (integrableOn_log_log_mul_rpow s hs)
      (integrableOn_γ_mul_rpow s hs)]
    rw [← MeasureTheory.integral_add (f := fun x => log (log x) * x ^ (-s) + γ * x ^ (-s))
      (g := fun x => E₂Λ x * x ^ (-s))
      ((integrableOn_log_log_mul_rpow s hs).add (integrableOn_γ_mul_rpow s hs))
      (integrableOn_E₂Λ_mul_rpow s hs)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    ring
  
  rw [key, mul_add, mul_add, mul_integ_log_log_eq s hs, mul_integ_gamma_eq s hs]

private lemma zeta_pole_mul_re_tendsto_one :
    Filter.Tendsto (fun s : ℝ => (s - 1) * (riemannZeta (s : ℂ)).re)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  have hofReal :
      Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
        (nhdsWithin (1 : ℂ) ({1} : Set ℂ)ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Set.mem_compl_singleton_iff.mpr (by
        norm_num
        exact ne_of_gt (Set.mem_Ioi.mp hs))
  have hcomplex :
      Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    riemannZeta_residue_one.comp hofReal
  have hreal :
      Filter.Tendsto
        (fun s : ℝ => (((s : ℂ) - 1) * riemannZeta (s : ℂ)).re)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 : ℝ)) :=
    (Complex.continuous_re.tendsto (1 : ℂ)).comp hcomplex
  simpa [Complex.ofReal_sub, Complex.ofReal_mul] using hreal

private theorem log_zeta_limit :
    Filter.Tendsto
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  have hlog :
      Filter.Tendsto
        (fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.log 1)) :=
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      zeta_pole_mul_re_tendsto_one
  have hEq :
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
        =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s - 1 := sub_pos.mpr (Set.mem_Ioi.mp hs)
    have hzpos : 0 < (riemannZeta (s : ℂ)).re :=
      riemannZeta_re_pos_of_one_lt (Set.mem_Ioi.mp hs)
    rw [Real.log_mul hspos.ne' hzpos.ne']
    ring
  simpa using hlog.congr' (hEq.mono fun s hs => hs.symm)

section
open MeasureTheory Set

private lemma measurable_E₂Λ : Measurable E₂Λ := by fun_prop

private lemma E₂Λ_eq_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    E₂Λ x = - log (log x) - γ := by
  obtain ⟨h1, h2⟩ := hx
  have hf : ⌊x⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by exact_mod_cast h1.le, by exact_mod_cast h2⟩
  unfold E₂Λ
  rw [hf]
  simp

private lemma abs_E₂Λ_le_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    |E₂Λ x| ≤ |log (x - 1)| + log 2 + |γ| := by
  obtain ⟨hx1, hx2⟩ := hx
  have hloglog : |log (log x)| ≤ |log (x - 1)| + log 2 := by
    have hxpos : (0:ℝ) < x := by linarith
    have hlogx_pos : 0 < log x := Real.log_pos hx1
    have hxm1 : 0 < x - 1 := by linarith
    have hub : log x ≤ x - 1 := by have := Real.log_le_sub_one_of_pos hxpos; linarith
    have hlb2 : (x - 1) / 2 ≤ log x := by
      have h := Real.log_le_sub_one_of_pos (x := 1 / x) (by positivity)
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one] at h
      simp only [zero_sub] at h
      have h12 : (x - 1) / 2 ≤ 1 - 1 / x := by
        rw [← sub_nonneg]
        have e : (1 - 1 / x) - (x - 1) / 2 = (3 * x - 2 - x ^ 2) / (2 * x) := by field_simp; ring
        rw [e]; exact div_nonneg (by nlinarith [hx1, hx2]) (by positivity)
      linarith
    have hupper : log (log x) ≤ log (x - 1) := Real.log_le_log hlogx_pos hub
    have hlower : log (x - 1) - log 2 ≤ log (log x) := by
      have := Real.log_le_log (show (0:ℝ) < (x - 1) / 2 by positivity) hlb2
      rwa [Real.log_div (by linarith) (by norm_num)] at this
    have h2 : (0:ℝ) ≤ log 2 := Real.log_nonneg (by norm_num)
    rw [abs_le]
    exact ⟨by have := neg_abs_le (log (x - 1)); linarith,
          by have := le_abs_self (log (x - 1)); linarith⟩
  rw [E₂Λ_eq_on_Ioo ⟨hx1, hx2⟩]
  have htri : |(- log (log x) - γ)| ≤ |log (log x)| + |γ| := by
    have h := abs_sub (-log (log x)) γ
    rwa [abs_neg] at h
  linarith

private lemma abs_E₂Λ_le_const {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log 2 :=
  (E₂Λ.abs_le hx).trans <| div_le_div_of_nonneg_left (by positivity)
    (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) hx)

private lemma integrableOn_log_sub_one_bound :
    IntegrableOn (fun x => |log (x - 1)| + log 2 + |γ|) (Set.Ioo 1 2) volume := by
  have hlog : IntegrableOn (fun x => |log (x - 1)|) (Set.Ioo 1 2) volume := by
    have h0 : IntervalIntegrable (fun x => log x) volume 0 1 :=
      intervalIntegral.intervalIntegrable_log'
    have h1 : IntervalIntegrable (fun x => log (x - 1)) volume (0 + 1) (1 + 1) :=
      h0.comp_sub_right 1
    norm_num at h1
    exact (h1.1.mono_set Set.Ioo_subset_Ioc_self).abs
  have hc : IntegrableOn (fun _ : ℝ => log 2 + |γ|) (Set.Ioo (1 : ℝ) 2) volume :=
    integrableOn_const (measure_Ioo_lt_top).ne (by finiteness)
  have hsum : IntegrableOn (fun x => |log (x - 1)| + (log 2 + |γ|)) (Set.Ioo 1 2) volume :=
    hlog.add hc
  exact hsum.congr_fun (fun x _ => by ring) measurableSet_Ioo

private lemma integrableOn_E₂Λ_Ioo {X : ℝ} (_hX : 2 ≤ X) :
    IntegrableOn E₂Λ (Set.Ioo 1 X) volume := by
  have hsub : Set.Ioo (1 : ℝ) X ⊆ Set.Ioo 1 2 ∪ Set.Icc 2 X := by
    intro x hx; simp only [Set.mem_Ioo, Set.mem_union, Set.mem_Icc] at *
    rcases lt_or_ge x 2 with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨h, hx.2.le⟩
  apply IntegrableOn.mono_set _ hsub
  apply IntegrableOn.union
  · have hg := integrableOn_log_sub_one_bound
    refine Integrable.mono' hg measurable_E₂Λ.aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_on_Ioo hx
  · refine Integrable.mono' (g := fun _ => (log 4 + 6) / log 2) ?_
      measurable_E₂Λ.aestronglyMeasurable ?_
    · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by finiteness)
    · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_const hx.1

private lemma sub_one_mul_integral_E₂Λ_tendsto :
    Filter.Tendsto (fun s : ℝ => (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  
  obtain ⟨X₀, hX₀⟩ : ∃ X, ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := by
    have := E₂Λ.bound'.def (by positivity : (0:ℝ) < ε / 2)
    simp only [Real.norm_eq_abs, abs_one, mul_one] at this
    rw [Filter.eventually_atTop] at this; exact this
  set X := max X₀ 2 with hXdef
  have hX2 : 2 ≤ X := le_max_right _ _
  have hXge : ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := fun x hx => hX₀ x (le_trans (le_max_left _ _) hx)
  
  set B := ∫ x in Set.Ioo 1 X, |E₂Λ x| with hBdef
  have hB0 : 0 ≤ B := setIntegral_nonneg measurableSet_Ioo (fun x _ => abs_nonneg _)
  refine ⟨min 1 (ε / 2 / (B + 1)), by positivity, ?_⟩
  intro s hs hdist
  simp only [Set.mem_Ioi] at hs
  rw [Real.dist_eq] at hdist
  have hs1 : s - 1 < min 1 (ε / 2 / (B + 1)) := by
    rw [abs_of_pos (by linarith)] at hdist; exact hdist
  have hsm1 : 0 < s - 1 := by linarith
  
  have hintAbs : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi 1) volume := by
    have h2 : IntegrableOn (fun x => |E₂Λ x * x ^ (-s)|) (Set.Ioi 1) volume :=
      (integrableOn_E₂Λ_mul_rpow s hs).abs
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro x hx; simp only [Set.mem_Ioi] at hx
    change |E₂Λ x * x ^ (-s)| = |E₂Λ x| * x ^ (-s)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  have hintAbsIoc : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioc 1 X) volume :=
    hintAbs.mono_set Set.Ioc_subset_Ioi_self
  have hintAbsIoiX : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi X) volume :=
    hintAbs.mono_set (Set.Ioi_subset_Ioi (by linarith))
  
  have hsplit : ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) =
      (∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s)) + ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) := by
    have hu : Set.Ioi (1:ℝ) = Set.Ioc 1 X ∪ Set.Ioi X :=
      (Set.Ioc_union_Ioi_eq_Ioi (by linarith)).symm
    rw [hu, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_left))
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_right))]
  
  have hp1 : ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ B := by
    rw [hBdef]
    have ha : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioo 1 X) volume := (integrableOn_E₂Λ_Ioo hX2).abs
    have habsIoc : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioc 1 X) volume :=
      ha.congr_set_ae (Ioo_ae_eq_Ioc).symm
    rw [← integral_Ioc_eq_integral_Ioo]
    apply setIntegral_mono_on hintAbsIoc habsIoc measurableSet_Ioc
    intro x hx
    have hx1 : (1:ℝ) ≤ x := by have := hx.1; linarith
    have hle1 : x ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    calc |E₂Λ x| * x ^ (-s) ≤ |E₂Λ x| * 1 := by gcongr
      _ = |E₂Λ x| := mul_one _
  
  have hp2 : ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ (ε / 2) * (X ^ (1 - s) / (s - 1)) := by
    have hrpow_int : IntegrableOn (fun x : ℝ => x ^ (-s)) (Set.Ioi X) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X)
    have hval : ∫ x in Set.Ioi X, x ^ (-s) = X ^ (1 - s) / (s - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X),
        show -s + 1 = 1 - s by ring, show (1:ℝ) - s = -(s - 1) by ring]
      rw [div_neg, neg_div, neg_neg]
    rw [← hval, ← integral_const_mul]
    apply setIntegral_mono_on hintAbsIoiX (hrpow_int.const_mul (ε / 2)) measurableSet_Ioi
    intro x hx
    have hxpos : (0:ℝ) < x := by simp only [Set.mem_Ioi] at hx; linarith
    have hnn : 0 ≤ x ^ (-s) := Real.rpow_nonneg hxpos.le _
    have hb : |E₂Λ x| ≤ ε / 2 := hXge x (by simp only [Set.mem_Ioi] at hx; linarith)
    gcongr
  have hXpow : X ^ (1 - s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  
  have hbound : (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B + ε / 2 := by
    rw [hsplit, mul_add]
    have ht2 : (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ ε / 2 := by
      calc (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s)
          ≤ (s - 1) * ((ε / 2) * (X ^ (1 - s) / (s - 1))) :=
            mul_le_mul_of_nonneg_left hp2 hsm1.le
        _ = (ε / 2) * X ^ (1 - s) := by
              have hne : s - 1 ≠ 0 := by linarith
              field_simp
        _ ≤ (ε / 2) * 1 := by gcongr
        _ = ε / 2 := mul_one _
    have ht1 : (s - 1) * ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B :=
      mul_le_mul_of_nonneg_left hp1 hsm1.le
    linarith
  
  have habs_le : |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := by
    rw [abs_mul, abs_of_pos hsm1]
    gcongr
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [Set.mem_Ioi] at hx
    change ‖E₂Λ x * x ^ (-s)‖ = |E₂Λ x| * x ^ (-s)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  rw [Real.dist_eq, sub_zero]
  
  have hfin : (s - 1) * B + ε / 2 < ε := by
    have hlt : s - 1 < ε / 2 / (B + 1) := lt_of_lt_of_le hs1 (min_le_right _ _)
    have hBp : 0 < B + 1 := by linarith
    have h1 : (s - 1) * B ≤ (s - 1) * (B + 1) := by nlinarith
    have h2 : (s - 1) * (B + 1) < (ε / 2 / (B + 1)) * (B + 1) := mul_lt_mul_of_pos_right hlt hBp
    have h3 : (ε / 2 / (B + 1)) * (B + 1) = ε / 2 := by field_simp
    linarith
  calc |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := habs_le
    _ ≤ (s - 1) * B + ε / 2 := hbound
    _ < ε := hfin

end

theorem deriv_gamma_add_γ_eq_zero : deriv Gamma 1 + γ = 0 := by
  
  have key : ∀ s : ℝ, 1 < s →
      (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s) = deriv Gamma 1 + γ := by
    intro s hs
    have h := log_zeta_eq s hs
    linarith
  
  have hconst : Filter.Tendsto
      (fun s : ℝ => (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (deriv Gamma 1 + γ)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (key s hs).symm
  
  have hlim := log_zeta_limit.sub sub_one_mul_integral_E₂Λ_tendsto
  rw [sub_zero] at hlim
  exact tendsto_nhds_unique hconst hlim

theorem γ.eq_eulerMascheroni : γ = eulerMascheroniConstant := by
  linarith [Real.eulerMascheroniConstant_eq_neg_deriv, deriv_gamma_add_γ_eq_zero]

noncomputable def M : ℝ := (∫ t in Set.Ioi 2, E₁p t / (t * log t^2)) + 1 - log (log 2)

theorem M.le : M ≤ (log 4 + 4) / log 2 + 1 - log (log 2) := calc
    _ ≤ (∫ t in Set.Ioi 2, (log 4 + 4) / (t * log t^2)) + 1 - log (log 2) := by
      unfold M; gcongr with x hx
      · exact integrable_E₁p_div_mul_log_sq (by norm_num)
      · exact integrable_const_div_mul_log_sq _ (by norm_num)
      · measurability
      · simp at hx; positivity
      simp at hx; exact E₁p.le (by linarith)
    _ = _ := by rw [integ_div_mul_log_sq _ (by norm_num)]

theorem M.ge : M ≥ (-2 - E₁) / log 2 + 1 - log (log 2) := calc
    _ ≥ (∫ t in Set.Ioi 2, (-2 - E₁) / (t * log t^2)) + 1 - log (log 2) := by
      unfold M; gcongr with x hx
      · exact integrable_const_div_mul_log_sq _ (by norm_num)
      · exact integrable_E₁p_div_mul_log_sq (by norm_num)
      · measurability
      · simp at hx; positivity
      simp at hx; exact E₁p.ge (by linarith)
    _ = _ := by rw [integ_div_mul_log_sq _ (by norm_num)]

noncomputable abbrev E₂p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p - log (log x) - M

theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind

theorem E₂p.bound : E₂p =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6 + E₁, 2
    intro x hx
    convert E₂p.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]

theorem E₂p.bound' : E₂p =o[atTop] (fun _ ↦ (1:ℝ)) := E₂p.bound.trans_isLittleO inv_log_eq_o_one

lemma HasSum_log_one_sub_one_div_prime {p : ℕ} (hp : p.Prime) :
    HasSum (fun n : ℕ ↦ (-1 : ℝ) / (( n + 1) * p ^ (n + 1))) (log (1 - 1 / p)) := by
  convert! Real.hasSum_pow_div_log_of_abs_lt_one (x := 1 / p) _|>.neg using 1
  · ext
    rw [div_pow, one_pow, div_div]
    ring
  · ring
  · simp only [one_div, abs_inv, Nat.abs_cast]
    exact inv_lt_one_of_one_lt₀ (mod_cast hp.one_lt)

lemma E₂Λ_sub_E₂p_tendsto :
    Tendsto (E₂Λ - E₂p) atTop (nhds 0) := by
  exact isLittleO_one_iff ℝ|>.mp <| E₂Λ.bound'.sub E₂p.bound'

noncomputable abbrev M_eq_f (n : ℕ) :=
    if ¬n.Prime then Λ n /(n * log n) else 0

lemma E₂Λ_sub_E₂p_eq (x : ℝ) :
    E₂Λ x - E₂p x = ∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_f n - (γ - M) := by
  calc
  _ = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p - (γ - M) := by ring
  _ = _ := by
    rw [sum_filter, ← sum_sub_distrib]
    congr
    ext n
    split_ifs with hn
    · rw [vonMangoldt_apply_prime hn]
      have : log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · ring

lemma M_eq_f.sum_tendsto :
    Tendsto (fun (x : ℝ) ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_f n) atTop (nhds (γ - M)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  convert E₂Λ_sub_E₂p_tendsto using 1
  ext
  rw [← E₂Λ_sub_E₂p_eq]
  simp

lemma M_eq_f.sum_tendsto' :
    Tendsto (fun (N : ℕ) ↦ ∑ n ∈ range N, M_eq_f n) atTop (nhds (γ - M)) := by
  have : Tendsto (fun (N : ℕ) ↦ (∑ n ∈ Ioc 0 ⌊(N : ℝ)⌋₊, M_eq_f n)) atTop (nhds (γ - M)) := M_eq_f.sum_tendsto.comp tendsto_natCast_atTop_atTop
  simp_rw [Nat.floor_natCast] at this
  apply (this.comp (tendsto_sub_atTop_nat 1)).congr'
  filter_upwards [eventually_ge_atTop 1] with N hn
  rw [Nat.range_eq_Icc_zero_sub_one, ← add_sum_Ioc_eq_sum_Icc] <;> grind

lemma M_eq_f.HasSum :
    HasSum M_eq_f (γ - M) := by
  refine hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ ?_) _|>.mpr M_eq_f.sum_tendsto'
  unfold M_eq_f
  split_ifs with hn
  · rfl
  · exact div_nonneg vonMangoldt_nonneg (by positivity)

lemma M_eq_f.sum_primes :
    ∑' (p : Nat.Primes), M_eq_f p = 0 := by
  convert! tsum_zero with p
  grind

lemma tsum_primes_eq_tsum_ite (f : ℕ → ℝ) :
    ∑' (n : Nat.Primes), f n = ∑' (n : ℕ), if n.Prime then f n else 0 := by
  convert! _root_.tsum_subtype Nat.Prime f using 2
  ext
  simp [Set.indicator]
  congr

lemma tsum_M_eq_f_eq_tsum :
    -∑' (n : ℕ), M_eq_f n = ∑' p : ℕ, if p.Prime then log (1 - 1 / p) + 1 / p else 0 := by
  rw [tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers M_eq_f.HasSum.summable
    (fun n hn ↦ (by simp_all [vonMangoldt_ne_zero_iff])), M_eq_f.sum_primes, zero_add,
    tsum_primes_eq_tsum_ite (fun p ↦ ∑' (k : ℕ), M_eq_f (p ^ (k + 2))), ← tsum_neg]
  refine tsum_congr fun n ↦ ?_
  split_ifs with hn
  · rw [← HasSum_log_one_sub_one_div_prime hn|>.tsum_eq, HasSum_log_one_sub_one_div_prime hn|>.summable.tsum_eq_zero_add]
    simp only [ite_not, Nat.cast_pow, log_pow, Nat.cast_add, Nat.cast_ofNat, CharP.cast_eq_zero,
      zero_add, pow_one, one_mul, Nat.cast_one, one_div]
    trans -∑' (k : ℕ), (1 : ℝ) / ((k + 2) * n ^ (k + 2))
    · congr
      ext k
      have : ¬(Nat.Prime (n ^ (k + 2))) := by exact Nat.Prime.not_prime_pow (by grind)
      simp only [this, ↓reduceIte, one_div, mul_inv_rev]
      rw [vonMangoldt_apply_pow (by grind), vonMangoldt_apply_prime hn]
      have : log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · rw [← tsum_neg]
      ring_nf
      congr
      ext
      ring_nf
  · ring

theorem M.eq : M = γ + ∑' p : ℕ, if p.Prime then log (1 - 1 / p) + 1 / p else 0 := by
  rw [← tsum_M_eq_f_eq_tsum, M_eq_f.HasSum.tsum_eq]
  ring

noncomputable def E₃ (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, log (1 - (1:ℝ) / p) + log (log x) + eulerMascheroniConstant

theorem prod_one_minus_div_prime_eq {x : ℝ} (hx : 1 < x) :
    ∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / p) =
      exp (-eulerMascheroniConstant) * exp (E₃ x) / log x := by
  have hlog : 0 < log x := log_pos hx
  have hpos : ∀ {p : ℕ}, p.Prime → (0 : ℝ) < 1 - 1 / p := fun {p} hp ↦ by
    have : (2 : ℝ) ≤ p := mod_cast hp.two_le
    grind [one_div_le_one_div_of_le two_pos this]
  rw [E₃, exp_add, exp_add, exp_sum, exp_log hlog, exp_neg,
    prod_congr rfl fun p hp ↦ exp_log (hpos (mem_filter.mp hp).2)]
  field_simp

noncomputable abbrev M_eq_summand (p : ℕ) := if p.Prime then log (1 - 1 / p) + 1 / p else 0

lemma M_eq_summand_bound (n : ℕ) :
    |M_eq_summand n| ≤ 2 / n ^ 2 := by
  unfold M_eq_summand
  split_ifs with h
  · trans 1 / n ^ 2 / (1 - 1 / n)
    · convert abs_log_sub_add_sum_range_le (x := 1 / n) _ 1 using 1
      · rw [add_comm]
        simp
      · rw [abs_of_nonneg (by simp)]
        ring
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast h.one_lt)
    rw [(by ring : (2 : ℝ) / n ^ 2 = 1 / n ^ 2 / (1 / 2))]
    gcongr
    suffices (1 : ℝ) / n ≤ 1 / 2 by linarith
    gcongr
    exact_mod_cast h.two_le
  · rw [abs_zero]
    positivity

lemma M_eq_summable : Summable M_eq_summand := by
  apply Summable.of_abs
  exact Summable.of_nonneg_of_le (by simp) M_eq_summand_bound (Summable.const_div (by simp) _)

lemma tsum_M_eq_summand_eq :
    ∑' (n : ℕ), M_eq_summand n = M - γ := by
  rw [M.eq]
  grind

lemma sum_one_div_sq_le {N : ℝ} (hN : 1 ≤ N) :
    ∑' (n : ℕ), (1 : ℝ) / (n + N) ^ 2 ≤ 2 / N := by
  grw [AntitoneOn.tsum_le_integral (f := (fun t ↦ 1 / (t + N) ^ 2))]
  · have hd : ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ -1 / (t + N)) (1 / (x + N) ^ 2) x := by
      intro t ht
      convert! HasDerivAt.fun_div (d' := (1 : ℝ)) (hasDerivAt_const ..) _ _ using 1
      · ring
      · simpa using hasDerivAt_id' t
      · simp at ht
        linarith
    have lim : Tendsto (fun t ↦ -1 / (t + N)) atTop (nhds 0) := by
      exact (tendsto_atTop_add_const_right atTop N tendsto_id).const_div_atTop _
    rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun _ _ ↦ (by positivity)) lim]
    ring_nf
    rw [mul_two]
    gcongr
    field_simp
    exact hN
  · unfold AntitoneOn
    intro a ha b hb h
    beta_reduce
    simp at ha hb
    gcongr
  · convert! integrableOn_add_rpow_Ioi_of_lt (by norm_num : (-2 : ℝ) < -1) (by linarith : -N < 0) using 2
    simp
  · exact fun _ _ ↦ (by positivity)

lemma sum_M_eq_summand_le {N : ℕ} (hN : 0 < N) :
    |∑ n ∈ range N, M_eq_summand n - (M - γ)| ≤ 4 / N := by
  rw [← tsum_M_eq_summand_eq, ← M_eq_summable.sum_add_tsum_nat_add N]
  simp only [sub_add_cancel_left, abs_neg]
  rw [← norm_eq_abs]
  have summable := summable_nat_add_iff N|>.mpr M_eq_summable.norm
  apply norm_tsum_le_tsum_norm summable|>.trans
  apply Summable.tsum_le_tsum (fun _ ↦ M_eq_summand_bound _) summable _|>.trans
  · conv => lhs; arg 1; ext; rw [← mul_one_div]
    rw [tsum_mul_left]
    push_cast
    grw [sum_one_div_sq_le (mod_cast hN)]
    ring_nf
    rfl
  · exact (summable_nat_add_iff N|>.mpr (summable_one_div_nat_pow.mpr one_lt_two))|>.const_div _

lemma sum_M_eq_summand_le' {x : ℝ} (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_summand n - (M - γ)| ≤ 4 / x := by
  have := sum_M_eq_summand_le (by grind : 0 < ⌊x⌋₊ + 1)
  rw [Nat.range_eq_Icc_zero_sub_one _ (by grind), ← add_sum_Ioc_eq_sum_Icc (by grind),
    (by simp : M_eq_summand 0 = 0), zero_add] at this
  simp only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one] at this
  grw [this]
  gcongr
  exact Nat.lt_floor_add_one _|>.le

theorem E₃.abs_le : ∃ C, ∀ x, 2 ≤ x → |E₃ x| ≤ C / log x := by
  unfold E₃
  refine ⟨4 + (log 4 + 6 + E₁), fun x hx ↦ ?_⟩
  calc
  _ = |(∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_summand n - (M - γ)) - E₂p x| := by
    unfold E₂p
    have (n : ℕ) : M_eq_summand n = (if n.Prime then log (1 - 1 / n) else 0) + (if n.Prime then (1 : ℝ) / n else 0) := by
      unfold M_eq_summand
      split_ifs
      · rfl
      · ring
    simp_rw [this]
    rw [sum_filter, sum_filter, sum_add_distrib, γ.eq_eulerMascheroni]
    ring_nf
  _ ≤ _ := by
    grw [abs_sub, E₂p.abs_le hx, sum_M_eq_summand_le' hx]
    have : 4 / x ≤ 4 / log x := by
      gcongr
      · exact log_pos (by linarith)
      · exact log_le_self (by linarith)
    grw [this]
    rw [← add_div]

theorem E₃.bound : E₃ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [isBigO_iff, norm_eq_abs, eventually_atTop]
    obtain ⟨ C, hC ⟩ := E₃.abs_le
    use C, 2
    convert hC using 3 with x hx
    have : 0 < log x := by apply log_pos; linarith
    have : 0 < 1 / log x := by positivity
    grind [abs_of_pos this]

theorem E₃.bound' : E₃ =o[atTop] (fun _ ↦ (1:ℝ)) := E₃.bound.trans_isLittleO inv_log_eq_o_one

theorem E₃.bound'' : (fun x ↦ ∏ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1 - (1:ℝ) / p)) ~[atTop] (fun x ↦ exp (-eulerMascheroniConstant) / log x) := by
   rw [isEquivalent_iff_tendsto_one]
   · convert Tendsto.congr' ?_ (Tendsto.rexp ((isLittleO_one_iff ℝ).mp E₃.bound')) using 2 with x
     · simp
     simp only [EventuallyEq.iff_eventually, Pi.div_apply, eventually_atTop]; use 2; intro x hx
     rw [prod_one_minus_div_prime_eq (by linarith)]
     have : 0 < log x := by apply log_pos; linarith
     field_simp
   simp only [ne_eq, div_eq_zero_iff, exp_ne_zero, log_eq_zero, eventually_atTop]; use 2
   grind

end Mertens
end

section
open Finset Filter Real
open scoped BigOperators Classical

namespace Erdos946MertensAux

private lemma nonpos_of_deriv_nonpos {a : ℝ} (ha : 0 ≤ a) {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Set.Icc 0 a, HasDerivAt f (f' x) x)
    (h0 : f 0 ≤ 0) (hfp : ∀ x ∈ Set.Icc 0 a, f' x ≤ 0) : f a ≤ 0 := by
  have hmono := antitoneOn_of_deriv_nonpos (convex_Icc 0 a)
    (fun y hy => (hf y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hf y (interior_subset hy)).differentiableAt.differentiableWithinAt)
    (fun y hy => by
      rw [(hf y (interior_subset hy)).deriv]
      exact hfp y (interior_subset hy))
  have hle := hmono ⟨le_rfl, ha⟩ ⟨ha, le_rfl⟩ ha
  linarith

/-- Elementary polynomial upper bound for `exp t - 1` on `0 <= t <= c`. -/
lemma exp_sub_one_le_poly {c t : ℝ} (ht0 : 0 ≤ t) (htc : t ≤ c) :
    Real.exp t - 1 ≤
      t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 + (Real.exp c / 120) * t ^ 5 := by
  have hbound : ∀ x ∈ Set.Icc (0 : ℝ) t, Real.exp x ≤ Real.exp c :=
    fun x hx => Real.exp_le_exp.mpr (hx.2.trans htc)
  have h1 : ∀ x ∈ Set.Icc (0 : ℝ) t, Real.exp x - 1 - Real.exp c * x ≤ 0 := by
    intro x hx
    refine nonpos_of_deriv_nonpos hx.1
      (f := fun z => Real.exp z - 1 - Real.exp c * z)
      (f' := fun z => Real.exp z - Real.exp c) (fun y _ => ?_) (by simp) (fun y hy => by
        linarith [hbound y ⟨hy.1, hy.2.trans hx.2⟩])
    have d1 : HasDerivAt (fun z : ℝ => Real.exp z - 1) (Real.exp y) y :=
      (Real.hasDerivAt_exp y).sub_const 1
    have d2 : HasDerivAt (fun z : ℝ => Real.exp c * z) (Real.exp c) y := by
      simpa using (hasDerivAt_id y).const_mul (Real.exp c)
    exact d1.sub d2
  have h2 : ∀ x ∈ Set.Icc (0 : ℝ) t, Real.exp x - 1 - x - Real.exp c * x ^ 2 / 2 ≤ 0 := by
    intro x hx
    refine nonpos_of_deriv_nonpos hx.1
      (f := fun z => Real.exp z - 1 - z - Real.exp c * z ^ 2 / 2)
      (f' := fun z => Real.exp z - 1 - Real.exp c * z) (fun y _ => ?_) (by simp) (fun y hy =>
        h1 y ⟨hy.1, hy.2.trans hx.2⟩)
    have d1 : HasDerivAt (fun z : ℝ => Real.exp z - 1 - z) (Real.exp y - 1) y :=
      ((Real.hasDerivAt_exp y).sub_const 1).sub (hasDerivAt_id y)
    have d2 : HasDerivAt (fun z : ℝ => Real.exp c * z ^ 2 / 2) (Real.exp c * y) y := by
      have := ((hasDerivAt_pow 2 y).const_mul (Real.exp c)).div_const 2
      simpa [mul_div_assoc] using this.congr_deriv (by norm_num; ring)
    exact d1.sub d2
  have h3 : ∀ x ∈ Set.Icc (0 : ℝ) t,
      Real.exp x - 1 - x - x ^ 2 / 2 - Real.exp c * x ^ 3 / 6 ≤ 0 := by
    intro x hx
    refine nonpos_of_deriv_nonpos hx.1
      (f := fun z => Real.exp z - 1 - z - z ^ 2 / 2 - Real.exp c * z ^ 3 / 6)
      (f' := fun z => Real.exp z - 1 - z - Real.exp c * z ^ 2 / 2) (fun y _ => ?_) (by simp)
      (fun y hy => h2 y ⟨hy.1, hy.2.trans hx.2⟩)
    have d1 : HasDerivAt (fun z : ℝ => Real.exp z - 1 - z - z ^ 2 / 2) (Real.exp y - 1 - y) y := by
      have da := ((Real.hasDerivAt_exp y).sub_const 1).sub (hasDerivAt_id y)
      have db : HasDerivAt (fun z : ℝ => z ^ 2 / 2) y y :=
        ((hasDerivAt_pow 2 y).div_const 2).congr_deriv (by norm_num)
      exact da.sub db
    have d2 : HasDerivAt (fun z : ℝ => Real.exp c * z ^ 3 / 6) (Real.exp c * y ^ 2 / 2) y :=
      (((hasDerivAt_pow 3 y).const_mul (Real.exp c)).div_const 6).congr_deriv (by norm_num; ring)
    exact d1.sub d2
  have h4 : ∀ x ∈ Set.Icc (0 : ℝ) t,
      Real.exp x - 1 - x - x ^ 2 / 2 - x ^ 3 / 6 - Real.exp c * x ^ 4 / 24 ≤ 0 := by
    intro x hx
    refine nonpos_of_deriv_nonpos hx.1
      (f := fun z => Real.exp z - 1 - z - z ^ 2 / 2 - z ^ 3 / 6 - Real.exp c * z ^ 4 / 24)
      (f' := fun z => Real.exp z - 1 - z - z ^ 2 / 2 - Real.exp c * z ^ 3 / 6) (fun y _ => ?_)
      (by simp) (fun y hy => h3 y ⟨hy.1, hy.2.trans hx.2⟩)
    have d1 : HasDerivAt (fun z : ℝ => Real.exp z - 1 - z - z ^ 2 / 2 - z ^ 3 / 6)
        (Real.exp y - 1 - y - y ^ 2 / 2) y := by
      have da := ((Real.hasDerivAt_exp y).sub_const 1).sub (hasDerivAt_id y)
      have db : HasDerivAt (fun z : ℝ => z ^ 2 / 2) y y :=
        ((hasDerivAt_pow 2 y).div_const 2).congr_deriv (by norm_num)
      have dc : HasDerivAt (fun z : ℝ => z ^ 3 / 6) (y ^ 2 / 2) y :=
        ((hasDerivAt_pow 3 y).div_const 6).congr_deriv (by norm_num; ring)
      exact (da.sub db).sub dc
    have d2 : HasDerivAt (fun z : ℝ => Real.exp c * z ^ 4 / 24) (Real.exp c * y ^ 3 / 6) y :=
      (((hasDerivAt_pow 4 y).const_mul (Real.exp c)).div_const 24).congr_deriv (by norm_num; ring)
    exact d1.sub d2
  have h5 : Real.exp t - 1 - t - t ^ 2 / 2 - t ^ 3 / 6 - t ^ 4 / 24 - (Real.exp c / 120) * t ^ 5 ≤ 0 := by
    refine nonpos_of_deriv_nonpos ht0
      (f := fun z => Real.exp z - 1 - z - z ^ 2 / 2 - z ^ 3 / 6 - z ^ 4 / 24 - (Real.exp c / 120) * z ^ 5)
      (f' := fun z => Real.exp z - 1 - z - z ^ 2 / 2 - z ^ 3 / 6 - Real.exp c * z ^ 4 / 24)
      (fun y _ => ?_) (by simp) (fun y hy => h4 y hy)
    have d1 : HasDerivAt (fun z : ℝ => Real.exp z - 1 - z - z ^ 2 / 2 - z ^ 3 / 6 - z ^ 4 / 24)
        (Real.exp y - 1 - y - y ^ 2 / 2 - y ^ 3 / 6) y := by
      have da := ((Real.hasDerivAt_exp y).sub_const 1).sub (hasDerivAt_id y)
      have db : HasDerivAt (fun z : ℝ => z ^ 2 / 2) y y :=
        ((hasDerivAt_pow 2 y).div_const 2).congr_deriv (by norm_num)
      have dc : HasDerivAt (fun z : ℝ => z ^ 3 / 6) (y ^ 2 / 2) y :=
        ((hasDerivAt_pow 3 y).div_const 6).congr_deriv (by norm_num; ring)
      have dd : HasDerivAt (fun z : ℝ => z ^ 4 / 24) (y ^ 3 / 6) y :=
        ((hasDerivAt_pow 4 y).div_const 24).congr_deriv (by norm_num; ring)
      exact ((da.sub db).sub dc).sub dd
    have d2 : HasDerivAt (fun z : ℝ => (Real.exp c / 120) * z ^ 5) (Real.exp c * y ^ 4 / 24) y :=
      ((hasDerivAt_pow 5 y).const_mul (Real.exp c / 120)).congr_deriv (by norm_num; ring)
    exact d1.sub d2
  linarith

/-- Direct induction proof of `(m+1) * b * a^m <= b^(m+1) + m * a^(m+1)` for `0 <= a <= b`. -/
lemma pow_weighted_am_gm {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ m : ℕ, ((m : ℝ) + 1) * b * a ^ m ≤ b ^ (m + 1) + (m : ℝ) * a ^ (m + 1) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have hb : 0 ≤ b := ha.trans hab
    have h2 : a ^ (m + 1) ≤ b ^ (m + 1) := pow_le_pow_left₀ ha hab (m + 1)
    have hstep : 0 ≤ (b - a) * (b ^ (m + 1) - a ^ (m + 1)) :=
      mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr h2)
    have h3 : ((m : ℝ) + 1) * b * a ^ (m + 1) ≤ b ^ (m + 1) * a + (m : ℝ) * a ^ (m + 2) := by
      have hm := mul_le_mul_of_nonneg_right ih ha
      have heq1 : ((m : ℝ) + 1) * b * a ^ m * a = ((m : ℝ) + 1) * b * a ^ (m + 1) := by
        rw [pow_succ]; ring
      have heq2 : (b ^ (m + 1) + (m : ℝ) * a ^ (m + 1)) * a = b ^ (m + 1) * a + (m : ℝ) * a ^ (m + 2) := by
        rw [pow_succ a (m + 1)]; ring
      linarith
    have hb2 : b ^ (m + 1 + 1) = b * b ^ (m + 1) := by rw [pow_succ]; ring
    have ha2 : a ^ (m + 1 + 1) = a ^ (m + 2) := rfl
    have ha12 : a ^ (m + 2) = a * a ^ (m + 1) := by rw [pow_succ]; ring
    push_cast
    nlinarith [hstep, h3, hb2, ha2, ha12]

lemma pow_sub_le_mul_pow_pred' {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (k : ℕ) (hk : 1 ≤ k) :
    ((k : ℝ) - 1) * (b ^ k - a ^ k) ≤ (k : ℝ) * b * (b ^ (k - 1) - a ^ (k - 1)) := by
  cases k with
  | zero => omega
  | succ m =>
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    have h := pow_weighted_am_gm ha hab m
    have hbm : b ^ (m + 1) = b * b ^ m := by rw [pow_succ]; ring
    nlinarith

/-- Partial summation for `∑_{p < w} (log p)^k / p` (`k >= 1`) from Mertens 1st theorem. -/
lemma sum_log_pow_div_p_le (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℕ, 2 ≤ w →
      ∑ p ∈ (Ioo 0 w).filter Nat.Prime, (Real.log p) ^ k / (p : ℝ) ≤
        (Real.log w) ^ k / (k : ℝ) + C * (Real.log w) ^ (k - 1) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Mertens.E₁p.bounded
  have hS_bound : ∀ n : ℕ, 1 ≤ n →
      |∑ p ∈ (Ioc 0 n).filter Nat.Prime, (Real.log p) / (p : ℝ) - Real.log n| ≤ C₁ := by
    intro n hn
    have h := hC₁ (n : ℝ) (by exact_mod_cast hn)
    simpa [Mertens.E₁p, Nat.floor_natCast] using h
  cases k with
  | zero => omega
  | succ m =>
    cases m with
    | zero =>
      refine ⟨C₁ + 1, by linarith, fun w hw => ?_⟩
      have hsub : (Ioo 0 w).filter Nat.Prime ⊆ (Ioc 0 w).filter Nat.Prime := by
        intro p hp
        simp only [mem_filter, mem_Ioo, mem_Ioc] at hp ⊢
        exact ⟨⟨hp.1.1, hp.1.2.le⟩, hp.2⟩
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => by
        have hp' := (mem_filter.mp hp).2
        have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp'.one_lt.le
        exact div_nonneg (Real.log_nonneg h1) (Nat.cast_nonneg p)
      have hb := (abs_le.mp (hS_bound w (by omega))).2
      simp only [zero_add, pow_one, Nat.cast_one, div_one, Nat.sub_self, pow_zero, mul_one]
      linarith
    | succ m' =>
      set k := m' + 2
      have hk2 : 2 ≤ k := by omega
      let S : ℕ → ℝ := fun n => ∑ p ∈ (Ioc 0 n).filter Nat.Prime, Real.log p / (p : ℝ)
      have hS_step : ∀ n : ℕ, 1 ≤ n →
          S n - S (n - 1) = if n.Prime then Real.log n / (n : ℝ) else 0 := by
        intro n hn
        have hIoc : Ioc 0 n = insert n (Ioc 0 (n - 1)) := by
          ext j; simp only [mem_Ioc, mem_insert]; omega
        have hnot : n ∉ Ioc 0 (n - 1) := by simp
        dsimp [S]
        rw [hIoc, Finset.filter_insert]
        split_ifs with hp
        · rw [Finset.sum_insert (fun h => hnot (mem_filter.mp h).1)]
          ring
        · ring
      have hsum_inv_sq : ∀ N : ℕ, ∑ n ∈ Icc 2 N, (1 : ℝ) / ((n : ℝ) * (n : ℝ)) ≤ 1 := by
        intro N
        calc ∑ n ∈ Icc 2 N, (1 : ℝ) / ((n : ℝ) * (n : ℝ))
            ≤ ∑ n ∈ Icc 2 N, ((1 : ℝ) / ((n : ℝ) - 1) - (1 : ℝ) / (n : ℝ)) := by
              refine Finset.sum_le_sum fun n hn => ?_
              have hn2 : 2 ≤ n := (mem_Icc.mp hn).1
              have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn2
              have hpos1 : (0 : ℝ) < n - 1 := by linarith
              have hpos2 : (0 : ℝ) < n := by linarith
              rw [div_sub_div _ _ hpos1.ne' hpos2.ne', div_le_div_iff₀ (mul_pos hpos2 hpos2) (mul_pos hpos1 hpos2)]
              nlinarith
          _ ≤ 1 := by
              by_cases hN2 : N < 2
              · have : Icc 2 N = ∅ := by ext x; simp; omega
                rw [this, Finset.sum_empty]; norm_num
              · push Not at hN2
                have htele : ∀ K : ℕ, 2 ≤ K →
                    ∑ n ∈ Icc 2 K, ((1 : ℝ) / ((n : ℝ) - 1) - (1 : ℝ) / (n : ℝ)) = 1 - 1 / (K : ℝ) := by
                  intro K hK
                  induction K, hK using Nat.le_induction with
                  | base => norm_num
                  | succ j hj ihj =>
                    have hIj : Icc 2 (j + 1) = insert (j + 1) (Icc 2 j) := by
                      ext x; simp only [mem_Icc, mem_insert]; omega
                    have hnj : j + 1 ∉ Icc 2 j := by simp
                    rw [hIj, Finset.sum_insert hnj, ihj]
                    push_cast; ring
                rw [htele N hN2]
                have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
                linarith
      refine ⟨2 * C₁ + (k : ℝ) * 2 + 2, by positivity, fun w hw => ?_⟩
      by_cases hw2 : w = 2
      · subst hw2
        have hempty : (Ioo 0 2).filter Nat.Prime = ∅ := by
          ext p; simp only [mem_filter, mem_Ioo, notMem_empty, iff_false, not_and]
          intro hp hprime; have := hprime.two_le; omega
        rw [hempty, Finset.sum_empty]
        have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        positivity
      have hw3 : 3 ≤ w := by omega
      have hlogw_pos : 0 < Real.log (w : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < w))
      have hrewrite :
          ∑ p ∈ (Ioo 0 w).filter Nat.Prime, (Real.log p) ^ k / (p : ℝ) =
            ∑ n ∈ Icc 2 (w - 1), (S n - S (n - 1)) * (Real.log n) ^ (k - 1) := by
        have h1 : (Ioo 0 w).filter Nat.Prime = (Icc 2 (w - 1)).filter Nat.Prime := by
          ext p; simp only [mem_filter, mem_Ioo, mem_Icc]
          constructor
          · rintro ⟨⟨_, h2⟩, hp⟩; exact ⟨⟨hp.two_le, by omega⟩, hp⟩
          · rintro ⟨⟨h1, h2⟩, hp⟩; exact ⟨⟨by omega, by omega⟩, hp⟩
        rw [h1, Finset.sum_filter]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn2 : 2 ≤ n := (mem_Icc.mp hn).1
        rw [hS_step n (by omega)]
        split_ifs with hp
        · have hk_eq : k = (k - 1) + 1 := by omega
          conv_lhs => rw [hk_eq, pow_succ]
          ring
        · simp
      rw [hrewrite]
      let f : ℕ → ℝ := fun n => (Real.log n) ^ (k - 1)
      have hS1 : S 1 = 0 := by
        dsimp [S]
        have : (Ioc 0 1).filter Nat.Prime = ∅ := by
          ext p; simp only [mem_filter, mem_Ioc, notMem_empty, iff_false, not_and]
          intro h hp; have := hp.two_le; omega
        rw [this, Finset.sum_empty]
      have habp : ∀ N : ℕ, 2 ≤ N →
          ∑ n ∈ Icc 2 N, (S n - S (n - 1)) * f n =
            S N * f N - ∑ n ∈ Icc 2 (N - 1), S n * (f (n + 1) - f n) := by
        intro N hN
        induction N, hN using Nat.le_induction with
        | base =>
          have h1 : Icc 2 2 = {2} := by ext x; simp
          have h2 : Icc 2 1 = ∅ := by ext x; simp
          rw [h1, h2, Finset.sum_singleton, Finset.sum_empty, hS1]
          ring
        | succ M hM ih =>
          have hI1 : Icc 2 (M + 1) = insert (M + 1) (Icc 2 M) := by
            ext x; simp only [mem_Icc, mem_insert]; omega
          have hI2 : Icc 2 M = insert M (Icc 2 (M - 1)) := by
            ext x; simp only [mem_Icc, mem_insert]; omega
          have hn1 : M + 1 ∉ Icc 2 M := by simp
          have hn2 : M ∉ Icc 2 (M - 1) := by simp; omega
          rw [hI1, Finset.sum_insert hn1, ih]
          simp only [Nat.add_sub_cancel]
          rw [hI2, Finset.sum_insert hn2]
          ring
      rw [habp (w - 1) (by omega)]
      have hf_nonneg : ∀ n : ℕ, 1 ≤ n → 0 ≤ f n := fun n hn =>
        pow_nonneg (Real.log_nonneg (by exact_mod_cast hn)) _
      have hf_mono : ∀ n : ℕ, 2 ≤ n → f n ≤ f (n + 1) := fun n hn =>
        pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
          (Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast (by omega : n ≤ n + 1))) _
      have hSw_ub : S (w - 1) ≤ Real.log (w - 1 : ℕ) + C₁ := by
        have := (abs_le.mp (hS_bound (w - 1) (by omega))).2
        linarith
      have hSn_lb : ∀ n ∈ Icc 2 (w - 2), Real.log n - C₁ ≤ S n := by
        intro n hn
        have := (abs_le.mp (hS_bound n (by have := (mem_Icc.mp hn).1; omega))).1
        linarith
      have hsum_lb :
          ∑ n ∈ Icc 2 (w - 2), (Real.log n - C₁) * (f (n + 1) - f n) ≤
            ∑ n ∈ Icc 2 (w - 2), S n * (f (n + 1) - f n) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn2 := (mem_Icc.mp hn).1
        exact mul_le_mul_of_nonneg_right (hSn_lb n hn) (sub_nonneg.mpr (hf_mono n hn2))
      have htele_f : ∑ n ∈ Icc 2 (w - 2), (f (n + 1) - f n) = f (w - 1) - f 2 := by
        have haux : ∀ M : ℕ, 1 ≤ M → ∑ n ∈ Icc 2 M, (f (n + 1) - f n) = f (M + 1) - f 2 := by
          intro M hM
          induction M, hM using Nat.le_induction with
          | base =>
            have : Icc 2 1 = ∅ := by ext x; simp
            rw [this, Finset.sum_empty]; ring
          | succ j hj ihj =>
            have hIj : Icc 2 (j + 1) = insert (j + 1) (Icc 2 j) := by
              ext x; simp only [mem_Icc, mem_insert]; omega
            have hnj : j + 1 ∉ Icc 2 j := by simp
            rw [hIj, Finset.sum_insert hnj, ihj]; ring
        have := haux (w - 2) (by omega)
        rwa [show w - 2 + 1 = w - 1 by omega] at this
      have hterm_lb : ∀ n ∈ Icc 2 (w - 2),
          ((k : ℝ) - 1) / (k : ℝ) * ((Real.log ((n + 1 : ℕ) : ℝ)) ^ k - (Real.log (n : ℝ)) ^ k) -
            (k : ℝ) * (Real.log w) ^ (k - 1) * ((1 : ℝ) / ((n : ℝ) * (n : ℝ))) ≤
              Real.log (n : ℝ) * (f (n + 1) - f n) := by
        intro n hn
        have hn2 := (mem_Icc.mp hn).1
        have hnw := (mem_Icc.mp hn).2
        have ha : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
        have hab : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast (by omega : n ≤ n + 1))
        have h1 := pow_sub_le_mul_pow_pred' ha hab k (by omega)
        have hkpos : (0 : ℝ) < k := by positivity
        have h2 : ((k : ℝ) - 1) / (k : ℝ) * ((Real.log ((n + 1 : ℕ) : ℝ)) ^ k - (Real.log (n : ℝ)) ^ k) ≤
            Real.log ((n + 1 : ℕ) : ℝ) * (f (n + 1) - f n) := by
          dsimp [f]
          rw [div_mul_eq_mul_div, div_le_iff₀ hkpos]
          linarith
        have hdiff_log : Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
          have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
          have hn1 : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast (by omega : 0 < n + 1)
          rw [← Real.log_div hn1.ne' hn0.ne']
          calc Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ))
              ≤ ((n + 1 : ℕ) : ℝ) / (n : ℝ) - 1 := Real.log_le_sub_one_of_pos (div_pos hn1 hn0)
            _ = 1 / (n : ℝ) := by push_cast; field_simp; ring
        have hdiff_f : f (n + 1) - f n ≤ (k : ℝ) * (Real.log w) ^ (k - 1) * (1 / (n : ℝ)) := by
          have hlog3 : (1 : ℝ) < Real.log (w : ℝ) := by
            have h3 : Real.exp 1 < (w : ℝ) := by
              have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
              have hw' : (3 : ℝ) ≤ w := by exact_mod_cast hw3
              linarith
            simpa using Real.log_lt_log (Real.exp_pos 1) h3
          have hbw : Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log (w : ℝ) :=
            Real.log_le_log (by exact_mod_cast (by omega : 0 < n + 1)) (by exact_mod_cast (by omega : n + 1 ≤ w))
          have hpow_diff : ∀ (r : ℕ) (x y : ℝ), 0 ≤ x → x ≤ y →
              y ^ r - x ^ r ≤ (r : ℝ) * y ^ (r - 1) * (y - x) := by
            intro r x y hx hxy
            cases r with
            | zero => simp
            | succ r' =>
              simp only [Nat.add_sub_cancel]
              have hind : ∀ s : ℕ, y ^ (s + 1) - x ^ (s + 1) ≤ ((s : ℝ) + 1) * y ^ s * (y - x) := by
                intro s
                induction s with
                | zero => simp
                | succ s ihs =>
                  have hy : 0 ≤ y := hx.trans hxy
                  have h1' : y ^ (s + 2) - x ^ (s + 2) = y * (y ^ (s + 1) - x ^ (s + 1)) + x ^ (s + 1) * (y - x) := by
                    rw [pow_succ y (s + 1), pow_succ x (s + 1)]; ring
                  have h2' : x ^ (s + 1) ≤ y ^ (s + 1) := pow_le_pow_left₀ hx hxy (s + 1)
                  have h3' : y * (y ^ (s + 1) - x ^ (s + 1)) ≤ y * (((s : ℝ) + 1) * y ^ s * (y - x)) :=
                    mul_le_mul_of_nonneg_left ihs hy
                  have h3'' : y * (((s : ℝ) + 1) * y ^ s * (y - x)) = ((s : ℝ) + 1) * y ^ (s + 1) * (y - x) := by
                    rw [pow_succ]; ring
                  have h4' : x ^ (s + 1) * (y - x) ≤ y ^ (s + 1) * (y - x) :=
                    mul_le_mul_of_nonneg_right h2' (sub_nonneg.mpr hxy)
                  calc y ^ (s + 1 + 1) - x ^ (s + 1 + 1)
                      = y * (y ^ (s + 1) - x ^ (s + 1)) + x ^ (s + 1) * (y - x) := h1'
                    _ ≤ ((s : ℝ) + 1) * y ^ (s + 1) * (y - x) + y ^ (s + 1) * (y - x) := by linarith
                    _ = (((s + 1 : ℕ) : ℝ) + 1) * y ^ (s + 1) * (y - x) := by push_cast; ring
              push_cast
              exact hind r'
          have hpd := hpow_diff (k - 1) (Real.log (n : ℝ)) (Real.log ((n + 1 : ℕ) : ℝ)) ha hab
          have hb_pow : (Real.log ((n + 1 : ℕ) : ℝ)) ^ (k - 1 - 1) ≤ (Real.log (w : ℝ)) ^ (k - 1) := by
            calc (Real.log ((n + 1 : ℕ) : ℝ)) ^ (k - 1 - 1)
                ≤ (Real.log (w : ℝ)) ^ (k - 1 - 1) :=
                  pow_le_pow_left₀ (ha.trans hab) hbw _
              _ ≤ (Real.log (w : ℝ)) ^ (k - 1) :=
                  pow_le_pow_right₀ hlog3.le (by omega)
          have hkm1 : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : k - 1 ≤ k)
          dsimp [f]
          calc (Real.log ((n + 1 : ℕ) : ℝ)) ^ (k - 1) - (Real.log (n : ℝ)) ^ (k - 1)
              ≤ ((k - 1 : ℕ) : ℝ) * (Real.log ((n + 1 : ℕ) : ℝ)) ^ (k - 1 - 1) *
                  (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) := hpd
            _ ≤ (k : ℝ) * (Real.log (w : ℝ)) ^ (k - 1) * (1 / (n : ℝ)) := by
                have hdiff_nn : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := sub_nonneg.mpr hab
                have hA : ((k - 1 : ℕ) : ℝ) * (Real.log ((n + 1 : ℕ) : ℝ)) ^ (k - 1 - 1) ≤
                    (k : ℝ) * (Real.log (w : ℝ)) ^ (k - 1) :=
                  mul_le_mul hkm1 hb_pow (pow_nonneg (ha.trans hab) _) (by positivity)
                exact mul_le_mul hA hdiff_log hdiff_nn (by positivity)
        have hprod_err : (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) * (f (n + 1) - f n) ≤
            (k : ℝ) * (Real.log w) ^ (k - 1) * ((1 : ℝ) / ((n : ℝ) * (n : ℝ))) := by
          have hdiff_nn : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := sub_nonneg.mpr hab
          have hf_nn : 0 ≤ f (n + 1) - f n := sub_nonneg.mpr (hf_mono n hn2)
          calc (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) * (f (n + 1) - f n)
              ≤ (1 / (n : ℝ)) * ((k : ℝ) * (Real.log w) ^ (k - 1) * (1 / (n : ℝ))) :=
                mul_le_mul hdiff_log hdiff_f hf_nn (by positivity)
            _ = (k : ℝ) * (Real.log w) ^ (k - 1) * ((1 : ℝ) / ((n : ℝ) * (n : ℝ))) := by ring
        linarith
      have htele_pow :
          ∑ n ∈ Icc 2 (w - 2), ((Real.log ((n + 1 : ℕ) : ℝ)) ^ k - (Real.log (n : ℝ)) ^ k) =
            (Real.log ((w - 1 : ℕ) : ℝ)) ^ k - (Real.log (2 : ℝ)) ^ k := by
        have haux : ∀ M : ℕ, 1 ≤ M →
            ∑ n ∈ Icc 2 M, ((Real.log ((n + 1 : ℕ) : ℝ)) ^ k - (Real.log (n : ℝ)) ^ k) =
              (Real.log ((M + 1 : ℕ) : ℝ)) ^ k - (Real.log (2 : ℝ)) ^ k := by
          intro M hM
          induction M, hM using Nat.le_induction with
          | base =>
            have : Icc 2 1 = ∅ := by ext x; simp
            rw [this, Finset.sum_empty]; ring
          | succ j hj ihj =>
            have hIj : Icc 2 (j + 1) = insert (j + 1) (Icc 2 j) := by
              ext x; simp only [mem_Icc, mem_insert]; omega
            have hnj : j + 1 ∉ Icc 2 j := by simp
            rw [hIj, Finset.sum_insert hnj, ihj]; ring
        have := haux (w - 2) (by omega)
        rwa [show w - 2 + 1 = w - 1 by omega] at this
      have hsum_log_lb :
          ((k : ℝ) - 1) / (k : ℝ) * ((Real.log ((w - 1 : ℕ) : ℝ)) ^ k - (Real.log 2) ^ k) -
            (k : ℝ) * (Real.log w) ^ (k - 1) ≤
              ∑ n ∈ Icc 2 (w - 2), Real.log (n : ℝ) * (f (n + 1) - f n) := by
        have h1 := Finset.sum_le_sum hterm_lb
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, htele_pow] at h1
        have h2 := hsum_inv_sq (w - 2)
        have h3 : (k : ℝ) * (Real.log w) ^ (k - 1) *
            ∑ n ∈ Icc 2 (w - 2), (1 : ℝ) / ((n : ℝ) * (n : ℝ)) ≤
              (k : ℝ) * (Real.log w) ^ (k - 1) := by
          simpa using mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ (k : ℝ) * (Real.log w) ^ (k - 1))
        linarith
      have hsum_split :
          ∑ n ∈ Icc 2 (w - 2), (Real.log (n : ℝ) - C₁) * (f (n + 1) - f n) =
            (∑ n ∈ Icc 2 (w - 2), Real.log (n : ℝ) * (f (n + 1) - f n)) -
              C₁ * (f (w - 1) - f 2) := by
        calc ∑ n ∈ Icc 2 (w - 2), (Real.log (n : ℝ) - C₁) * (f (n + 1) - f n)
            = ∑ n ∈ Icc 2 (w - 2), (Real.log (n : ℝ) * (f (n + 1) - f n) - C₁ * (f (n + 1) - f n)) := by
              refine Finset.sum_congr rfl fun n _ => by ring
          _ = (∑ n ∈ Icc 2 (w - 2), Real.log (n : ℝ) * (f (n + 1) - f n)) -
                C₁ * ∑ n ∈ Icc 2 (w - 2), (f (n + 1) - f n) := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
          _ = _ := by rw [htele_f]
      have hfw_le : f (w - 1) ≤ (Real.log w) ^ (k - 1) := by
        dsimp [f]
        exact pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ w - 1)))
          (Real.log_le_log (by exact_mod_cast (by omega : 0 < w - 1)) (by exact_mod_cast (by omega : w - 1 ≤ w))) _
      have hlogw_m1 : Real.log ((w - 1 : ℕ) : ℝ) * f (w - 1) = (Real.log ((w - 1 : ℕ) : ℝ)) ^ k := by
        dsimp [f]
        have hk_eq : k = (k - 1) + 1 := by omega
        conv_rhs => rw [hk_eq, pow_succ]
        ring
      have hpow_w_le : (Real.log ((w - 1 : ℕ) : ℝ)) ^ k ≤ (Real.log w) ^ k :=
        pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ w - 1)))
          (Real.log_le_log (by exact_mod_cast (by omega : 0 < w - 1)) (by exact_mod_cast (by omega : w - 1 ≤ w))) _
      have hlog2_le : (Real.log 2) ^ k ≤ (Real.log w) ^ (k - 1) := by
        have hlog2_lt1 : Real.log 2 ≤ 1 := by
          have : (2 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) (Real.add_one_le_exp 1)
          exact (Real.log_le_iff_le_exp (by norm_num)).mpr this
        have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have hlog2_le_w : Real.log 2 ≤ Real.log (w : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ w))
        have hk_eq : k = (k - 1) + 1 := by omega
        calc (Real.log 2) ^ k = (Real.log 2) ^ (k - 1) * Real.log 2 := by conv_lhs => rw [hk_eq, pow_succ]
          _ ≤ (Real.log w) ^ (k - 1) * 1 :=
            mul_le_mul (pow_le_pow_left₀ hlog2_nn hlog2_le_w _) hlog2_lt1 hlog2_nn (pow_nonneg hlogw_pos.le _)
          _ = (Real.log w) ^ (k - 1) := mul_one _
      have hf2_nn : 0 ≤ f 2 := hf_nonneg 2 (by omega)
      have hmain_comb : S (w - 1) * f (w - 1) ≤ (Real.log ((w - 1 : ℕ) : ℝ)) ^ k + C₁ * (Real.log w) ^ (k - 1) := by
        calc S (w - 1) * f (w - 1)
            ≤ (Real.log ((w - 1 : ℕ) : ℝ) + C₁) * f (w - 1) :=
              mul_le_mul_of_nonneg_right hSw_ub (hf_nonneg (w - 1) (by omega))
          _ = (Real.log ((w - 1 : ℕ) : ℝ)) ^ k + C₁ * f (w - 1) := by rw [add_mul, hlogw_m1]
          _ ≤ (Real.log ((w - 1 : ℕ) : ℝ)) ^ k + C₁ * (Real.log w) ^ (k - 1) := by
              gcongr
      have hcoeff_le : ((k : ℝ) - 1) / (k : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have hterm1 : (Real.log ((w - 1 : ℕ) : ℝ)) ^ k -
          ((k : ℝ) - 1) / (k : ℝ) * (Real.log ((w - 1 : ℕ) : ℝ)) ^ k ≤
            (Real.log w) ^ k / (k : ℝ) := by
        have : (Real.log ((w - 1 : ℕ) : ℝ)) ^ k -
            ((k : ℝ) - 1) / (k : ℝ) * (Real.log ((w - 1 : ℕ) : ℝ)) ^ k =
              (Real.log ((w - 1 : ℕ) : ℝ)) ^ k / (k : ℝ) := by
          have hk0 : (k : ℝ) ≠ 0 := by positivity
          field_simp; ring
        rw [this]
        exact div_le_div_of_nonneg_right hpow_w_le (by positivity)
      have hC1_f : C₁ * (f (w - 1) - f 2) ≤ C₁ * (Real.log w) ^ (k - 1) := by
        nlinarith
      have hlog2_term : ((k : ℝ) - 1) / (k : ℝ) * (Real.log 2) ^ k ≤ (Real.log w) ^ (k - 1) := by
        calc ((k : ℝ) - 1) / (k : ℝ) * (Real.log 2) ^ k
            ≤ 1 * (Real.log w) ^ (k - 1) :=
              mul_le_mul hcoeff_le hlog2_le (pow_nonneg (Real.log_nonneg (by norm_num)) _) zero_le_one
          _ = (Real.log w) ^ (k - 1) := one_mul _
      have hpos_lw : 0 ≤ (Real.log w) ^ (k - 1) := pow_nonneg hlogw_pos.le _
      have hfinal_c : (2 * C₁ + (k : ℝ) + 1) * (Real.log w) ^ (k - 1) ≤
          (2 * C₁ + (k : ℝ) * 2 + 2) * (Real.log w) ^ (k - 1) := by
        apply mul_le_mul_of_nonneg_right _ hpos_lw
        have : (0 : ℝ) ≤ (k : ℝ) := by positivity
        linarith
      have hwd : w - 1 - 1 = w - 2 := by omega
      rw [hwd]
      linarith [hmain_comb, hsum_lb, hsum_split, hsum_log_lb, hterm1, hC1_f, hlog2_term, hfinal_c]

/-- `Ein_ub c = c + c^2/4 + c^3/18 + c^4/96 + (exp c / 600) * c^5`. -/
noncomputable def EinUb (c : ℝ) : ℝ :=
  c + c ^ 2 / 4 + c ^ 3 / 18 + c ^ 4 / 96 + (Real.exp c / 600) * c ^ 5

/-- Convergent tail bound: `∑_{p > P₀} log p / (p * (p - 7))` is uniformly bounded by a constant. -/
lemma sum_log_div_p_mul_sub7_le (P₀ : ℕ) (hP₀ : 100 ≤ P₀) :
    ∃ B : ℝ, 0 < B ∧ ∀ w : ℕ,
      ∑ p ∈ (Ioo P₀ w).filter Nat.Prime, Real.log p / ((p : ℝ) * ((p : ℝ) - 7)) ≤ B := by
  have hsumm : Summable (fun p : ℕ => (4 : ℝ) / ((p : ℝ) ^ ((3 : ℝ) / 2))) := by
    simpa [div_eq_mul_inv] using (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3 / 2)).mul_left 4
  refine ⟨(∑' p : ℕ, (4 : ℝ) / ((p : ℝ) ^ ((3 : ℝ) / 2))) + 1, by
    have hnn : 0 ≤ ∑' p : ℕ, (4 : ℝ) / ((p : ℝ) ^ ((3 : ℝ) / 2)) :=
      tsum_nonneg fun p => by positivity
    linarith, fun w => ?_⟩
  calc ∑ p ∈ (Ioo P₀ w).filter Nat.Prime, Real.log p / ((p : ℝ) * ((p : ℝ) - 7))
      ≤ ∑ p ∈ (Ioo P₀ w).filter Nat.Prime, (4 : ℝ) / ((p : ℝ) ^ ((3 : ℝ) / 2)) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp100 : 100 < p := lt_of_le_of_lt hP₀ (mem_Ioo.mp (mem_filter.mp hp).1).1
        have hpr : (100 : ℝ) < p := by exact_mod_cast hp100
        have hp0 : (0 : ℝ) < p := by linarith
        have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
        have hlog : Real.log p ≤ 2 * Real.sqrt p := by
          have := Real.log_le_sub_one_of_pos hs
          rw [Real.log_sqrt hp0.le] at this
          linarith
        have hsub : (p : ℝ) / 2 ≤ (p : ℝ) - 7 := by linarith
        have h32 : (p : ℝ) ^ ((3 : ℝ) / 2) = (p : ℝ) * Real.sqrt p := by
          rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hp0, Real.rpow_one, Real.sqrt_eq_rpow]
        have hden1 : 0 < (p : ℝ) * ((p : ℝ) - 7) := mul_pos hp0 (by linarith)
        have hden2 : 0 < (p : ℝ) * Real.sqrt p := mul_pos hp0 hs
        rw [h32, div_le_div_iff₀ hden1 hden2]
        have hmul_sq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
        nlinarith [mul_le_mul_of_nonneg_right hlog hden2.le]
    _ ≤ ∑' p : ℕ, (4 : ℝ) / ((p : ℝ) ^ ((3 : ℝ) / 2)) :=
        hsumm.sum_le_tsum _ (fun p _ => by positivity)
    _ ≤ _ := by linarith

/-- Key Rankin exponential sum bound:
`∑_{P₀ < p < w} (7 / (p - 7)) * (p^(c / log w) - 1) <= 7 * EinUb c + C / log w`. -/
lemma sum_h_rpow_sub_one_le (P₀ : ℕ) (hP₀ : 100 ≤ P₀) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℕ, P₀ < w →
      ∑ p ∈ (Ioo P₀ w).filter Nat.Prime,
        (7 / ((p : ℝ) - 7)) * ((p : ℝ) ^ (c / Real.log w) - 1) ≤
          7 * EinUb c + C / Real.log w := by
  obtain ⟨C1, hC1p, h1⟩ := sum_log_pow_div_p_le 1 (by norm_num)
  obtain ⟨C2, hC2p, h2⟩ := sum_log_pow_div_p_le 2 (by norm_num)
  obtain ⟨C3, hC3p, h3⟩ := sum_log_pow_div_p_le 3 (by norm_num)
  obtain ⟨C4, hC4p, h4⟩ := sum_log_pow_div_p_le 4 (by norm_num)
  obtain ⟨C5, hC5p, h5⟩ := sum_log_pow_div_p_le 5 (by norm_num)
  obtain ⟨B, hBp, hB⟩ := sum_log_div_p_mul_sub7_le P₀ hP₀
  refine ⟨7 * (c * C1 + c ^ 2 / 2 * C2 + c ^ 3 / 6 * C3 + c ^ 4 / 24 * C4 +
      (Real.exp c / 120) * c ^ 5 * C5) + 49 * c * Real.exp c * B + 1, by positivity, fun w hw => ?_⟩
  have hw2 : 2 ≤ w := by omega
  have hlw : 0 < Real.log (w : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < w))
  have hsub_oo : (Ioo P₀ w).filter Nat.Prime ⊆ (Ioo 0 w).filter Nat.Prime := by
    intro p hp
    simp only [mem_filter, mem_Ioo] at hp ⊢
    exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
  have hterm : ∀ p ∈ (Ioo P₀ w).filter Nat.Prime,
      (7 / ((p : ℝ) - 7)) * ((p : ℝ) ^ (c / Real.log w) - 1) ≤
        7 * (c / Real.log w * (Real.log p / p) +
             (c ^ 2 / (2 * (Real.log w) ^ 2)) * ((Real.log p) ^ 2 / p) +
             (c ^ 3 / (6 * (Real.log w) ^ 3)) * ((Real.log p) ^ 3 / p) +
             (c ^ 4 / (24 * (Real.log w) ^ 4)) * ((Real.log p) ^ 4 / p) +
             ((Real.exp c / 120) * c ^ 5 / (Real.log w) ^ 5) * ((Real.log p) ^ 5 / p)) +
        49 * c * Real.exp c / Real.log w * (Real.log p / ((p : ℝ) * ((p : ℝ) - 7))) := by
    intro p hp
    have hp_lo := (mem_Ioo.mp (mem_filter.mp hp).1).1
    have hp_hi := (mem_Ioo.mp (mem_filter.mp hp).1).2
    have hpr : (100 : ℝ) < p := by exact_mod_cast (lt_of_le_of_lt hP₀ hp_lo)
    have hp0 : (0 : ℝ) < p := by linarith
    have hp7 : (0 : ℝ) < (p : ℝ) - 7 := by linarith
    set t := c * Real.log p / Real.log w
    have hlp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
    have hlp_le : Real.log (p : ℝ) ≤ Real.log (w : ℝ) :=
      Real.log_le_log hp0 (by exact_mod_cast hp_hi.le)
    have ht0 : 0 ≤ t := by dsimp [t]; positivity
    have htc : t ≤ c := by
      dsimp [t]
      rw [div_le_iff₀ hlw]
      exact mul_le_mul_of_nonneg_left hlp_le hc.le
    have hrpow : (p : ℝ) ^ (c / Real.log w) = Real.exp t := by
      rw [Real.rpow_def_of_pos hp0]
      dsimp [t]
      ring_nf
    rw [hrpow]
    have hsplit : (7 : ℝ) / ((p : ℝ) - 7) = 7 / (p : ℝ) + 49 / ((p : ℝ) * ((p : ℝ) - 7)) := by
      field_simp; ring
    rw [hsplit, add_mul]
    have hpoly := exp_sub_one_le_poly ht0 htc
    have hlin : Real.exp t - 1 ≤ Real.exp c * t := by
      have hexp_mv : Real.exp t - 1 ≤ t * Real.exp t := by
        have := Real.add_one_le_exp (-t)
        have hmul := mul_le_mul_of_nonneg_right this (Real.exp_pos t).le
        rw [add_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
        linarith
      calc Real.exp t - 1 ≤ t * Real.exp t := hexp_mv
        _ ≤ t * Real.exp c := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htc) ht0
        _ = Real.exp c * t := mul_comm _ _
    have hpart1 : 7 / (p : ℝ) * (Real.exp t - 1) ≤
        7 * (c / Real.log w * (Real.log p / p) +
             (c ^ 2 / (2 * (Real.log w) ^ 2)) * ((Real.log p) ^ 2 / p) +
             (c ^ 3 / (6 * (Real.log w) ^ 3)) * ((Real.log p) ^ 3 / p) +
             (c ^ 4 / (24 * (Real.log w) ^ 4)) * ((Real.log p) ^ 4 / p) +
             ((Real.exp c / 120) * c ^ 5 / (Real.log w) ^ 5) * ((Real.log p) ^ 5 / p)) := by
      calc 7 / (p : ℝ) * (Real.exp t - 1)
          ≤ 7 / (p : ℝ) * (t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 + (Real.exp c / 120) * t ^ 5) :=
            mul_le_mul_of_nonneg_left hpoly (by positivity)
        _ = _ := by dsimp [t]; field_simp
    have hpart2 : 49 / ((p : ℝ) * ((p : ℝ) - 7)) * (Real.exp t - 1) ≤
        49 * c * Real.exp c / Real.log w * (Real.log p / ((p : ℝ) * ((p : ℝ) - 7))) := by
      calc 49 / ((p : ℝ) * ((p : ℝ) - 7)) * (Real.exp t - 1)
          ≤ 49 / ((p : ℝ) * ((p : ℝ) - 7)) * (Real.exp c * t) :=
            mul_le_mul_of_nonneg_left hlin (by positivity)
        _ = _ := by dsimp [t]; ring
    exact add_le_add hpart1 hpart2
  have hsum_k : ∀ (k : ℕ) (Ck : ℝ),
      ∑ p ∈ (Ioo 0 w).filter Nat.Prime, (Real.log p) ^ k / (p : ℝ) ≤
        (Real.log w) ^ k / (k : ℝ) + Ck * (Real.log w) ^ (k - 1) →
      ∑ p ∈ (Ioo P₀ w).filter Nat.Prime, (Real.log p) ^ k / (p : ℝ) ≤
        (Real.log w) ^ k / (k : ℝ) + Ck * (Real.log w) ^ (k - 1) := by
    intro k Ck hk
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub_oo fun p hp _ => ?_) hk
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.one_lt.le
    exact div_nonneg (pow_nonneg (Real.log_nonneg hp1) k) (Nat.cast_nonneg p)
  have hs1 : ∑ p ∈ (Ioo P₀ w).filter Nat.Prime, Real.log p / (p : ℝ) ≤ Real.log w + C1 := by
    have := hsum_k 1 C1 (h1 w hw2)
    simpa only [pow_one, Nat.cast_one, div_one, Nat.sub_self, pow_zero, mul_one] using this
  have hs2 : ∑ p ∈ (Ioo P₀ w).filter Nat.Prime, (Real.log p) ^ 2 / (p : ℝ) ≤ (Real.log w) ^ 2 / 2 + C2 * Real.log w := by
    have := hsum_k 2 C2 (h2 w hw2)
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using this
  have hs3 : ∑ p ∈ (Ioo P₀ w).filter Nat.Prime, (Real.log p) ^ 3 / (p : ℝ) ≤ (Real.log w) ^ 3 / 3 + C3 * (Real.log w) ^ 2 := by
    have := hsum_k 3 C3 (h3 w hw2)
    simpa only [Nat.cast_ofNat] using this
  have hs4 : ∑ p ∈ (Ioo P₀ w).filter Nat.Prime, (Real.log p) ^ 4 / (p : ℝ) ≤ (Real.log w) ^ 4 / 4 + C4 * (Real.log w) ^ 3 := by
    have := hsum_k 4 C4 (h4 w hw2)
    simpa only [Nat.cast_ofNat] using this
  have hs5 : ∑ p ∈ (Ioo P₀ w).filter Nat.Prime, (Real.log p) ^ 5 / (p : ℝ) ≤ (Real.log w) ^ 5 / 5 + C5 * (Real.log w) ^ 4 := by
    have := hsum_k 5 C5 (h5 w hw2)
    simpa only [Nat.cast_ofNat] using this
  have hsB := hB w
  calc ∑ p ∈ (Ioo P₀ w).filter Nat.Prime, (7 / ((p : ℝ) - 7)) * ((p : ℝ) ^ (c / Real.log w) - 1)
      ≤ ∑ p ∈ (Ioo P₀ w).filter Nat.Prime,
          (7 * (c / Real.log w * (Real.log p / p) +
               (c ^ 2 / (2 * (Real.log w) ^ 2)) * ((Real.log p) ^ 2 / p) +
               (c ^ 3 / (6 * (Real.log w) ^ 3)) * ((Real.log p) ^ 3 / p) +
               (c ^ 4 / (24 * (Real.log w) ^ 4)) * ((Real.log p) ^ 4 / p) +
               ((Real.exp c / 120) * c ^ 5 / (Real.log w) ^ 5) * ((Real.log p) ^ 5 / p)) +
           49 * c * Real.exp c / Real.log w * (Real.log p / ((p : ℝ) * ((p : ℝ) - 7)))) :=
        Finset.sum_le_sum hterm
    _ = 7 * (c / Real.log w * (∑ p ∈ (Ioo P₀ w).filter Nat.Prime, Real.log p / p) +
             (c ^ 2 / (2 * (Real.log w) ^ 2)) * (∑ p ∈ (Ioo P₀ w).filter Nat.Prime, (Real.log p) ^ 2 / p) +
             (c ^ 3 / (6 * (Real.log w) ^ 3)) * (∑ p ∈ (Ioo P₀ w).filter Nat.Prime, (Real.log p) ^ 3 / p) +
             (c ^ 4 / (24 * (Real.log w) ^ 4)) * (∑ p ∈ (Ioo P₀ w).filter Nat.Prime, (Real.log p) ^ 4 / p) +
             ((Real.exp c / 120) * c ^ 5 / (Real.log w) ^ 5) * (∑ p ∈ (Ioo P₀ w).filter Nat.Prime, (Real.log p) ^ 5 / p)) +
        49 * c * Real.exp c / Real.log w *
          (∑ p ∈ (Ioo P₀ w).filter Nat.Prime, Real.log p / ((p : ℝ) * ((p : ℝ) - 7))) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 7 * (c / Real.log w * (Real.log w + C1) +
             (c ^ 2 / (2 * (Real.log w) ^ 2)) * ((Real.log w) ^ 2 / 2 + C2 * Real.log w) +
             (c ^ 3 / (6 * (Real.log w) ^ 3)) * ((Real.log w) ^ 3 / 3 + C3 * (Real.log w) ^ 2) +
             (c ^ 4 / (24 * (Real.log w) ^ 4)) * ((Real.log w) ^ 4 / 4 + C4 * (Real.log w) ^ 3) +
             ((Real.exp c / 120) * c ^ 5 / (Real.log w) ^ 5) * ((Real.log w) ^ 5 / 5 + C5 * (Real.log w) ^ 4)) +
        49 * c * Real.exp c / Real.log w * B := by
        gcongr
    _ ≤ 7 * EinUb c +
        (7 * (c * C1 + c ^ 2 / 2 * C2 + c ^ 3 / 6 * C3 + c ^ 4 / 24 * C4 +
          (Real.exp c / 120) * c ^ 5 * C5) + 49 * c * Real.exp c * B + 1) / Real.log w := by
        unfold EinUb
        have hlw0 : Real.log (w : ℝ) ≠ 0 := hlw.ne'
        have hpos : (0 : ℝ) < 1 / Real.log w := by positivity
        have heq : 7 * (c / Real.log w * (Real.log w + C1) +
             (c ^ 2 / (2 * (Real.log w) ^ 2)) * ((Real.log w) ^ 2 / 2 + C2 * Real.log w) +
             (c ^ 3 / (6 * (Real.log w) ^ 3)) * ((Real.log w) ^ 3 / 3 + C3 * (Real.log w) ^ 2) +
             (c ^ 4 / (24 * (Real.log w) ^ 4)) * ((Real.log w) ^ 4 / 4 + C4 * (Real.log w) ^ 3) +
             ((Real.exp c / 120) * c ^ 5 / (Real.log w) ^ 5) * ((Real.log w) ^ 5 / 5 + C5 * (Real.log w) ^ 4)) +
            49 * c * Real.exp c / Real.log w * B =
            7 * (c + c ^ 2 / 4 + c ^ 3 / 18 + c ^ 4 / 96 + (Real.exp c / 600) * c ^ 5) +
            (7 * (c * C1 + c ^ 2 / 2 * C2 + c ^ 3 / 6 * C3 + c ^ 4 / 24 * C4 +
              (Real.exp c / 120) * c ^ 5 * C5) + 49 * c * Real.exp c * B) / Real.log w := by
          field_simp; ring
        rw [heq]
        apply add_le_add_right
        exact div_le_div_of_nonneg_right (by linarith) hlw.le

/-- The 7-dimensional sieve product `V7 P₀ w = ∏_{P₀ < p < w, p prime} (1 - 7/p)`. -/
noncomputable def V7 (P₀ w : ℕ) : ℝ :=
  ∏ p ∈ (Ioo P₀ w).filter Nat.Prime, (1 - 7 / (p : ℝ))

lemma V7_pos {P₀ w : ℕ} (hP₀ : 100 ≤ P₀) : 0 < V7 P₀ w := by
  unfold V7
  refine Finset.prod_pos fun p hp => ?_
  have hp100 : 100 < p := lt_of_le_of_lt hP₀ (mem_Ioo.mp (mem_filter.mp hp).1).1
  have hpr : (100 : ℝ) < p := by exact_mod_cast hp100
  have : 7 / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  linarith

/-- Comparison between `log (1 - 7/p)` and `7 * log (1 - 1/p)` for `p > 100`. -/
lemma abs_log_one_sub_seven_sub_seven_log_one_sub_one {p : ℕ} (hp : 100 < p) :
    |Real.log (1 - 7 / (p : ℝ)) - 7 * Real.log (1 - 1 / (p : ℝ))| ≤ 100 / ((p : ℝ) ^ 2) := by
  have hpr : (100 : ℝ) < p := by exact_mod_cast hp
  have hlog2 : ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 2 → -u - 2 * u ^ 2 ≤ Real.log (1 - u) ∧ Real.log (1 - u) ≤ -u := by
    intro u hu0 hu2
    have h1u : 0 < 1 - u := by linarith
    constructor
    · have h1 : -Real.log (1 - u) ≤ u / (1 - u) := by
        rw [← Real.log_inv]
        calc Real.log (1 - u)⁻¹ ≤ (1 - u)⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr h1u)
          _ = u / (1 - u) := by field_simp; ring
      have h2 : u / (1 - u) ≤ u + 2 * u ^ 2 := by
        rw [div_le_iff₀ h1u]
        nlinarith
      linarith
    · linarith [Real.log_le_sub_one_of_pos h1u]
  have hu7 := hlog2 (7 / (p : ℝ)) (by positivity) (by rw [div_le_iff₀ (by linarith)]; linarith)
  have hu1 := hlog2 (1 / (p : ℝ)) (by positivity) (by rw [div_le_iff₀ (by linarith)]; linarith)
  have hsq7 : 2 * (7 / (p : ℝ)) ^ 2 = 98 / (p : ℝ) ^ 2 := by ring
  have hsq1 : 7 * (2 * (1 / (p : ℝ)) ^ 2) = 14 / (p : ℝ) ^ 2 := by ring
  have hnn : (0 : ℝ) ≤ 1 / (p : ℝ) ^ 2 := by positivity
  have hzero : -(7 / (p : ℝ)) - 7 * (-(1 / (p : ℝ))) = 0 := by ring
  rw [abs_le]
  constructor
  · have : 98 / (p : ℝ) ^ 2 ≤ 100 / (p : ℝ) ^ 2 := by linarith [show 100 / (p : ℝ) ^ 2 - 98 / (p : ℝ) ^ 2 = 2 * (1 / (p : ℝ) ^ 2) by ring]
    linarith [hu7.1, hu1.2, hsq7, this, hzero]
  · have : 14 / (p : ℝ) ^ 2 ≤ 100 / (p : ℝ) ^ 2 := by linarith [show 100 / (p : ℝ) ^ 2 - 14 / (p : ℝ) ^ 2 = 86 * (1 / (p : ℝ) ^ 2) by ring]
    linarith [hu7.2, hu1.1, hsq1, this, hzero]

/-- Mertens 3rd theorem for `V7`: both order `Θ((log w)^{-7})` and sharp ratio `V7(p)/V7(w)`. -/
lemma V7_asymptotics (P₀ : ℕ) (hP₀ : 100 ≤ P₀) :
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ w : ℕ, P₀ < w →
      c₁ / (Real.log w) ^ 7 ≤ V7 P₀ w ∧ V7 P₀ w ≤ c₂ / (Real.log w) ^ 7) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ p w : ℕ, P₀ < p → p ≤ w →
      V7 P₀ p / V7 P₀ w ≤ Real.exp (C / Real.log p) * (Real.log w / Real.log p) ^ 7) := by
  obtain ⟨C₃, hC₃⟩ := Mertens.E₃.abs_le
  set C₃' := max C₃ 1
  have hC₃'p : 0 < C₃' := lt_of_lt_of_le one_pos (le_max_right _ _)
  let Ldiff (n : ℕ) : ℝ :=
    ∑ p ∈ (Ioo P₀ n).filter Nat.Prime, (Real.log (1 - 7 / (p : ℝ)) - 7 * Real.log (1 - 1 / (p : ℝ)))
  have hLdiff_bound : ∀ m n : ℕ, P₀ ≤ m → m ≤ n →
      |Ldiff n - Ldiff m| ≤ 200 / (m : ℝ) := by
    intro m n hm hmn
    have hm100 : 100 ≤ m := hP₀.trans hm
    have hsub : (Ioo P₀ m).filter Nat.Prime ⊆ (Ioo P₀ n).filter Nat.Prime := by
      intro p hp; simp only [mem_filter, mem_Ioo] at hp ⊢; exact ⟨⟨hp.1.1, lt_of_lt_of_le hp.1.2 hmn⟩, hp.2⟩
    have hsdiff : (Ioo P₀ n).filter Nat.Prime \ (Ioo P₀ m).filter Nat.Prime =
        (Ico (max (P₀ + 1) m) n).filter Nat.Prime := by
      ext p; simp only [Finset.mem_sdiff, mem_filter, mem_Ioo, mem_Ico, max_le_iff]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, hp⟩, hnot⟩
        refine ⟨⟨⟨by omega, ?_⟩, h2⟩, hp⟩
        by_contra hlt; push Not at hlt; exact hnot ⟨⟨h1, hlt⟩, hp⟩
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, hp⟩
        exact ⟨⟨⟨by omega, h3⟩, hp⟩, fun h => by omega⟩
    dsimp [Ldiff]
    rw [← Finset.sum_sdiff hsub, add_sub_cancel_right, hsdiff]
    set m' := max (P₀ + 1) m
    have hm_le_m' : m ≤ m' := le_max_right _ _
    have htele : ∀ K : ℕ, m' ≤ K →
        ∑ p ∈ Ico m' K, ((1 : ℝ) / (p : ℝ) - (1 : ℝ) / ((p : ℝ) + 1)) = 1 / (m' : ℝ) - 1 / (K : ℝ) := by
      intro K hK
      induction K, hK using Nat.le_induction with
      | base => simp
      | succ t ht iht =>
        have hIt : Ico m' (t + 1) = insert t (Ico m' t) := by
          ext x; simp only [mem_Ico, mem_insert]; omega
        have hnt : t ∉ Ico m' t := by simp
        rw [hIt, Finset.sum_insert hnt, iht]
        push_cast; ring
    by_cases hmn' : n < m'
    · have hempty : (Ico m' n).filter Nat.Prime = ∅ := by ext p; simp; omega
      rw [hempty, Finset.sum_empty, abs_zero]
      positivity
    · push Not at hmn'
      calc |∑ p ∈ (Ico m' n).filter Nat.Prime, (Real.log (1 - 7 / (p : ℝ)) - 7 * Real.log (1 - 1 / (p : ℝ)))|
          ≤ ∑ p ∈ (Ico m' n).filter Nat.Prime, |Real.log (1 - 7 / (p : ℝ)) - 7 * Real.log (1 - 1 / (p : ℝ))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ (Ico m' n).filter Nat.Prime, 100 / ((p : ℝ) ^ 2) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hp_lo : P₀ + 1 ≤ p := (le_max_left _ _).trans (mem_Ico.mp (mem_filter.mp hp).1).1
            exact abs_log_one_sub_seven_sub_seven_log_one_sub_one (by omega)
        _ ≤ ∑ p ∈ Ico m' n, 200 * ((1 : ℝ) / (p : ℝ) - (1 : ℝ) / ((p : ℝ) + 1)) := by
            refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => by positivity)) (Finset.sum_le_sum fun p hp => ?_)
            have hp_lo : 100 ≤ p := hm100.trans (hm_le_m'.trans (mem_Ico.mp hp).1)
            have hpr : (100 : ℝ) ≤ p := by exact_mod_cast hp_lo
            have hp0 : (0 : ℝ) < p := by linarith
            have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by linarith
            rw [div_sub_div _ _ hp0.ne' hp1.ne', mul_div_assoc', div_le_div_iff₀ (sq_pos_of_pos hp0) (mul_pos hp0 hp1)]
            nlinarith
        _ = 200 * (1 / (m' : ℝ) - 1 / (n : ℝ)) := by rw [← Finset.mul_sum, htele n hmn']
        _ ≤ 200 / (m' : ℝ) := by
            have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
            linarith [show 200 * (1 / (m' : ℝ)) = 200 / (m' : ℝ) by ring]
        _ ≤ 200 / (m : ℝ) :=
            div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast (by omega : 0 < m)) (by exact_mod_cast hm_le_m')
  let Q1 (n : ℕ) : ℝ := ∏ p ∈ (Ioc 0 n).filter Nat.Prime, (1 - 1 / (p : ℝ))
  have hQ1_pos : ∀ n : ℕ, 0 < Q1 n := fun n => Finset.prod_pos fun p hp => by
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
    have : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  have hV7_eq : ∀ n : ℕ, P₀ < n →
      V7 P₀ n = (Q1 (n - 1) / Q1 P₀) ^ 7 * Real.exp (Ldiff n) := by
    intro n hn
    have hlogV : Real.log (V7 P₀ n) = ∑ p ∈ (Ioo P₀ n).filter Nat.Prime, Real.log (1 - 7 / (p : ℝ)) := by
      unfold V7
      rw [Real.log_prod]
      intro p hp
      have hp100 : (100 : ℝ) < p := by exact_mod_cast lt_of_le_of_lt hP₀ (mem_Ioo.mp (mem_filter.mp hp).1).1
      have : 7 / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
      linarith
    have hQ_ratio : Q1 (n - 1) / Q1 P₀ = ∏ p ∈ (Ioo P₀ n).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
      unfold Q1
      have hsub : (Ioc 0 P₀).filter Nat.Prime ⊆ (Ioc 0 (n - 1)).filter Nat.Prime := by
        intro p hp; simp only [mem_filter, mem_Ioc] at hp ⊢; exact ⟨⟨hp.1.1, by omega⟩, hp.2⟩
      have hsdiff : (Ioc 0 (n - 1)).filter Nat.Prime \ (Ioc 0 P₀).filter Nat.Prime =
          (Ioo P₀ n).filter Nat.Prime := by
        ext p; simp only [Finset.mem_sdiff, mem_filter, mem_Ioc, mem_Ioo]
        constructor
        · rintro ⟨⟨⟨h1, h2⟩, hp⟩, hnot⟩
          refine ⟨⟨?_, by omega⟩, hp⟩
          by_contra hle; push Not at hle; exact hnot ⟨⟨h1, hle⟩, hp⟩
        · rintro ⟨⟨h1, h2⟩, hp⟩
          exact ⟨⟨⟨by omega, by omega⟩, hp⟩, fun h => by omega⟩
      rw [← Finset.prod_sdiff hsub, hsdiff, mul_div_cancel_right₀ _ (hQ1_pos P₀).ne']
    have hlogQ : Real.log ((Q1 (n - 1) / Q1 P₀) ^ 7) =
        ∑ p ∈ (Ioo P₀ n).filter Nat.Prime, 7 * Real.log (1 - 1 / (p : ℝ)) := by
      rw [Real.log_pow, hQ_ratio, Real.log_prod, Finset.mul_sum]
      · refine Finset.sum_congr rfl fun p _ => by norm_num
      · intro p hp
        have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
        have : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
        linarith
    have hVpos := V7_pos (w := n) hP₀
    have hQpos : 0 < (Q1 (n - 1) / Q1 P₀) ^ 7 := pow_pos (div_pos (hQ1_pos (n - 1)) (hQ1_pos P₀)) 7
    rw [← Real.exp_log hVpos, ← Real.exp_log hQpos, ← Real.exp_add]
    congr 1
    rw [hlogV, hlogQ]
    dsimp [Ldiff]
    rw [Finset.sum_sub_distrib]
    ring
  have hQ1_mert : ∀ n : ℕ, 2 ≤ n →
      Q1 n = Real.exp (-Real.eulerMascheroniConstant) * Real.exp (Mertens.E₃ (n : ℝ)) / Real.log (n : ℝ) := by
    intro n hn
    have h := Mertens.prod_one_minus_div_prime_eq (x := (n : ℝ)) (by exact_mod_cast (by omega : 1 < n))
    simpa [Q1, Nat.floor_natCast] using h
  have hlog_pred : ∀ n : ℕ, 100 < n →
      Real.log ((n - 1 : ℕ) : ℝ) ≤ Real.log (n : ℝ) ∧
      Real.log (n : ℝ) ≤ Real.log ((n - 1 : ℕ) : ℝ) + 2 / (n : ℝ) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn1 : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (by omega : 0 < n - 1)
    constructor
    · exact Real.log_le_log hn1 (by exact_mod_cast (by omega : n - 1 ≤ n))
    · have hdiv : Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ) = Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) :=
        (Real.log_div hn0.ne' hn1.ne').symm
      have h1 : Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤ (n : ℝ) / ((n - 1 : ℕ) : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hn0 hn1)
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      have hnr : (100 : ℝ) < n := by exact_mod_cast hn
      have h2 : (n : ℝ) / ((n : ℝ) - 1) - 1 ≤ 2 / (n : ℝ) := by
        have hsub0 : (n : ℝ) - 1 ≠ 0 := by linarith
        have : (n : ℝ) / ((n : ℝ) - 1) - 1 = 1 / ((n : ℝ) - 1) := by field_simp; ring
        rw [this, div_le_div_iff₀ (by linarith) hn0]
        linarith
      rw [hcast] at h1
      conv_rhs at hdiv => rw [hcast]
      linarith [hdiv, h1, h2]
  have hlog_ge2 : ∀ n : ℕ, 100 ≤ n → 2 ≤ Real.log (n : ℝ) := by
    intro n hn
    have hexp2 : Real.exp 2 ≤ (n : ℝ) := by
      have h1 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have hnr : (100 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [Real.exp_pos 1]
    exact (Real.le_log_iff_exp_le (by exact_mod_cast (by omega : 0 < n))).mpr hexp2
  constructor
  · let K := Real.exp (-7 * Real.eulerMascheroniConstant) / (Q1 P₀) ^ 7
    have hKpos : 0 < K := div_pos (Real.exp_pos _) (pow_pos (hQ1_pos P₀) 7)
    refine ⟨K * Real.exp (-7 * C₃' - 2) / 2 ^ 7, K * Real.exp (7 * C₃' + 2) * 2 ^ 7,
      by positivity, by positivity, fun w hw => ?_⟩
    have hw100 : 100 < w := lt_of_le_of_lt hP₀ hw
    have hl1 := hlog_ge2 (w - 1) (by omega)
    have hl2 := hlog_ge2 w (by omega)
    have hlp := hlog_pred w hw100
    have hlog_ratio_ub : Real.log (w : ℝ) / Real.log ((w - 1 : ℕ) : ℝ) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      have : 2 / (w : ℝ) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast (by omega : 0 < w))]; exact_mod_cast (by omega : 2 ≤ w)
      linarith
    have hlog_ratio_lb : 1 ≤ Real.log (w : ℝ) / Real.log ((w - 1 : ℕ) : ℝ) :=
      (one_le_div (by linarith)).mpr hlp.1
    have hE3 := hC₃ ((w - 1 : ℕ) : ℝ) (by exact_mod_cast (by omega : 2 ≤ w - 1))
    have hE3' : |Mertens.E₃ ((w - 1 : ℕ) : ℝ)| ≤ C₃' := by
      have h1 : C₃ / Real.log ((w - 1 : ℕ) : ℝ) ≤ C₃' / 1 := by
        calc C₃ / Real.log ((w - 1 : ℕ) : ℝ)
            ≤ C₃' / Real.log ((w - 1 : ℕ) : ℝ) := div_le_div_of_nonneg_right (le_max_left _ _) (by linarith)
          _ ≤ C₃' / 1 := div_le_div_of_nonneg_left hC₃'p.le zero_lt_one (by linarith)
      linarith [div_one C₃']
    have hLd := hLdiff_bound P₀ w le_rfl hw.le
    have hLd0 : Ldiff P₀ = 0 := by
      dsimp [Ldiff]
      have : (Ioo P₀ P₀).filter Nat.Prime = ∅ := by ext x; simp
      rw [this, Finset.sum_empty]
    rw [hLd0, sub_zero] at hLd
    have hLd2 : |Ldiff w| ≤ 2 := by
      have : 200 / (P₀ : ℝ) ≤ 2 := by
        rw [div_le_iff₀ (by exact_mod_cast (by omega : 0 < P₀))]
        have : (100 : ℝ) ≤ P₀ := by exact_mod_cast hP₀
        linarith
      exact hLd.trans this
    rw [hV7_eq w hw, hQ1_mert (w - 1) (by omega)]
    have hrew : (Real.exp (-Real.eulerMascheroniConstant) * Real.exp (Mertens.E₃ ((w - 1 : ℕ) : ℝ)) /
        Real.log ((w - 1 : ℕ) : ℝ) / Q1 P₀) ^ 7 * Real.exp (Ldiff w) =
        K * Real.exp (7 * Mertens.E₃ ((w - 1 : ℕ) : ℝ) + Ldiff w) *
          (Real.log (w : ℝ) / Real.log ((w - 1 : ℕ) : ℝ)) ^ 7 / (Real.log (w : ℝ)) ^ 7 := by
      dsimp [K]
      simp only [div_pow, mul_pow, ← Real.exp_nat_mul]
      rw [Real.exp_add]
      have hQ0 := (hQ1_pos P₀).ne'
      have hlw0 : Real.log (w : ℝ) ≠ 0 := by linarith
      have hlwm0 : Real.log ((w - 1 : ℕ) : ℝ) ≠ 0 := by linarith
      have he1 : ((7 : ℕ) : ℝ) * (-Real.eulerMascheroniConstant) = -7 * Real.eulerMascheroniConstant := by push_cast; ring
      have he2 : ((7 : ℕ) : ℝ) * Mertens.E₃ ((w - 1 : ℕ) : ℝ) = 7 * Mertens.E₃ ((w - 1 : ℕ) : ℝ) := by norm_num
      rw [he1, he2]
      field_simp
    rw [hrew]
    have hE_abs := abs_le.mp hE3'
    have hL_abs := abs_le.mp hLd2
    constructor
    · apply div_le_div_of_nonneg_right _ (pow_nonneg (by linarith) 7)
      have hexp : Real.exp (-7 * C₃' - 2) ≤ Real.exp (7 * Mertens.E₃ ((w - 1 : ℕ) : ℝ) + Ldiff w) :=
        Real.exp_le_exp.mpr (by linarith)
      have hrat : (1 : ℝ) ≤ (Real.log (w : ℝ) / Real.log ((w - 1 : ℕ) : ℝ)) ^ 7 :=
        one_le_pow₀ hlog_ratio_lb
      have hdiv2 : K * Real.exp (-7 * C₃' - 2) / 2 ^ 7 ≤ K * Real.exp (-7 * C₃' - 2) := by
        apply div_le_self (by positivity); norm_num
      calc K * Real.exp (-7 * C₃' - 2) / 2 ^ 7
          ≤ K * Real.exp (-7 * C₃' - 2) := hdiv2
        _ ≤ K * Real.exp (7 * Mertens.E₃ ((w - 1 : ℕ) : ℝ) + Ldiff w) :=
            mul_le_mul_of_nonneg_left hexp hKpos.le
        _ ≤ K * Real.exp (7 * Mertens.E₃ ((w - 1 : ℕ) : ℝ) + Ldiff w) *
              (Real.log (w : ℝ) / Real.log ((w - 1 : ℕ) : ℝ)) ^ 7 :=
            le_mul_of_one_le_right (by positivity) hrat
    · apply div_le_div_of_nonneg_right _ (pow_nonneg (by linarith) 7)
      have hexp : Real.exp (7 * Mertens.E₃ ((w - 1 : ℕ) : ℝ) + Ldiff w) ≤ Real.exp (7 * C₃' + 2) :=
        Real.exp_le_exp.mpr (by linarith)
      have hrat : (Real.log (w : ℝ) / Real.log ((w - 1 : ℕ) : ℝ)) ^ 7 ≤ 2 ^ 7 :=
        pow_le_pow_left₀ (by linarith) hlog_ratio_ub 7
      exact mul_le_mul (mul_le_mul_of_nonneg_left hexp hKpos.le) hrat (by positivity) (by positivity)
  · refine ⟨28 * C₃' + 220, by positivity, fun p w hp hpw => ?_⟩
    have hp100 : 100 < p := lt_of_le_of_lt hP₀ hp
    have hw100 : 100 < w := lt_of_lt_of_le hp100 hpw
    have hwP₀ : P₀ < w := lt_of_lt_of_le hp hpw
    rw [hV7_eq p hp, hV7_eq w hwP₀, hQ1_mert (p - 1) (by omega), hQ1_mert (w - 1) (by omega)]
    have hlp_ge : 2 ≤ Real.log ((p - 1 : ℕ) : ℝ) := hlog_ge2 (p - 1) (by omega)
    have hlw_ge : 2 ≤ Real.log ((w - 1 : ℕ) : ℝ) := hlog_ge2 (w - 1) (by omega)
    have hlp0 : 0 < Real.log (p : ℝ) := by linarith [hlog_ge2 p (by omega)]
    have hlw0 : 0 < Real.log (w : ℝ) := by linarith [hlog_ge2 w (by omega)]
    have hsimp :
        ((Real.exp (-Real.eulerMascheroniConstant) * Real.exp (Mertens.E₃ ((p - 1 : ℕ) : ℝ)) /
            Real.log ((p - 1 : ℕ) : ℝ) / Q1 P₀) ^ 7 * Real.exp (Ldiff p)) /
        ((Real.exp (-Real.eulerMascheroniConstant) * Real.exp (Mertens.E₃ ((w - 1 : ℕ) : ℝ)) /
            Real.log ((w - 1 : ℕ) : ℝ) / Q1 P₀) ^ 7 * Real.exp (Ldiff w)) =
        Real.exp (7 * Mertens.E₃ ((p - 1 : ℕ) : ℝ) - 7 * Mertens.E₃ ((w - 1 : ℕ) : ℝ) - (Ldiff w - Ldiff p)) *
          (Real.log ((w - 1 : ℕ) : ℝ) / Real.log ((p - 1 : ℕ) : ℝ)) ^ 7 := by
      have hQ0 := (hQ1_pos P₀).ne'
      have h1 : Real.log ((p - 1 : ℕ) : ℝ) ≠ 0 := by linarith
      have h2 : Real.log ((w - 1 : ℕ) : ℝ) ≠ 0 := by linarith
      have h3 : Real.exp (-Real.eulerMascheroniConstant) ≠ 0 := (Real.exp_pos _).ne'
      have h4 : Real.exp (Mertens.E₃ ((w - 1 : ℕ) : ℝ)) ≠ 0 := (Real.exp_pos _).ne'
      have h5 : Real.exp (Ldiff w) ≠ 0 := (Real.exp_pos _).ne'
      simp only [div_pow, mul_pow, ← Real.exp_nat_mul]
      rw [Real.exp_sub, Real.exp_sub, Real.exp_sub]
      have he1 : ((7 : ℕ) : ℝ) * Mertens.E₃ ((p - 1 : ℕ) : ℝ) = 7 * Mertens.E₃ ((p - 1 : ℕ) : ℝ) := by norm_num
      have he2 : ((7 : ℕ) : ℝ) * Mertens.E₃ ((w - 1 : ℕ) : ℝ) = 7 * Mertens.E₃ ((w - 1 : ℕ) : ℝ) := by norm_num
      rw [he1, he2]
      field_simp
    rw [hsimp]
    have hlogp_pred := hlog_pred p hp100
    have hlogw_pred := hlog_pred w hw100
    have hratio_p : Real.log (p : ℝ) / Real.log ((p - 1 : ℕ) : ℝ) ≤ Real.exp (2 / Real.log (p : ℝ)) := by
      have h1 : Real.log (p : ℝ) / Real.log ((p - 1 : ℕ) : ℝ) ≤ 1 + 2 / ((p : ℝ) * Real.log ((p - 1 : ℕ) : ℝ)) := by
        rw [div_le_iff₀ (by linarith)]
        have hmul : (1 + 2 / ((p : ℝ) * Real.log ((p - 1 : ℕ) : ℝ))) * Real.log ((p - 1 : ℕ) : ℝ) =
            Real.log ((p - 1 : ℕ) : ℝ) + 2 / (p : ℝ) := by
          have : Real.log ((p - 1 : ℕ) : ℝ) ≠ 0 := by linarith
          field_simp
        linarith [hlogp_pred.2]
      have h2 : 2 / ((p : ℝ) * Real.log ((p - 1 : ℕ) : ℝ)) ≤ 2 / Real.log (p : ℝ) := by
        apply div_le_div_of_nonneg_left (by norm_num) hlp0
        have hp_log : Real.log (p : ℝ) ≤ (p : ℝ) := (Real.log_le_sub_one_of_pos (by exact_mod_cast (by omega : 0 < p))).trans (by linarith)
        nlinarith [hlp_ge]
      calc Real.log (p : ℝ) / Real.log ((p - 1 : ℕ) : ℝ)
          ≤ 1 + 2 / ((p : ℝ) * Real.log ((p - 1 : ℕ) : ℝ)) := h1
        _ ≤ 1 + 2 / Real.log (p : ℝ) := by linarith
        _ ≤ Real.exp (2 / Real.log (p : ℝ)) := by linarith [Real.add_one_le_exp (2 / Real.log (p : ℝ))]
    have hpow_ratio : (Real.log ((w - 1 : ℕ) : ℝ) / Real.log ((p - 1 : ℕ) : ℝ)) ^ 7 ≤
        Real.exp (14 / Real.log (p : ℝ)) * (Real.log (w : ℝ) / Real.log (p : ℝ)) ^ 7 := by
      have h1 : Real.log ((w - 1 : ℕ) : ℝ) / Real.log ((p - 1 : ℕ) : ℝ) ≤
          Real.exp (2 / Real.log (p : ℝ)) * (Real.log (w : ℝ) / Real.log (p : ℝ)) := by
        calc Real.log ((w - 1 : ℕ) : ℝ) / Real.log ((p - 1 : ℕ) : ℝ)
            ≤ Real.log (w : ℝ) / Real.log ((p - 1 : ℕ) : ℝ) :=
              div_le_div_of_nonneg_right hlogw_pred.1 (by linarith)
          _ = (Real.log (p : ℝ) / Real.log ((p - 1 : ℕ) : ℝ)) * (Real.log (w : ℝ) / Real.log (p : ℝ)) := by
              have : Real.log (p : ℝ) ≠ 0 := hlp0.ne'
              field_simp
          _ ≤ Real.exp (2 / Real.log (p : ℝ)) * (Real.log (w : ℝ) / Real.log (p : ℝ)) :=
              mul_le_mul_of_nonneg_right hratio_p (by positivity)
      calc (Real.log ((w - 1 : ℕ) : ℝ) / Real.log ((p - 1 : ℕ) : ℝ)) ^ 7
          ≤ (Real.exp (2 / Real.log (p : ℝ)) * (Real.log (w : ℝ) / Real.log (p : ℝ))) ^ 7 :=
            pow_le_pow_left₀ (by positivity) h1 7
        _ = Real.exp (14 / Real.log (p : ℝ)) * (Real.log (w : ℝ) / Real.log (p : ℝ)) ^ 7 := by
            rw [mul_pow, ← Real.exp_nat_mul]
            congr 2; norm_num; ring
    have hlp_half : Real.log (p : ℝ) / 2 ≤ Real.log ((p - 1 : ℕ) : ℝ) := by
      have : 2 / (p : ℝ) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast (by omega : 0 < p))]; exact_mod_cast (by omega : 2 ≤ p)
      linarith [hlogp_pred.2, hlp_ge]
    have hE3p : |Mertens.E₃ ((p - 1 : ℕ) : ℝ)| ≤ 2 * C₃' / Real.log (p : ℝ) := by
      have h1 := hC₃ ((p - 1 : ℕ) : ℝ) (by exact_mod_cast (by omega : 2 ≤ p - 1))
      calc |Mertens.E₃ ((p - 1 : ℕ) : ℝ)|
          ≤ C₃ / Real.log ((p - 1 : ℕ) : ℝ) := h1
        _ ≤ C₃' / Real.log ((p - 1 : ℕ) : ℝ) := div_le_div_of_nonneg_right (le_max_left _ _) (by linarith)
        _ ≤ C₃' / (Real.log (p : ℝ) / 2) := div_le_div_of_nonneg_left hC₃'p.le (by positivity) hlp_half
        _ = 2 * C₃' / Real.log (p : ℝ) := by ring
    have hE3w : |Mertens.E₃ ((w - 1 : ℕ) : ℝ)| ≤ 2 * C₃' / Real.log (p : ℝ) := by
      have h1 := hC₃ ((w - 1 : ℕ) : ℝ) (by exact_mod_cast (by omega : 2 ≤ w - 1))
      have hpw_log : Real.log ((p - 1 : ℕ) : ℝ) ≤ Real.log ((w - 1 : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < p - 1)) (by exact_mod_cast (by omega : p - 1 ≤ w - 1))
      calc |Mertens.E₃ ((w - 1 : ℕ) : ℝ)|
          ≤ C₃ / Real.log ((w - 1 : ℕ) : ℝ) := h1
        _ ≤ C₃' / Real.log ((w - 1 : ℕ) : ℝ) := div_le_div_of_nonneg_right (le_max_left _ _) (by linarith)
        _ ≤ C₃' / (Real.log (p : ℝ) / 2) := div_le_div_of_nonneg_left hC₃'p.le (by positivity) (hlp_half.trans hpw_log)
        _ = 2 * C₃' / Real.log (p : ℝ) := by ring
    have hLdpw : |Ldiff w - Ldiff p| ≤ 200 / Real.log (p : ℝ) := by
      have h1 := hLdiff_bound p w hp.le hpw
      have hp_log : Real.log (p : ℝ) ≤ (p : ℝ) :=
        (Real.log_le_sub_one_of_pos (by exact_mod_cast (by omega : 0 < p))).trans (by linarith)
      exact h1.trans (div_le_div_of_nonneg_left (by norm_num) hlp0 hp_log)
    have hexp_bound :
        7 * Mertens.E₃ ((p - 1 : ℕ) : ℝ) - 7 * Mertens.E₃ ((w - 1 : ℕ) : ℝ) - (Ldiff w - Ldiff p) +
          14 / Real.log (p : ℝ) ≤ (28 * C₃' + 220) / Real.log (p : ℝ) := by
      have h1 := (abs_le.mp hE3p).2
      have h2 := (abs_le.mp hE3w).1
      have h3 := (abs_le.mp hLdpw).1
      have hpos : (0 : ℝ) < 6 / Real.log (p : ℝ) := by positivity
      linarith [show (28 * C₃' + 220) / Real.log (p : ℝ) =
        7 * (2 * C₃' / Real.log (p : ℝ)) + 7 * (2 * C₃' / Real.log (p : ℝ)) +
        200 / Real.log (p : ℝ) + 14 / Real.log (p : ℝ) + 6 / Real.log (p : ℝ) by ring]
    calc Real.exp (7 * Mertens.E₃ ((p - 1 : ℕ) : ℝ) - 7 * Mertens.E₃ ((w - 1 : ℕ) : ℝ) - (Ldiff w - Ldiff p)) *
            (Real.log ((w - 1 : ℕ) : ℝ) / Real.log ((p - 1 : ℕ) : ℝ)) ^ 7
        ≤ Real.exp (7 * Mertens.E₃ ((p - 1 : ℕ) : ℝ) - 7 * Mertens.E₃ ((w - 1 : ℕ) : ℝ) - (Ldiff w - Ldiff p)) *
            (Real.exp (14 / Real.log (p : ℝ)) * (Real.log (w : ℝ) / Real.log (p : ℝ)) ^ 7) :=
          mul_le_mul_of_nonneg_left hpow_ratio (Real.exp_pos _).le
      _ = Real.exp (7 * Mertens.E₃ ((p - 1 : ℕ) : ℝ) - 7 * Mertens.E₃ ((w - 1 : ℕ) : ℝ) - (Ldiff w - Ldiff p) +
            14 / Real.log (p : ℝ)) * (Real.log (w : ℝ) / Real.log (p : ℝ)) ^ 7 := by
          rw [Real.exp_add, mul_assoc]
      _ ≤ Real.exp ((28 * C₃' + 220) / Real.log (p : ℝ)) * (Real.log (w : ℝ) / Real.log (p : ℝ)) ^ 7 :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp_bound) (by positivity)

/-- Upper bound for `∏_{P₀ < p <= R} (1 + 7/p) <= C * (log R)^7`. -/
lemma prod_one_add_seven_div_p_le (P₀ : ℕ) (hP₀ : 100 ≤ P₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 2 ≤ R →
      ∏ p ∈ (Ioc P₀ R).filter Nat.Prime, (1 + 7 / (p : ℝ)) ≤ C * (Real.log R) ^ 7 := by
  obtain ⟨c₁, _, hc₁p, _, hV⟩ := (V7_asymptotics P₀ hP₀).1
  refine ⟨max (1 / c₁) 1 * Real.exp 10, by positivity, fun R hR => ?_⟩
  by_cases hRP : R ≤ P₀
  · have hempty : (Ioc P₀ R).filter Nat.Prime = ∅ := by ext x; simp; omega
    rw [hempty, Finset.prod_empty]
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log (R : ℝ) := by
      have := Real.log_two_gt_d9
      have hle : Real.log 2 ≤ Real.log (R : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hR)
      linarith
    have hpow : (1 / 128 : ℝ) ≤ (Real.log (R : ℝ)) ^ 7 := by
      calc (1 / 128 : ℝ) = (1 / 2 : ℝ) ^ 7 := by norm_num
        _ ≤ (Real.log (R : ℝ)) ^ 7 := pow_le_pow_left₀ (by norm_num) hlog2 7
    have hexp10 : (128 : ℝ) ≤ Real.exp 10 := by
      have h1 : (2 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) (Real.add_one_le_exp 1)
      have h10 : (2 : ℝ) ^ 10 ≤ Real.exp 10 := by
        rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
        exact pow_le_pow_left₀ (by norm_num) h1 10
      linarith [show (2 : ℝ) ^ 10 = 1024 by norm_num]
    have hm1 : (1 : ℝ) ≤ max (1 / c₁) 1 := le_max_right _ _
    have h12 : (128 : ℝ) ≤ max (1 / c₁) 1 * Real.exp 10 := by
      calc (128 : ℝ) = 1 * 128 := by norm_num
        _ ≤ max (1 / c₁) 1 * Real.exp 10 := mul_le_mul hm1 hexp10 (by norm_num) (by positivity)
    calc (1 : ℝ) = 128 * (1 / 128) := by norm_num
      _ ≤ (max (1 / c₁) 1 * Real.exp 10) * (Real.log (R : ℝ)) ^ 7 :=
          mul_le_mul h12 hpow (by norm_num) (by positivity)
  · push Not at hRP
    have hprod_le : ∏ p ∈ (Ioc P₀ R).filter Nat.Prime, (1 + 7 / (p : ℝ)) ≤ (V7 P₀ (R + 1))⁻¹ := by
      unfold V7
      have hset : (Ioc P₀ R).filter Nat.Prime = (Ioo P₀ (R + 1)).filter Nat.Prime := by
        ext p; simp only [mem_filter, mem_Ioc, mem_Ioo]
        constructor <;> rintro ⟨⟨_, _⟩, hp⟩ <;> exact ⟨⟨by omega, by omega⟩, hp⟩
      rw [hset, ← Finset.prod_inv_distrib]
      refine Finset.prod_le_prod (fun _ _ => by positivity) fun p hp => ?_
      have hp100 : (100 : ℝ) < p := by exact_mod_cast lt_of_le_of_lt hP₀ (mem_Ioo.mp (mem_filter.mp hp).1).1
      have hpos : 0 < 1 - 7 / (p : ℝ) := by
        have : 7 / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
        linarith
      rw [inv_eq_one_div, le_div_iff₀ hpos]
      have : (1 + 7 / (p : ℝ)) * (1 - 7 / (p : ℝ)) = 1 - 49 / (p : ℝ) ^ 2 := by ring
      rw [this]
      linarith [show (0 : ℝ) ≤ 49 / (p : ℝ) ^ 2 by positivity]
    have hVR := (hV (R + 1) (by omega)).1
    have hVpos := V7_pos (w := R + 1) hP₀
    have hlogR1_pos : 0 < Real.log ((R + 1 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < R + 1))
    have hinv_le : (V7 P₀ (R + 1))⁻¹ ≤ (1 / c₁) * (Real.log ((R + 1 : ℕ) : ℝ)) ^ 7 := by
      rw [inv_le_comm₀ hVpos (by positivity)]
      have : ((1 / c₁) * (Real.log ((R + 1 : ℕ) : ℝ)) ^ 7)⁻¹ = c₁ / (Real.log ((R + 1 : ℕ) : ℝ)) ^ 7 := by
        field_simp
      rw [this]; exact hVR
    have hlog_R1 : Real.log ((R + 1 : ℕ) : ℝ) ≤ 2 * Real.log (R : ℝ) := by
      have hR2 : (2 : ℝ) ≤ R := by exact_mod_cast hR
      have hsq : ((R + 1 : ℕ) : ℝ) ≤ (R : ℝ) ^ 2 := by push_cast; nlinarith
      calc Real.log ((R + 1 : ℕ) : ℝ)
          ≤ Real.log ((R : ℝ) ^ 2) := Real.log_le_log (by positivity) hsq
        _ = 2 * Real.log (R : ℝ) := by rw [Real.log_pow]; norm_num
    have hexp10 : (2 : ℝ) ^ 7 ≤ Real.exp 10 := by
      have h1 : (2 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) (Real.add_one_le_exp 1)
      have h10 : (2 : ℝ) ^ 10 ≤ Real.exp 10 := by
        rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
        exact pow_le_pow_left₀ (by norm_num) h1 10
      linarith [show (2 : ℝ) ^ 10 = 1024 by norm_num, show (2 : ℝ) ^ 7 = 128 by norm_num]
    calc ∏ p ∈ (Ioc P₀ R).filter Nat.Prime, (1 + 7 / (p : ℝ))
        ≤ (1 / c₁) * (Real.log ((R + 1 : ℕ) : ℝ)) ^ 7 := hprod_le.trans hinv_le
      _ ≤ (1 / c₁) * (2 * Real.log (R : ℝ)) ^ 7 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogR1_pos.le hlog_R1 7) (by positivity)
      _ = (1 / c₁) * (2 : ℝ) ^ 7 * (Real.log (R : ℝ)) ^ 7 := by ring
      _ ≤ max (1 / c₁) 1 * Real.exp 10 * (Real.log (R : ℝ)) ^ 7 := by
          have h1 : 1 / c₁ ≤ max (1 / c₁) 1 := le_max_left _ _
          have h2 : (1 / c₁) * (2 : ℝ) ^ 7 ≤ max (1 / c₁) 1 * Real.exp 10 :=
            mul_le_mul h1 hexp10 (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right h2 (pow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ R))) 7)

/-- Richert bin sum bound from Mertens 1st and 2nd theorems! -/
lemma sum_richert_bin_le {t₀ t₁ u : ℝ} (ht₀ : 0 < t₀) (ht01 : t₀ < t₁) (ht₁ : t₁ < 1) (hu : 0 < u) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∑ p ∈ (Ico ⌈(X : ℝ) ^ t₀⌉₊ ⌈(X : ℝ) ^ t₁⌉₊).filter Nat.Prime,
        (1 - u * Real.log p / Real.log X) * (7 / (p : ℝ)) ≤
          7 * (Real.log (t₁ / t₀) - u * (t₁ - t₀)) + C / Real.log X := by
  obtain ⟨C₁, hC₁p, hE₁⟩ := Mertens.E₁p.bounded
  set C₂ := Real.log 4 + 6 + Mertens.E₁
  have hC₂p : 0 < C₂ := by
    have hE1nn : 0 ≤ Mertens.E₁ := tsum_nonneg fun p => Mertens.E₁.summand_nonneg p
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    dsimp [C₂]; linarith
  refine ⟨7 * (4 * C₂ / t₀ + 2 * u * C₁ + 2 / t₀ + 2 * u + 10), by positivity, ?_⟩
  have hev0 : ∀ᶠ X : ℕ in atTop, (4 : ℝ) ≤ (X : ℝ) ^ t₀ :=
    (tendsto_rpow_atTop ht₀).comp tendsto_natCast_atTop_atTop |>.eventually_ge_atTop 4
  have hev_log : ∀ᶠ X : ℕ in atTop, (2 / t₀ : ℝ) ≤ Real.log (X : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (2 / t₀)
  filter_upwards [hev0, hev_log, eventually_ge_atTop 100] with X hX0 hXlog hX100
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) < X := by exact_mod_cast (by omega : 1 < X)
  have hlX : 0 < Real.log (X : ℝ) := Real.log_pos hX1
  set a := ⌈(X : ℝ) ^ t₀⌉₊ - 1
  set b := ⌈(X : ℝ) ^ t₁⌉₊ - 1
  have hXt0_le_Xt1 : (X : ℝ) ^ t₀ ≤ (X : ℝ) ^ t₁ :=
    Real.rpow_le_rpow_of_exponent_le hX1.le ht01.le
  have hceil0_ge : 4 ≤ ⌈(X : ℝ) ^ t₀⌉₊ := by
    have : (4 : ℝ) ≤ (⌈(X : ℝ) ^ t₀⌉₊ : ℝ) := hX0.trans (Nat.le_ceil _)
    exact_mod_cast this
  have ha_ge : 3 ≤ a := by dsimp [a]; omega
  have hab : a ≤ b := by
    dsimp [a, b]
    have : ⌈(X : ℝ) ^ t₀⌉₊ ≤ ⌈(X : ℝ) ^ t₁⌉₊ := Nat.ceil_mono hXt0_le_Xt1
    omega
  have hset : (Ico ⌈(X : ℝ) ^ t₀⌉₊ ⌈(X : ℝ) ^ t₁⌉₊).filter Nat.Prime =
      (Ioc 0 b).filter Nat.Prime \ (Ioc 0 a).filter Nat.Prime := by
    ext p; simp only [mem_filter, mem_Ico, Finset.mem_sdiff, mem_Ioc]
    dsimp [a, b]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨⟨⟨hp.pos, by omega⟩, hp⟩, fun h => by omega⟩
    · rintro ⟨⟨⟨_, h2⟩, hp⟩, hnot⟩
      refine ⟨⟨?_, by omega⟩, hp⟩
      by_contra hlt; push Not at hlt
      exact hnot ⟨⟨hp.pos, by omega⟩, hp⟩
  have hsub : (Ioc 0 a).filter Nat.Prime ⊆ (Ioc 0 b).filter Nat.Prime := by
    intro p hp; simp only [mem_filter, mem_Ioc] at hp ⊢; exact ⟨⟨hp.1.1, hp.1.2.trans hab⟩, hp.2⟩
  have hrew :
      ∑ p ∈ (Ico ⌈(X : ℝ) ^ t₀⌉₊ ⌈(X : ℝ) ^ t₁⌉₊).filter Nat.Prime,
        (1 - u * Real.log p / Real.log X) * (7 / (p : ℝ)) =
      7 * ((∑ p ∈ (Ioc 0 b).filter Nat.Prime, (1 : ℝ) / p) -
           (∑ p ∈ (Ioc 0 a).filter Nat.Prime, (1 : ℝ) / p)) -
      (7 * u / Real.log X) * ((∑ p ∈ (Ioc 0 b).filter Nat.Prime, Real.log p / p) -
           (∑ p ∈ (Ioc 0 a).filter Nat.Prime, Real.log p / p)) := by
    rw [hset]
    have hsplit : ∀ f : ℕ → ℝ,
        ∑ p ∈ (Ioc 0 b).filter Nat.Prime \ (Ioc 0 a).filter Nat.Prime, f p =
          (∑ p ∈ (Ioc 0 b).filter Nat.Prime, f p) - (∑ p ∈ (Ioc 0 a).filter Nat.Prime, f p) := by
      intro f
      have := Finset.sum_sdiff hsub (f := f)
      linarith
    calc ∑ p ∈ (Ioc 0 b).filter Nat.Prime \ (Ioc 0 a).filter Nat.Prime,
            (1 - u * Real.log p / Real.log X) * (7 / (p : ℝ))
        = ∑ p ∈ (Ioc 0 b).filter Nat.Prime \ (Ioc 0 a).filter Nat.Prime,
            (7 * ((1 : ℝ) / p) - (7 * u / Real.log X) * (Real.log p / p)) := by
          refine Finset.sum_congr rfl fun p _ => by ring
      _ = 7 * (∑ p ∈ (Ioc 0 b).filter Nat.Prime \ (Ioc 0 a).filter Nat.Prime, (1 : ℝ) / p) -
          (7 * u / Real.log X) * (∑ p ∈ (Ioc 0 b).filter Nat.Prime \ (Ioc 0 a).filter Nat.Prime, Real.log p / p) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = _ := by rw [hsplit, hsplit]
  rw [hrew]
  have ha_bounds : (X : ℝ) ^ t₀ - 1 ≤ (a : ℝ) ∧ (a : ℝ) ≤ (X : ℝ) ^ t₀ := by
    dsimp [a]
    have h1 : 1 ≤ ⌈(X : ℝ) ^ t₀⌉₊ := by omega
    rw [Nat.cast_sub h1, Nat.cast_one]
    constructor
    · linarith [Nat.le_ceil ((X : ℝ) ^ t₀)]
    · linarith [Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (X : ℝ) ^ t₀ by positivity)]
  have hb_bounds : (X : ℝ) ^ t₁ - 1 ≤ (b : ℝ) ∧ (b : ℝ) ≤ (X : ℝ) ^ t₁ := by
    dsimp [b]
    have h1 : 1 ≤ ⌈(X : ℝ) ^ t₁⌉₊ := by
      have : ⌈(X : ℝ) ^ t₀⌉₊ ≤ ⌈(X : ℝ) ^ t₁⌉₊ := Nat.ceil_mono hXt0_le_Xt1
      omega
    rw [Nat.cast_sub h1, Nat.cast_one]
    constructor
    · linarith [Nat.le_ceil ((X : ℝ) ^ t₁)]
    · linarith [Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (X : ℝ) ^ t₁ by positivity)]
  have hloga_ub : Real.log (a : ℝ) ≤ t₀ * Real.log (X : ℝ) := by
    calc Real.log (a : ℝ) ≤ Real.log ((X : ℝ) ^ t₀) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < a)) ha_bounds.2
      _ = t₀ * Real.log (X : ℝ) := by rw [Real.log_rpow hXp]
  have hloga_lb : t₀ * Real.log (X : ℝ) - 1 ≤ Real.log (a : ℝ) := by
    have hhalf : (X : ℝ) ^ t₀ / 2 ≤ (a : ℝ) := by linarith [ha_bounds.1, hX0]
    have h1 : Real.log ((X : ℝ) ^ t₀ / 2) ≤ Real.log (a : ℝ) :=
      Real.log_le_log (by positivity) hhalf
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hXp] at h1
    have hlog2 : Real.log 2 ≤ 1 := by
      exact (Real.log_le_iff_le_exp (by norm_num)).mpr (le_trans (by norm_num) (Real.add_one_le_exp 1))
    linarith
  have hlogb_ub : Real.log (b : ℝ) ≤ t₁ * Real.log (X : ℝ) := by
    calc Real.log (b : ℝ) ≤ Real.log ((X : ℝ) ^ t₁) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < b)) hb_bounds.2
      _ = t₁ * Real.log (X : ℝ) := by rw [Real.log_rpow hXp]
  have hlogb_lb : t₁ * Real.log (X : ℝ) - 1 ≤ Real.log (b : ℝ) := by
    have hhalf : (X : ℝ) ^ t₁ / 2 ≤ (b : ℝ) := by linarith [hb_bounds.1, hX0, hXt0_le_Xt1]
    have h1 : Real.log ((X : ℝ) ^ t₁ / 2) ≤ Real.log (b : ℝ) :=
      Real.log_le_log (by positivity) hhalf
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hXp] at h1
    have hlog2 : Real.log 2 ≤ 1 := by
      exact (Real.log_le_iff_le_exp (by norm_num)).mpr (le_trans (by norm_num) (Real.add_one_le_exp 1))
    linarith
  have hloga_ge_half : t₀ * Real.log (X : ℝ) / 2 ≤ Real.log (a : ℝ) := by
    have : 2 ≤ t₀ * Real.log (X : ℝ) := by
      have := mul_le_mul_of_nonneg_left hXlog ht₀.le
      rwa [mul_div_cancel₀ _ ht₀.ne'] at this
    linarith
  have hloga_pos : 0 < Real.log (a : ℝ) := by linarith [mul_pos ht₀ hlX]
  have hlogb_ge_half : t₀ * Real.log (X : ℝ) / 2 ≤ Real.log (b : ℝ) :=
    hloga_ge_half.trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < a)) (by exact_mod_cast hab))
  have hE2a := abs_le.mp (Mertens.E₂p.abs_le (x := (a : ℝ)) (by exact_mod_cast (by omega : 2 ≤ a)))
  have hE2b := abs_le.mp (Mertens.E₂p.abs_le (x := (b : ℝ)) (by exact_mod_cast (by omega : 2 ≤ b)))
  have hS2_diff :
      (∑ p ∈ (Ioc 0 b).filter Nat.Prime, (1 : ℝ) / p) -
      (∑ p ∈ (Ioc 0 a).filter Nat.Prime, (1 : ℝ) / p) ≤
        Real.log (t₁ / t₀) + (4 * C₂ / t₀ + 2 / t₀) / Real.log (X : ℝ) := by
    have ha_eq : Mertens.E₂p (a : ℝ) = (∑ p ∈ (Ioc 0 a).filter Nat.Prime, (1 : ℝ) / p) - Real.log (Real.log (a : ℝ)) - Mertens.M := by
      simp [Mertens.E₂p, Nat.floor_natCast]
    have hb_eq : Mertens.E₂p (b : ℝ) = (∑ p ∈ (Ioc 0 b).filter Nat.Prime, (1 : ℝ) / p) - Real.log (Real.log (b : ℝ)) - Mertens.M := by
      simp [Mertens.E₂p, Nat.floor_natCast]
    have hloglog : Real.log (Real.log (b : ℝ)) - Real.log (Real.log (a : ℝ)) ≤
        Real.log (t₁ / t₀) + (2 / t₀) / Real.log (X : ℝ) := by
      have h1 : Real.log (Real.log (b : ℝ)) ≤ Real.log (t₁ * Real.log (X : ℝ)) :=
        Real.log_le_log (by linarith) hlogb_ub
      have h2 : Real.log (t₀ * Real.log (X : ℝ)) - Real.log (Real.log (a : ℝ)) ≤ (2 / t₀) / Real.log (X : ℝ) := by
        rw [← Real.log_div (by positivity) hloga_pos.ne']
        calc Real.log (t₀ * Real.log (X : ℝ) / Real.log (a : ℝ))
            ≤ t₀ * Real.log (X : ℝ) / Real.log (a : ℝ) - 1 := Real.log_le_sub_one_of_pos (by positivity)
          _ = (t₀ * Real.log (X : ℝ) - Real.log (a : ℝ)) / Real.log (a : ℝ) := by field_simp
          _ ≤ 1 / (t₀ * Real.log (X : ℝ) / 2) :=
              div_le_div₀ zero_le_one (by linarith) (by positivity) hloga_ge_half
          _ = (2 / t₀) / Real.log (X : ℝ) := by field_simp
      have h3 : Real.log (t₁ * Real.log (X : ℝ)) - Real.log (t₀ * Real.log (X : ℝ)) = Real.log (t₁ / t₀) := by
        have ht1p : 0 < t₁ := ht₀.trans ht01
        rw [← Real.log_div (mul_pos ht1p hlX).ne' (mul_pos ht₀ hlX).ne']
        congr 1; field_simp
      linarith
    have hCa : C₂ / Real.log (a : ℝ) ≤ (2 * C₂ / t₀) / Real.log (X : ℝ) := by
      calc C₂ / Real.log (a : ℝ)
          ≤ C₂ / (t₀ * Real.log (X : ℝ) / 2) := div_le_div_of_nonneg_left hC₂p.le (by positivity) hloga_ge_half
        _ = (2 * C₂ / t₀) / Real.log (X : ℝ) := by field_simp
    have hCb : C₂ / Real.log (b : ℝ) ≤ (2 * C₂ / t₀) / Real.log (X : ℝ) := by
      calc C₂ / Real.log (b : ℝ)
          ≤ C₂ / (t₀ * Real.log (X : ℝ) / 2) := div_le_div_of_nonneg_left hC₂p.le (by positivity) hlogb_ge_half
        _ = (2 * C₂ / t₀) / Real.log (X : ℝ) := by field_simp
    have hsum_eq : (4 * C₂ / t₀ + 2 / t₀) / Real.log (X : ℝ) =
        (2 * C₂ / t₀) / Real.log (X : ℝ) + (2 * C₂ / t₀) / Real.log (X : ℝ) + (2 / t₀) / Real.log (X : ℝ) := by ring
    linarith [hE2a.1, hE2b.2, ha_eq, hb_eq, hloglog, hCa, hCb, hsum_eq]
  have hE1a := abs_le.mp (hE₁ (a : ℝ) (by exact_mod_cast (by omega : 1 ≤ a)))
  have hE1b := abs_le.mp (hE₁ (b : ℝ) (by exact_mod_cast (by omega : 1 ≤ b)))
  have hS1_diff :
      (t₁ - t₀) * Real.log (X : ℝ) - (2 * C₁ + 1) ≤
      (∑ p ∈ (Ioc 0 b).filter Nat.Prime, Real.log p / p) -
      (∑ p ∈ (Ioc 0 a).filter Nat.Prime, Real.log p / p) := by
    have ha_eq : Mertens.E₁p (a : ℝ) = (∑ p ∈ (Ioc 0 a).filter Nat.Prime, Real.log p / p) - Real.log (a : ℝ) := by
      simp [Mertens.E₁p, Nat.floor_natCast]
    have hb_eq : Mertens.E₁p (b : ℝ) = (∑ p ∈ (Ioc 0 b).filter Nat.Prime, Real.log p / p) - Real.log (b : ℝ) := by
      simp [Mertens.E₁p, Nat.floor_natCast]
    linarith [hE1a.2, hE1b.1, ha_eq, hb_eq, hloga_ub, hlogb_lb]
  have hpart2 :
      (7 * u / Real.log X) * ((t₁ - t₀) * Real.log (X : ℝ) - (2 * C₁ + 1)) ≤
      (7 * u / Real.log X) * ((∑ p ∈ (Ioc 0 b).filter Nat.Prime, Real.log p / p) -
        (∑ p ∈ (Ioc 0 a).filter Nat.Prime, Real.log p / p)) :=
    mul_le_mul_of_nonneg_left hS1_diff (by positivity)
  have hpart2_simp :
      (7 * u / Real.log X) * ((t₁ - t₀) * Real.log (X : ℝ) - (2 * C₁ + 1)) =
      7 * u * (t₁ - t₀) - (7 * u * (2 * C₁ + 1)) / Real.log X := by
    have hlX0 := hlX.ne'
    field_simp
  have hfinal_err :
      7 * ((4 * C₂ / t₀ + 2 / t₀) / Real.log (X : ℝ)) + (7 * u * (2 * C₁ + 1)) / Real.log (X : ℝ) ≤
      7 * (4 * C₂ / t₀ + 2 * u * C₁ + 2 / t₀ + 2 * u + 10) / Real.log (X : ℝ) := by
    have hpos : (0 : ℝ) < (7 * u + 70) / Real.log (X : ℝ) := by positivity
    linarith [show 7 * (4 * C₂ / t₀ + 2 * u * C₁ + 2 / t₀ + 2 * u + 10) / Real.log (X : ℝ) =
      7 * ((4 * C₂ / t₀ + 2 / t₀) / Real.log (X : ℝ)) + (7 * u * (2 * C₁ + 1)) / Real.log (X : ℝ) +
      (7 * u + 70) / Real.log (X : ℝ) by ring]
  linarith [hS2_diff, hpart2, hpart2_simp, hfinal_err]

end Erdos946MertensAux
end

section
open Finset Filter Real
open scoped BigOperators Classical

namespace Erdos946Selberg

private lemma coprime_of_squarefree_mul {a b : ℕ} (h : Squarefree (a * b)) : a.Coprime b := by
  refine Nat.coprime_of_dvd fun p hp ha hb => ?_
  exact (Nat.squarefree_iff_prime_squarefree.mp h p hp) (mul_dvd_mul ha hb)

private lemma primeFactors_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, p).primeFactors = S := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert p T hpT ih =>
    have hpp : p.Prime := hS p (mem_insert_self p T)
    have hT : ∀ q ∈ T, q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
    have hTpos : 0 < ∏ q ∈ T, q := Finset.prod_pos fun q hq => (hT q hq).pos
    rw [Finset.prod_insert hpT, Nat.primeFactors_mul hpp.ne_zero hTpos.ne', hpp.primeFactors, ih hT]
    ext q; simp

/-- Multiplicative root-count function: `ρ(p) = 7` for primes `p > P₀`, `0` for `p <= P₀`. -/
noncomputable def rho (P₀ d : ℕ) : ℝ :=
  if Squarefree d ∧ ∀ p ∈ d.primeFactors, P₀ < p then (7 : ℝ) ^ d.primeFactors.card else 0

/-- `g(d) = ρ(d) / d`. -/
noncomputable def gFunc (P₀ d : ℕ) : ℝ := rho P₀ d / (d : ℝ)

/-- `h(d) = ∏_{p | d} (7 / (p - 7))` for squarefree `d` with all prime factors `> P₀`. -/
noncomputable def hFunc (P₀ d : ℕ) : ℝ :=
  if Squarefree d ∧ ∀ p ∈ d.primeFactors, P₀ < p then
    ∏ p ∈ d.primeFactors, (7 / ((p : ℝ) - 7))
  else 0

/-- Support predicate: squarefree `d` with all prime factors in `(P₀, w)`. -/
def ValidDiv (P₀ w d : ℕ) : Prop :=
  0 < d ∧ Squarefree d ∧ ∀ p ∈ d.primeFactors, P₀ < p ∧ p < w

lemma validDiv_one (P₀ w : ℕ) : ValidDiv P₀ w 1 := by
  refine ⟨by norm_num, squarefree_one, ?_⟩
  simp

lemma validDiv_of_dvd {P₀ w d e : ℕ} (hd : ValidDiv P₀ w d) (hed : e ∣ d) : ValidDiv P₀ w e := by
  have he0 : 0 < e := Nat.pos_of_dvd_of_pos hed hd.1
  refine ⟨he0, hd.2.1.squarefree_of_dvd hed, fun p hp => hd.2.2 p ?_⟩
  exact Nat.mem_primeFactors.mpr
    ⟨Nat.prime_of_mem_primeFactors hp, (Nat.dvd_of_mem_primeFactors hp).trans hed, hd.1.ne'⟩

lemma validDiv_mul_of_coprime {P₀ w a b : ℕ} (ha : ValidDiv P₀ w a) (hb : ValidDiv P₀ w b)
    (hcop : a.Coprime b) : ValidDiv P₀ w (a * b) := by
  refine ⟨Nat.mul_pos ha.1 hb.1, (Nat.squarefree_mul hcop).mpr ⟨ha.2.1, hb.2.1⟩, fun p hp => ?_⟩
  rw [Nat.primeFactors_mul ha.1.ne' hb.1.ne', mem_union] at hp
  rcases hp with h | h
  · exact ha.2.2 p h
  · exact hb.2.2 p h

lemma validDiv_lcm {P₀ w a b : ℕ} (ha : ValidDiv P₀ w a) (hb : ValidDiv P₀ w b) :
    ValidDiv P₀ w (Nat.lcm a b) := by
  have hpos : 0 < Nat.lcm a b := Nat.lcm_pos ha.1 hb.1
  have hsf : Squarefree (Nat.lcm a b) := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hpp
    -- p^2 | lcm a b -> p^2 | a or p^2 | b (by prime power factorization)
    have hdvd : p ^ 2 ∣ Nat.lcm a b := by simpa [pow_two] using hpp
    have hfac := Nat.factorization_lcm ha.1.ne' hb.1.ne'
    have hle := (hp.pow_dvd_iff_le_factorization hpos.ne').mp hdvd
    rw [hfac, Finsupp.sup_apply] at hle
    rcases le_sup_iff.mp hle with h | h
    · have := (hp.pow_dvd_iff_le_factorization ha.1.ne').mpr h
      exact (Nat.squarefree_iff_prime_squarefree.mp ha.2.1 p hp) (by simpa [pow_two] using this)
    · have := (hp.pow_dvd_iff_le_factorization hb.1.ne').mpr h
      exact (Nat.squarefree_iff_prime_squarefree.mp hb.2.1 p hp) (by simpa [pow_two] using this)
  refine ⟨hpos, hsf, fun p hp => ?_⟩
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hdvd := Nat.dvd_of_mem_primeFactors hp
  have hdivmul : p ∣ a * b := hdvd.trans (Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a))
  rcases hpr.dvd_mul.mp hdivmul with h | h
  · exact ha.2.2 p (Nat.mem_primeFactors.mpr ⟨hpr, h, ha.1.ne'⟩)
  · exact hb.2.2 p (Nat.mem_primeFactors.mpr ⟨hpr, h, hb.1.ne'⟩)

lemma gFunc_pos {P₀ w d : ℕ} (hd : ValidDiv P₀ w d) : 0 < gFunc P₀ d := by
  unfold gFunc rho
  rw [if_pos ⟨hd.2.1, fun p hp => (hd.2.2 p hp).1⟩]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
  positivity

lemma hFunc_pos {P₀ w d : ℕ} (hP₀ : 100 ≤ P₀) (hd : ValidDiv P₀ w d) : 0 < hFunc P₀ d := by
  unfold hFunc
  rw [if_pos ⟨hd.2.1, fun p hp => (hd.2.2 p hp).1⟩]
  refine Finset.prod_pos fun p hp => ?_
  have hp100 : (100 : ℝ) < p := by exact_mod_cast lt_of_le_of_lt hP₀ (hd.2.2 p hp).1
  exact div_pos (by norm_num) (by linarith)

lemma hFunc_nonneg {P₀ d : ℕ} (hP₀ : 100 ≤ P₀) : 0 ≤ hFunc P₀ d := by
  unfold hFunc
  split_ifs with h
  · refine Finset.prod_nonneg fun p hp => ?_
    have hp100 : (100 : ℝ) < p := by exact_mod_cast lt_of_le_of_lt hP₀ (h.2 p hp)
    exact div_nonneg (by norm_num) (by linarith)
  · exact le_rfl

lemma gFunc_mul_of_coprime {P₀ w a b : ℕ} (ha : ValidDiv P₀ w a) (hb : ValidDiv P₀ w b)
    (hcop : a.Coprime b) : gFunc P₀ (a * b) = gFunc P₀ a * gFunc P₀ b := by
  have hab := validDiv_mul_of_coprime ha hb hcop
  unfold gFunc rho
  rw [if_pos ⟨hab.2.1, fun p hp => (hab.2.2 p hp).1⟩,
      if_pos ⟨ha.2.1, fun p hp => (ha.2.2 p hp).1⟩,
      if_pos ⟨hb.2.1, fun p hp => (hb.2.2 p hp).1⟩]
  rw [Nat.primeFactors_mul ha.1.ne' hb.1.ne', Finset.card_union_of_disjoint hcop.disjoint_primeFactors,
      pow_add, Nat.cast_mul]
  ring

lemma hFunc_mul_of_coprime {P₀ w a b : ℕ} (ha : ValidDiv P₀ w a) (hb : ValidDiv P₀ w b)
    (hcop : a.Coprime b) : hFunc P₀ (a * b) = hFunc P₀ a * hFunc P₀ b := by
  have hab := validDiv_mul_of_coprime ha hb hcop
  unfold hFunc
  rw [if_pos ⟨hab.2.1, fun p hp => (hab.2.2 p hp).1⟩,
      if_pos ⟨ha.2.1, fun p hp => (ha.2.2 p hp).1⟩,
      if_pos ⟨hb.2.1, fun p hp => (hb.2.2 p hp).1⟩]
  rw [Nat.primeFactors_mul ha.1.ne' hb.1.ne', Finset.prod_union hcop.disjoint_primeFactors]

/-- Fundamental Selberg divisor identity: for valid `d`, `1 / g(d) = ∑_{r | d} 1 / h(r)` —
equivalently, `∑_{r | d} h(r) = h(d) / g(d)`! -/
lemma sum_divisors_hFunc {P₀ w d : ℕ} (hP₀ : 100 ≤ P₀) (hd : ValidDiv P₀ w d) :
    ∑ r ∈ d.divisors, hFunc P₀ r = hFunc P₀ d / gFunc P₀ d := by
  -- For squarefree d, divisors biject with subsets of d.primeFactors via ∏_{p ∈ S} p!
  have h1 : ∑ r ∈ d.divisors, hFunc P₀ r = ∏ p ∈ d.primeFactors, (1 + 7 / ((p : ℝ) - 7)) := by
    rw [Finset.prod_one_add]
    refine Finset.sum_bij (fun r _ => r.primeFactors) ?_ ?_ ?_ ?_
    · intro r hr
      have hrd : r ∣ d := Nat.dvd_of_mem_divisors hr
      exact Finset.mem_powerset.mpr (Nat.primeFactors_mono hrd hd.1.ne')
    · intro r1 hr1 r2 hr2 heq
      have hsf1 : Squarefree r1 := hd.2.1.squarefree_of_dvd (Nat.dvd_of_mem_divisors hr1)
      have hsf2 : Squarefree r2 := hd.2.1.squarefree_of_dvd (Nat.dvd_of_mem_divisors hr2)
      rw [← Nat.prod_primeFactors_of_squarefree hsf1, ← Nat.prod_primeFactors_of_squarefree hsf2, heq]
    · intro S hS
      refine ⟨∏ p ∈ S, p, ?_, ?_⟩
      · have hSsub : S ⊆ d.primeFactors := Finset.mem_powerset.mp hS
        have hprod_dvd : (∏ p ∈ S, p) ∣ d := by
          rw [← Nat.prod_primeFactors_of_squarefree hd.2.1]
          exact Finset.prod_dvd_prod_of_subset _ _ _ hSsub
        exact Nat.mem_divisors.mpr ⟨hprod_dvd, hd.1.ne'⟩
      · have hSsub : S ⊆ d.primeFactors := Finset.mem_powerset.mp hS
        have hprime : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hSsub hp)
        exact primeFactors_prod_primes hprime
    · intro r hr
      have hrvalid := validDiv_of_dvd hd (Nat.dvd_of_mem_divisors hr)
      unfold hFunc
      rw [if_pos ⟨hrvalid.2.1, fun p hp => (hrvalid.2.2 p hp).1⟩]
  rw [h1]
  unfold hFunc gFunc rho
  rw [if_pos ⟨hd.2.1, fun p hp => (hd.2.2 p hp).1⟩,
      if_pos ⟨hd.2.1, fun p hp => (hd.2.2 p hp).1⟩]
  have hd_eq : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    have := Nat.prod_primeFactors_of_squarefree hd.2.1
    conv_lhs => rw [← this]
    push_cast; rfl
  have hpow : (7 : ℝ) ^ d.primeFactors.card = ∏ _p ∈ d.primeFactors, (7 : ℝ) := by
    simp
  rw [hd_eq, hpow, ← Finset.prod_div_distrib, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp100 : (100 : ℝ) < p := by exact_mod_cast lt_of_le_of_lt hP₀ (hd.2.2 p hp).1
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp7 : (p : ℝ) - 7 ≠ 0 := by linarith
  field_simp; ring

/-- Key Selberg diagonalization identity:
`g([d1, d2]) = g(d1) * g(d2) * ∑_{r | gcd d1 d2} 1 / h(r)`! -/
lemma gFunc_lcm_eq {P₀ w d1 d2 : ℕ} (hP₀ : 100 ≤ P₀)
    (h1 : ValidDiv P₀ w d1) (h2 : ValidDiv P₀ w d2) :
    gFunc P₀ (Nat.lcm d1 d2) =
      gFunc P₀ d1 * gFunc P₀ d2 * ∑ r ∈ (Nat.gcd d1 d2).divisors, (hFunc P₀ r)⁻¹ := by
  set g := Nat.gcd d1 d2
  have hg_dvd1 : g ∣ d1 := Nat.gcd_dvd_left d1 d2
  have hg_dvd2 : g ∣ d2 := Nat.gcd_dvd_right d1 d2
  have hg_valid : ValidDiv P₀ w g := validDiv_of_dvd h1 hg_dvd1
  -- Since d1, d2 are squarefree: lcm d1 d2 * g = d1 * d2, and g.Coprime (d1/g), g.Coprime (d2/g)
  have hlcm_eq : gFunc P₀ (Nat.lcm d1 d2) * gFunc P₀ g = gFunc P₀ d1 * gFunc P₀ d2 := by
    -- Write d1 = g * a, d2 = g * b with a, b, g pairwise coprime
    set a := d1 / g
    set b := d2 / g
    have hga : g * a = d1 := Nat.mul_div_cancel' hg_dvd1
    have hgb : g * b = d2 := Nat.mul_div_cancel' hg_dvd2
    have ha_valid : ValidDiv P₀ w a := validDiv_of_dvd h1 ⟨g, by rw [mul_comm]; exact hga.symm⟩
    have hb_valid : ValidDiv P₀ w b := validDiv_of_dvd h2 ⟨g, by rw [mul_comm]; exact hgb.symm⟩
    have hcop_ga : g.Coprime a := by
      have hsf := h1.2.1; rw [← hga] at hsf; exact coprime_of_squarefree_mul hsf
    have hcop_gb : g.Coprime b := by
      have hsf := h2.2.1; rw [← hgb] at hsf; exact coprime_of_squarefree_mul hsf
    have hcop_ab : a.Coprime b := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left d2 h1.1)
    have hlcm_gab : Nat.lcm d1 d2 = g * (a * b) := by
      have hmul := Nat.gcd_mul_lcm d1 d2
      have : g * (g * (a * b)) = g * Nat.lcm d1 d2 := by
        calc g * (g * (a * b)) = (g * a) * (g * b) := by ring
          _ = d1 * d2 := by rw [hga, hgb]
          _ = g * Nat.lcm d1 d2 := hmul.symm
      exact (Nat.eq_of_mul_eq_mul_left hg_valid.1 this).symm
    have hcop_g_ab : g.Coprime (a * b) := hcop_ga.mul_right hcop_gb
    rw [hlcm_gab, gFunc_mul_of_coprime hg_valid (validDiv_mul_of_coprime ha_valid hb_valid hcop_ab) hcop_g_ab,
        gFunc_mul_of_coprime ha_valid hb_valid hcop_ab,
        ← hga, ← hgb,
        gFunc_mul_of_coprime hg_valid ha_valid hcop_ga,
        gFunc_mul_of_coprime hg_valid hb_valid hcop_gb]
    ring
  -- Now show 1 / g(g) = ∑_{r | g} 1 / h(r):
  have hinv_g : (gFunc P₀ g)⁻¹ = ∑ r ∈ g.divisors, (hFunc P₀ r)⁻¹ := by
    -- By sum_divisors_hFunc: ∑_{r | g} h(r) = h(g) / g(g).
    -- Divide both sides by h(g), and substitute s = g / r: h(g / s) / h(g) = (h(s))⁻¹!
    have hsd := sum_divisors_hFunc hP₀ hg_valid
    have hhg : 0 < hFunc P₀ g := hFunc_pos hP₀ hg_valid
    have hgg : 0 < gFunc P₀ g := gFunc_pos hg_valid
    have hbij : ∑ r ∈ g.divisors, (hFunc P₀ r)⁻¹ = (∑ r ∈ g.divisors, hFunc P₀ r) / hFunc P₀ g := by
      rw [Finset.sum_div]
      refine Finset.sum_bij (fun r _ => g / r) ?_ ?_ ?_ ?_
      · intro r hr
        exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hr), hg_valid.1.ne'⟩
      · intro r1 hr1 r2 hr2 heq
        have h1' := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hr1)
        have h2' := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hr2)
        have hd_pos : 0 < g / r1 := Nat.div_pos (Nat.le_of_dvd hg_valid.1 (Nat.dvd_of_mem_divisors hr1))
          (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hr1) hg_valid.1)
        rw [← heq] at h2'
        exact Nat.eq_of_mul_eq_mul_right hd_pos (h1'.trans h2'.symm)
      · intro s hs
        refine ⟨g / s, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hs), hg_valid.1.ne'⟩, ?_⟩
        exact Nat.div_div_self (Nat.dvd_of_mem_divisors hs) hg_valid.1.ne'
      · intro r hr
        have hrd := Nat.dvd_of_mem_divisors hr
        have hr_valid := validDiv_of_dvd hg_valid hrd
        have hgr_valid := validDiv_of_dvd hg_valid (Nat.div_dvd_of_dvd hrd)
        have hmul_eq : r * (g / r) = g := Nat.mul_div_cancel' hrd
        have hcop : r.Coprime (g / r) := by
          have hsf := hg_valid.2.1; rw [← hmul_eq] at hsf; exact coprime_of_squarefree_mul hsf
        have hhmul : hFunc P₀ g = hFunc P₀ r * hFunc P₀ (g / r) := by
          conv_lhs => rw [← hmul_eq]
          exact hFunc_mul_of_coprime hr_valid hgr_valid hcop
        have hrp := (hFunc_pos hP₀ hr_valid).ne'
        have hgrp := (hFunc_pos hP₀ hgr_valid).ne'
        rw [hhmul]
        field_simp
    rw [hbij, hsd]
    field_simp
  have hgg : gFunc P₀ g ≠ 0 := (gFunc_pos hg_valid).ne'
  rw [← hinv_g]
  calc gFunc P₀ (Nat.lcm d1 d2)
      = (gFunc P₀ (Nat.lcm d1 d2) * gFunc P₀ g) * (gFunc P₀ g)⁻¹ := by field_simp
    _ = gFunc P₀ d1 * gFunc P₀ d2 * (gFunc P₀ g)⁻¹ := by rw [hlcm_eq]

/-- The Selberg denominator `G_w(R) = ∑_{r <= R, ValidDiv P₀ w r} h(r)`. -/
noncomputable def GSum (P₀ w R : ℕ) : ℝ :=
  ∑ r ∈ (Icc 1 R).filter (fun r => ValidDiv P₀ w r), hFunc P₀ r

lemma GSum_pos {P₀ w R : ℕ} (hP₀ : 100 ≤ P₀) (hR : 1 ≤ R) : 0 < GSum P₀ w R := by
  unfold GSum
  have h1mem : 1 ∈ (Icc 1 R).filter (fun r => ValidDiv P₀ w r) :=
    mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hR⟩, validDiv_one P₀ w⟩
  have h1val : hFunc P₀ 1 = 1 := by
    unfold hFunc
    rw [if_pos ⟨squarefree_one, by simp⟩]
    simp
  have hle := Finset.single_le_sum (f := hFunc P₀) (fun r _ => hFunc_nonneg hP₀) h1mem
  linarith

/-- Optimal Selberg weights `λ_d`: supported on `ValidDiv P₀ w d ∧ d <= R`, with `λ_1 = 1` and `|λ_d| <= 1`. -/
noncomputable def selbergLambda (P₀ w R d : ℕ) : ℝ :=
  if ValidDiv P₀ w d ∧ d ≤ R then
    ((-1 : ℝ) ^ d.primeFactors.card / (gFunc P₀ d * GSum P₀ w R)) *
      ∑ r ∈ ((Icc 1 R).filter (fun r => ValidDiv P₀ w r)).filter (fun r => d ∣ r), hFunc P₀ r
  else 0

lemma selbergLambda_one {P₀ w R : ℕ} (hP₀ : 100 ≤ P₀) (hR : 1 ≤ R) :
    selbergLambda P₀ w R 1 = 1 := by
  unfold selbergLambda
  rw [if_pos ⟨validDiv_one P₀ w, hR⟩]
  have hg1 : gFunc P₀ 1 = 1 := by
    unfold gFunc rho
    rw [if_pos ⟨squarefree_one, by simp⟩]
    simp
  have hfilt : ((Icc 1 R).filter (fun r => ValidDiv P₀ w r)).filter (fun r => 1 ∣ r) =
      (Icc 1 R).filter (fun r => ValidDiv P₀ w r) := by
    ext r; simp
  rw [hfilt, Nat.primeFactors_one, card_empty, pow_zero, hg1, one_mul]
  change 1 / GSum P₀ w R * GSum P₀ w R = 1
  have hG := (GSum_pos (w := w) hP₀ hR).ne'
  field_simp

lemma abs_selbergLambda_le_one {P₀ w R d : ℕ} (hP₀ : 100 ≤ P₀) (hR : 1 ≤ R) :
    |selbergLambda P₀ w R d| ≤ 1 := by
  unfold selbergLambda
  split_ifs with hd
  · have hG := GSum_pos (w := w) hP₀ hR
    have hgd := gFunc_pos hd.1
    have hsum_nn : 0 ≤ ∑ r ∈ ((Icc 1 R).filter (fun r => ValidDiv P₀ w r)).filter (fun r => d ∣ r), hFunc P₀ r :=
      Finset.sum_nonneg fun r _ => hFunc_nonneg hP₀
    rw [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (mul_pos hgd hG),
        abs_of_nonneg hsum_nn, one_div, inv_mul_le_iff₀ (mul_pos hgd hG), mul_one]
    -- Show ∑_{d | r <= R, valid} h(r) <= g(d) * GSum P₀ w R!
    -- Write r = d * u (with u <= R/d, valid, coprime to d). Then h(r) = h(d) * h(u).
    -- Multiply by ∑_{a | d} h(a) = h(d) / g(d):
    -- (h(d) / g(d)) * ∑_{u <= R/d, valid, cop d} h(u) = ∑_{a | d} ∑_{u} h(a * u) <= GSum P₀ w R!
    let U := ((Icc 1 (R / d)).filter (fun u => ValidDiv P₀ w u)).filter (fun u => u.Coprime d)
    have hsum_eq :
        ∑ r ∈ ((Icc 1 R).filter (fun r => ValidDiv P₀ w r)).filter (fun r => d ∣ r), hFunc P₀ r =
          hFunc P₀ d * ∑ u ∈ U, hFunc P₀ u := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun r _ => r / d) ?_ ?_ ?_ ?_
      · intro r hr
        have hr1 := (mem_filter.mp (mem_filter.mp hr).1).1
        have hrv := (mem_filter.mp (mem_filter.mp hr).1).2
        have hrd := (mem_filter.mp hr).2
        have hu_pos : 0 < r / d := Nat.div_pos (Nat.le_of_dvd hrv.1 hrd) hd.1.1
        have hu_le : r / d ≤ R / d := Nat.div_le_div_right (mem_Icc.mp hr1).2
        have hu_valid := validDiv_of_dvd hrv (Nat.div_dvd_of_dvd hrd)
        have hmul : d * (r / d) = r := Nat.mul_div_cancel' hrd
        have hcop : (r / d).Coprime d := by
          have hsf := hrv.2.1; rw [← hmul] at hsf; exact (coprime_of_squarefree_mul hsf).symm
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hu_pos, hu_le⟩, hu_valid⟩, hcop⟩
      · intro r1 hr1 r2 hr2 heq
        have h1' := Nat.mul_div_cancel' (mem_filter.mp hr1).2
        have h2' := Nat.mul_div_cancel' (mem_filter.mp hr2).2
        rw [← h1', ← h2', heq]
      · intro u hu
        have hu1 := (mem_filter.mp (mem_filter.mp hu).1).1
        have huv := (mem_filter.mp (mem_filter.mp hu).1).2
        have hcop := (mem_filter.mp hu).2
        refine ⟨d * u, ?_, Nat.mul_div_cancel_left u hd.1.1⟩
        have hdu_pos : 1 ≤ d * u := Nat.mul_pos hd.1.1 huv.1
        have hdu_le : d * u ≤ R :=
          (Nat.mul_le_mul_left d (mem_Icc.mp hu1).2).trans (Nat.mul_div_le R d)
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hdu_pos, hdu_le⟩,
          validDiv_mul_of_coprime hd.1 huv hcop.symm⟩, dvd_mul_right d u⟩
      · intro r hr
        have hrv := (mem_filter.mp (mem_filter.mp hr).1).2
        have hrd := (mem_filter.mp hr).2
        have hu_valid := validDiv_of_dvd hrv (Nat.div_dvd_of_dvd hrd)
        have hmul : d * (r / d) = r := Nat.mul_div_cancel' hrd
        have hcop : d.Coprime (r / d) := by
          have hsf := hrv.2.1; rw [← hmul] at hsf; exact coprime_of_squarefree_mul hsf
        conv_lhs => rw [← hmul]
        exact hFunc_mul_of_coprime hd.1 hu_valid hcop
    rw [hsum_eq]
    have hprod_le : (hFunc P₀ d / gFunc P₀ d) * ∑ u ∈ U, hFunc P₀ u ≤ GSum P₀ w R := by
      rw [← sum_divisors_hFunc hP₀ hd.1, Finset.sum_mul_sum, ← Finset.sum_product']
      unfold GSum
      have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) ↑(d.divisors ×ˢ U) := by
        intro p1 hp1 p2 hp2 heq
        rw [Finset.mem_coe, mem_product] at hp1 hp2
        dsimp only at heq
        have ha1 : p1.1 ∣ d := Nat.dvd_of_mem_divisors hp1.1
        have ha2 : p2.1 ∣ d := Nat.dvd_of_mem_divisors hp2.1
        have hu1_cop : p1.2.Coprime d := (mem_filter.mp hp1.2).2
        have hu2_cop : p2.2.Coprime d := (mem_filter.mp hp2.2).2
        have ha1_dvd : p1.1 ∣ p2.1 :=
          (hu2_cop.coprime_dvd_right ha1).symm.dvd_of_dvd_mul_right ⟨p1.2, by rw [← heq]⟩
        have ha2_dvd : p2.1 ∣ p1.1 :=
          (hu1_cop.coprime_dvd_right ha2).symm.dvd_of_dvd_mul_right ⟨p2.2, by rw [heq]⟩
        have ha_eq : p1.1 = p2.1 := Nat.dvd_antisymm ha1_dvd ha2_dvd
        have ha1_pos : 0 < p1.1 := Nat.pos_of_dvd_of_pos ha1 hd.1.1
        have hu_eq : p1.2 = p2.2 := Nat.eq_of_mul_eq_mul_left ha1_pos (by rw [← ha_eq] at heq; exact heq)
        exact Prod.ext ha_eq hu_eq
      have hsub : (d.divisors ×ˢ U).image (fun p : ℕ × ℕ => p.1 * p.2) ⊆
          (Icc 1 R).filter (fun r => ValidDiv P₀ w r) := by
        intro r hr
        obtain ⟨⟨a, u⟩, hau, rfl⟩ := mem_image.mp hr
        obtain ⟨ha, hu⟩ := mem_product.mp hau
        have had : a ∣ d := Nat.dvd_of_mem_divisors ha
        have hav := validDiv_of_dvd hd.1 had
        have hu1 := (mem_filter.mp (mem_filter.mp hu).1).1
        have huv := (mem_filter.mp (mem_filter.mp hu).1).2
        have hcop := (mem_filter.mp hu).2
        have ha_le : a ≤ d := Nat.le_of_dvd hd.1.1 had
        have hau_le : a * u ≤ R :=
          (Nat.mul_le_mul ha_le (mem_Icc.mp hu1).2).trans (Nat.mul_div_le R d)
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hav.1 huv.1, hau_le⟩,
          validDiv_mul_of_coprime hav huv (hcop.coprime_dvd_right had).symm⟩
      calc ∑ x ∈ d.divisors ×ˢ U, hFunc P₀ x.1 * hFunc P₀ x.2
          = ∑ x ∈ d.divisors ×ˢ U, hFunc P₀ (x.1 * x.2) := by
            refine Finset.sum_congr rfl fun ⟨a, u⟩ hau => ?_
            obtain ⟨ha, hu⟩ := mem_product.mp hau
            have had := Nat.dvd_of_mem_divisors ha
            have hav := validDiv_of_dvd hd.1 had
            have huv := (mem_filter.mp (mem_filter.mp hu).1).2
            have hcop := (mem_filter.mp hu).2
            exact (hFunc_mul_of_coprime hav huv (hcop.coprime_dvd_right had).symm).symm
        _ = ∑ r ∈ (d.divisors ×ˢ U).image (fun p : ℕ × ℕ => p.1 * p.2), hFunc P₀ r :=
            (Finset.sum_image hinj).symm
        _ ≤ ∑ r ∈ (Icc 1 R).filter (fun r => ValidDiv P₀ w r), hFunc P₀ r :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => hFunc_nonneg hP₀
    have := mul_le_mul_of_nonneg_left hprod_le hgd.le
    rw [← mul_assoc, mul_div_cancel₀ _ hgd.ne'] at this
    exact this
  · simp

/-- Exact Selberg quadratic form evaluation:
`∑_{d1, d2} λ_{d1} * λ_{d2} * g([d1, d2]) = 1 / G_w(R)`! -/
lemma selberg_quad_eq {P₀ w R : ℕ} (hP₀ : 100 ≤ P₀) (hR : 1 ≤ R) :
    let D := (Icc 1 R).filter (fun d => ValidDiv P₀ w d)
    ∑ d1 ∈ D, ∑ d2 ∈ D,
      selbergLambda P₀ w R d1 * selbergLambda P₀ w R d2 * gFunc P₀ (Nat.lcm d1 d2) =
        1 / GSum P₀ w R := by
  intro D
  have hG := GSum_pos (w := w) hP₀ hR
  -- First compute the diagonalized coordinate z_r = ∑_{d ∈ D, r | d} λ_d * g(d) = (-1)^{ω(r)} * h(r) / G!
  have hz : ∀ r ∈ D,
      ∑ d ∈ D.filter (fun d => r ∣ d), selbergLambda P₀ w R d * gFunc P₀ d =
        (-1 : ℝ) ^ r.primeFactors.card * hFunc P₀ r / GSum P₀ w R := by
    intro r hr
    have hrv : ValidDiv P₀ w r := (mem_filter.mp hr).2
    -- Plug in selbergLambda:
    have h1 : ∑ d ∈ D.filter (fun d => r ∣ d), selbergLambda P₀ w R d * gFunc P₀ d =
        (1 / GSum P₀ w R) * ∑ d ∈ D.filter (fun d => r ∣ d),
          (-1 : ℝ) ^ d.primeFactors.card * ∑ s ∈ D.filter (fun s => d ∣ s), hFunc P₀ s := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hdD := (mem_filter.mp hd).1
      have hdv := (mem_filter.mp hdD).2
      have hdR := (mem_Icc.mp (mem_filter.mp hdD).1).2
      unfold selbergLambda
      rw [if_pos ⟨hdv, hdR⟩]
      have hgd := (gFunc_pos hdv).ne'
      have hG0 := hG.ne'
      field_simp; rfl
    rw [h1]
    -- Swap sums over d and s: for each s ∈ D with r | s, the inner sum over r | d | s is
    -- ∑_{r | d | s} (-1)^{ω(d)} = (-1)^{ω(r)} * ∑_{u | (s/r)} (-1)^{ω(u)} = (-1)^{ω(r)} * [s = r]!
    have hswap :
        ∑ d ∈ D.filter (fun d => r ∣ d),
          (-1 : ℝ) ^ d.primeFactors.card * ∑ s ∈ D.filter (fun s => d ∣ s), hFunc P₀ s =
        ∑ s ∈ D.filter (fun s => r ∣ s),
          hFunc P₀ s * ∑ d ∈ s.divisors.filter (fun d => r ∣ d), (-1 : ℝ) ^ d.primeFactors.card := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_sigma', Finset.sum_sigma']
      refine Finset.sum_bij (fun x _ => Sigma.mk x.2 x.1) ?_ ?_ ?_ ?_
      · intro ⟨d, s⟩ hds
        simp only [mem_sigma, mem_filter] at hds ⊢
        refine ⟨⟨hds.2.1, hds.1.2.trans hds.2.2⟩, ⟨Nat.mem_divisors.mpr ⟨hds.2.2, (mem_filter.mp hds.2.1).2.1.ne'⟩, hds.1.2⟩⟩
      · intro ⟨d1, s1⟩ _ ⟨d2, s2⟩ _ heq
        simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
        exact Sigma.ext heq.2 (heq_of_eq heq.1)
      · intro ⟨s, d⟩ hsd
        simp only [mem_sigma, mem_filter] at hsd ⊢
        have hds : d ∣ s := Nat.dvd_of_mem_divisors hsd.2.1
        have hsD := hsd.1.1
        have hsv := (mem_filter.mp hsD).2
        have hsR := (mem_Icc.mp (mem_filter.mp hsD).1).2
        have hdv := validDiv_of_dvd hsv hds
        have hdD : d ∈ D := mem_filter.mpr ⟨mem_Icc.mpr ⟨hdv.1, (Nat.le_of_dvd hsv.1 hds).trans hsR⟩, hdv⟩
        exact ⟨⟨d, s⟩, ⟨⟨hdD, hsd.2.2⟩, ⟨hsD, hds⟩⟩, rfl⟩
      · intro ⟨d, s⟩ _
        ring
    rw [hswap]
    have hmob : ∀ s ∈ D.filter (fun s => r ∣ s),
        ∑ d ∈ s.divisors.filter (fun d => r ∣ d), (-1 : ℝ) ^ d.primeFactors.card =
          if s = r then (-1 : ℝ) ^ r.primeFactors.card else 0 := by
      intro s hs
      have hsv := (mem_filter.mp (mem_filter.mp hs).1).2
      have hrs := (mem_filter.mp hs).2
      set q := s / r
      have hmul : r * q = s := Nat.mul_div_cancel' hrs
      have hq_valid := validDiv_of_dvd hsv (Nat.div_dvd_of_dvd hrs)
      have hcop : r.Coprime q := by
        have hsf := hsv.2.1; rw [← hmul] at hsf; exact coprime_of_squarefree_mul hsf
      -- Biject d ∈ s.divisors with r | d to u ∈ q.divisors via d = r * u
      have hbij : ∑ d ∈ s.divisors.filter (fun d => r ∣ d), (-1 : ℝ) ^ d.primeFactors.card =
          (-1 : ℝ) ^ r.primeFactors.card * ∑ u ∈ q.divisors, (-1 : ℝ) ^ u.primeFactors.card := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun d _ => d / r) ?_ ?_ ?_ ?_
        · intro d hd
          have hds := Nat.dvd_of_mem_divisors (mem_filter.mp hd).1
          have hrd := (mem_filter.mp hd).2
          have huq : d / r ∣ q := by
            obtain ⟨t, ht⟩ := hds
            refine ⟨t, ?_⟩
            apply Nat.eq_of_mul_eq_mul_left hrv.1
            calc r * q = s := hmul
              _ = d * t := ht
              _ = (r * (d / r)) * t := by rw [Nat.mul_div_cancel' hrd]
              _ = r * ((d / r) * t) := by ring
          exact Nat.mem_divisors.mpr ⟨huq, hq_valid.1.ne'⟩
        · intro d1 hd1 d2 hd2 heq
          rw [← Nat.mul_div_cancel' (mem_filter.mp hd1).2,
              ← Nat.mul_div_cancel' (mem_filter.mp hd2).2, heq]
        · intro u hu
          have huq := Nat.dvd_of_mem_divisors hu
          refine ⟨r * u, ?_, Nat.mul_div_cancel_left u hrv.1⟩
          exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hmul ▸ Nat.mul_dvd_mul_left r huq, hsv.1.ne'⟩,
            dvd_mul_right r u⟩
        · intro d hd
          have hrd := (mem_filter.mp hd).2
          have hu_valid := validDiv_of_dvd (validDiv_of_dvd hsv (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1))
            (Nat.div_dvd_of_dvd hrd)
          have hdm : r * (d / r) = d := Nat.mul_div_cancel' hrd
          have hcop_ru : r.Coprime (d / r) := by
            have hsf := (validDiv_of_dvd hsv (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)).2.1
            rw [← hdm] at hsf; exact coprime_of_squarefree_mul hsf
          conv_lhs => rw [← hdm]
          rw [Nat.primeFactors_mul hrv.1.ne' hu_valid.1.ne',
              Finset.card_union_of_disjoint hcop_ru.disjoint_primeFactors, pow_add]
      rw [hbij]
      change ValidDiv P₀ w q at hq_valid
      -- ∑_{u | q} (-1)^{ω(u)} = ∏_{p | q} (1 + (-1)) = if q = 1 then 1 else 0
      have hprod_mob : ∑ u ∈ q.divisors, (-1 : ℝ) ^ u.primeFactors.card =
          ∏ _p ∈ q.primeFactors, (1 + (-1 : ℝ)) := by
        rw [Finset.prod_one_add]
        refine Finset.sum_bij (fun u _ => u.primeFactors) ?_ ?_ ?_ ?_
        · intro u hu
          exact Finset.mem_powerset.mpr (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hu) hq_valid.1.ne')
        · intro u1 hu1 u2 hu2 heq
          have hs1 := hq_valid.2.1.squarefree_of_dvd (Nat.dvd_of_mem_divisors hu1)
          have hs2 := hq_valid.2.1.squarefree_of_dvd (Nat.dvd_of_mem_divisors hu2)
          rw [← Nat.prod_primeFactors_of_squarefree hs1, ← Nat.prod_primeFactors_of_squarefree hs2, heq]
        · intro S hS
          have hSsub := Finset.mem_powerset.mp hS
          refine ⟨∏ p ∈ S, p, ?_, primeFactors_prod_primes (fun p hp => Nat.prime_of_mem_primeFactors (hSsub hp))⟩
          have hdvd : (∏ p ∈ S, p) ∣ q := by
            rw [← Nat.prod_primeFactors_of_squarefree hq_valid.2.1]
            exact Finset.prod_dvd_prod_of_subset _ _ _ hSsub
          exact Nat.mem_divisors.mpr ⟨hdvd, hq_valid.1.ne'⟩
        · intro u _; simp
      rw [hprod_mob]
      by_cases hsr : s = r
      · subst hsr
        have hq1 : q = 1 := Nat.div_self hrv.1
        rw [if_pos rfl, hq1, Nat.primeFactors_one, Finset.prod_empty, mul_one]
      · rw [if_neg hsr]
        have hqne1 : q ≠ 1 := fun h1 => hsr (by rw [← hmul, h1, mul_one])
        have hne : q.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by have := hq_valid.1; omega)
        obtain ⟨p, hp⟩ := hne
        rw [Finset.prod_eq_zero hp (by norm_num), mul_zero]
    rw [Finset.sum_congr rfl (fun s hs => by rw [hmob s hs])]
    have hrmem : r ∈ D.filter (fun s => r ∣ s) := mem_filter.mpr ⟨hr, dvd_refl r⟩
    rw [Finset.sum_eq_single r (fun s _ hne => by rw [if_neg hne, mul_zero]) (fun h => absurd hrmem h),
        if_pos rfl]
    ring
  -- Now expand the quadratic form using gFunc_lcm_eq!
  calc ∑ d1 ∈ D, ∑ d2 ∈ D,
        selbergLambda P₀ w R d1 * selbergLambda P₀ w R d2 * gFunc P₀ (Nat.lcm d1 d2)
      = ∑ d1 ∈ D, ∑ d2 ∈ D,
          (selbergLambda P₀ w R d1 * gFunc P₀ d1) * (selbergLambda P₀ w R d2 * gFunc P₀ d2) *
            ∑ r ∈ (Nat.gcd d1 d2).divisors, (hFunc P₀ r)⁻¹ := by
        refine Finset.sum_congr rfl fun d1 hd1 => Finset.sum_congr rfl fun d2 hd2 => ?_
        rw [gFunc_lcm_eq hP₀ (mem_filter.mp hd1).2 (mem_filter.mp hd2).2]
        ring
    _ = ∑ r ∈ D, (hFunc P₀ r)⁻¹ *
          (∑ d ∈ D.filter (fun d => r ∣ d), selbergLambda P₀ w R d * gFunc P₀ d) ^ 2 := by
        -- Swap sum over (d1, d2) with sum over r ∈ D dividing both d1 and d2
        have hinner : ∀ d1 ∈ D, ∀ d2 ∈ D,
            ∑ r ∈ (Nat.gcd d1 d2).divisors, (hFunc P₀ r)⁻¹ =
              ∑ r ∈ D, if r ∣ d1 ∧ r ∣ d2 then (hFunc P₀ r)⁻¹ else 0 := by
          intro d1 hd1 d2 hd2
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext r
          simp only [Nat.mem_divisors, mem_filter, mem_Icc, D]
          have hd1v := (mem_filter.mp hd1).2
          have hd1R := (mem_Icc.mp (mem_filter.mp hd1).1).2
          have hd2v := (mem_filter.mp hd2).2
          constructor
          · rintro ⟨hrg, _⟩
            have hr1 := hrg.trans (Nat.gcd_dvd_left d1 d2)
            have hr2 := hrg.trans (Nat.gcd_dvd_right d1 d2)
            have hrv := validDiv_of_dvd hd1v hr1
            exact ⟨⟨⟨hrv.1, (Nat.le_of_dvd hd1v.1 hr1).trans hd1R⟩, hrv⟩, hr1, hr2⟩
          · rintro ⟨_, hr1, hr2⟩
            exact ⟨Nat.dvd_gcd hr1 hr2, (Nat.gcd_pos_of_pos_left d2 hd1v.1).ne'⟩
        simp_rw [Finset.mul_sum]
        calc ∑ d1 ∈ D, ∑ d2 ∈ D, ∑ r ∈ (Nat.gcd d1 d2).divisors,
              (selbergLambda P₀ w R d1 * gFunc P₀ d1) * (selbergLambda P₀ w R d2 * gFunc P₀ d2) *
                (hFunc P₀ r)⁻¹
            = ∑ d1 ∈ D, ∑ d2 ∈ D, ∑ r ∈ D,
                if r ∣ d1 ∧ r ∣ d2 then
                  (hFunc P₀ r)⁻¹ * ((selbergLambda P₀ w R d1 * gFunc P₀ d1) *
                    (selbergLambda P₀ w R d2 * gFunc P₀ d2))
                else 0 := by
              refine Finset.sum_congr rfl fun d1 hd1 => Finset.sum_congr rfl fun d2 hd2 => ?_
              rw [← Finset.mul_sum, hinner d1 hd1 d2 hd2, Finset.mul_sum]
              refine Finset.sum_congr rfl fun r _ => ?_
              split_ifs <;> ring
          _ = ∑ r ∈ D, (hFunc P₀ r)⁻¹ *
                (∑ d ∈ D.filter (fun d => r ∣ d), selbergLambda P₀ w R d * gFunc P₀ d) ^ 2 := by
              rw [Finset.sum_comm]
              conv_lhs =>
                arg 2; ext d1; rw [Finset.sum_comm]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun r _ => ?_
              have hsf_r : ∑ d ∈ D.filter (fun d => r ∣ d), selbergLambda P₀ w R d * gFunc P₀ d =
                  ∑ d ∈ D, if r ∣ d then selbergLambda P₀ w R d * gFunc P₀ d else 0 := Finset.sum_filter _ _
              rw [hsf_r, sq, Finset.sum_mul, Finset.mul_sum]
              refine Finset.sum_congr rfl fun d1 _ => ?_
              rw [Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun d2 _ => ?_
              by_cases h1' : r ∣ d1 <;> by_cases h2' : r ∣ d2 <;> simp [h1', h2']
              left; ring
    _ = ∑ r ∈ D, hFunc P₀ r / (GSum P₀ w R) ^ 2 := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [hz r hr]
        have hhr := (hFunc_pos hP₀ (mem_filter.mp hr).2).ne'
        have hsq : ((-1 : ℝ) ^ r.primeFactors.card) ^ 2 = 1 := by
          rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
        field_simp
        exact hsq
    _ = 1 / GSum P₀ w R := by
        rw [← Finset.sum_div]
        change GSum P₀ w R / (GSum P₀ w R) ^ 2 = 1 / GSum P₀ w R
        have hG0 := hG.ne'
        field_simp

/-- General Selberg upper bound sieve on any finite set `I` with integer sequence `F : ℕ → ℕ`. -/
theorem selberg_upper {P₀ w R : ℕ} (hP₀ : 100 ≤ P₀) (hR : 1 ≤ R)
    (I : Finset ℕ) (F : ℕ → ℕ) (X K_err : ℝ) (hK : 0 ≤ K_err)
    (happrox : ∀ d : ℕ, ValidDiv P₀ w d →
      |((I.filter (fun m => d ∣ F m)).card : ℝ) - gFunc P₀ d * X| ≤ K_err * rho P₀ d) :
    ((I.filter (fun m => ∀ p : ℕ, p.Prime → P₀ < p → p < w → ¬ p ∣ F m)).card : ℝ) ≤
      X / GSum P₀ w R + K_err * (∑ d ∈ (Icc 1 R).filter (fun d => ValidDiv P₀ w d), rho P₀ d) ^ 2 := by
  let D := (Icc 1 R).filter (fun d => ValidDiv P₀ w d)
  let S := I.filter (fun m => ∀ p : ℕ, p.Prime → P₀ < p → p < w → ¬ p ∣ F m)
  -- For every m ∈ S, the only d ∈ D dividing F m is d = 1!
  have hS_weight : ∀ m ∈ S, (∑ d ∈ D.filter (fun d => d ∣ F m), selbergLambda P₀ w R d) ^ 2 = 1 := by
    intro m hm
    have hm_rough := (mem_filter.mp hm).2
    have hfilt : D.filter (fun d => d ∣ F m) = {1} := by
      ext d
      simp only [mem_filter, mem_singleton, D, mem_Icc]
      constructor
      · rintro ⟨⟨⟨hd1le, _⟩, hdv⟩, hdm⟩
        by_contra hd1
        have hdgt1 : 1 < d := by omega
        obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hdgt1
        have hpr := Nat.prime_of_mem_primeFactors hp
        have hpd := (Nat.dvd_of_mem_primeFactors hp).trans hdm
        have hbounds := hdv.2.2 p hp
        exact hm_rough p hpr hbounds.1 hbounds.2 hpd
      · rintro rfl
        exact ⟨⟨⟨le_rfl, hR⟩, validDiv_one P₀ w⟩, one_dvd _⟩
    rw [hfilt, Finset.sum_singleton, selbergLambda_one hP₀ hR, one_pow]
  -- Step 1: |S| <= ∑_{m ∈ I} (∑_{d ∈ D, d | F m} λ_d)^2
  have hstep1 : (S.card : ℝ) ≤ ∑ m ∈ I, (∑ d ∈ D.filter (fun d => d ∣ F m), selbergLambda P₀ w R d) ^ 2 := by
    have h1 : (S.card : ℝ) = ∑ m ∈ S, (∑ d ∈ D.filter (fun d => d ∣ F m), selbergLambda P₀ w R d) ^ 2 := by
      rw [Finset.sum_congr rfl hS_weight, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [h1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun m _ _ => sq_nonneg _
  -- Step 2: Expand the square and swap sums
  have hstep2 :
      ∑ m ∈ I, (∑ d ∈ D.filter (fun d => d ∣ F m), selbergLambda P₀ w R d) ^ 2 =
        ∑ d1 ∈ D, ∑ d2 ∈ D,
          selbergLambda P₀ w R d1 * selbergLambda P₀ w R d2 *
            ((I.filter (fun m => Nat.lcm d1 d2 ∣ F m)).card : ℝ) := by
    have hsq : ∀ m ∈ I,
        (∑ d ∈ D.filter (fun d => d ∣ F m), selbergLambda P₀ w R d) ^ 2 =
          ∑ d1 ∈ D, ∑ d2 ∈ D,
            if Nat.lcm d1 d2 ∣ F m then selbergLambda P₀ w R d1 * selbergLambda P₀ w R d2 else 0 := by
      intro m _
      have hsf_m : ∑ d ∈ D.filter (fun d => d ∣ F m), selbergLambda P₀ w R d =
          ∑ d ∈ D, if d ∣ F m then selbergLambda P₀ w R d else 0 := Finset.sum_filter _ _
      rw [hsf_m, sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d1 _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d2 _ => ?_
      simp only [Nat.lcm_dvd_iff]
      by_cases h1 : d1 ∣ F m <;> by_cases h2 : d2 ∣ F m <;> simp [h1, h2]
    rw [Finset.sum_congr rfl hsq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d1 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d2 _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- Step 3: Split card into main term g([d1,d2]) * X + error term
  have hstep3 :
      ∑ d1 ∈ D, ∑ d2 ∈ D,
        selbergLambda P₀ w R d1 * selbergLambda P₀ w R d2 *
          ((I.filter (fun m => Nat.lcm d1 d2 ∣ F m)).card : ℝ) ≤
      (∑ d1 ∈ D, ∑ d2 ∈ D,
        selbergLambda P₀ w R d1 * selbergLambda P₀ w R d2 * gFunc P₀ (Nat.lcm d1 d2)) * X +
      K_err * ∑ d1 ∈ D, ∑ d2 ∈ D, rho P₀ d1 * rho P₀ d2 := by
    have hsplit :
        ∑ d1 ∈ D, ∑ d2 ∈ D,
          selbergLambda P₀ w R d1 * selbergLambda P₀ w R d2 *
            ((I.filter (fun m => Nat.lcm d1 d2 ∣ F m)).card : ℝ) -
        (∑ d1 ∈ D, ∑ d2 ∈ D,
          selbergLambda P₀ w R d1 * selbergLambda P₀ w R d2 * gFunc P₀ (Nat.lcm d1 d2)) * X =
        ∑ d1 ∈ D, ∑ d2 ∈ D,
          selbergLambda P₀ w R d1 * selbergLambda P₀ w R d2 *
            (((I.filter (fun m => Nat.lcm d1 d2 ∣ F m)).card : ℝ) - gFunc P₀ (Nat.lcm d1 d2) * X) := by
      simp_rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d1 _ => Finset.sum_congr rfl fun d2 _ => by ring
    suffices h :
        ∑ d1 ∈ D, ∑ d2 ∈ D,
          selbergLambda P₀ w R d1 * selbergLambda P₀ w R d2 *
            (((I.filter (fun m => Nat.lcm d1 d2 ∣ F m)).card : ℝ) - gFunc P₀ (Nat.lcm d1 d2) * X) ≤
        ∑ d1 ∈ D, ∑ d2 ∈ D, K_err * (rho P₀ d1 * rho P₀ d2) by
      have hmul_pull : ∑ d1 ∈ D, ∑ d2 ∈ D, K_err * (rho P₀ d1 * rho P₀ d2) =
          K_err * ∑ d1 ∈ D, ∑ d2 ∈ D, rho P₀ d1 * rho P₀ d2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d1 _ => (Finset.mul_sum _ _ _).symm
      linarith
    refine Finset.sum_le_sum fun d1 hd1 => Finset.sum_le_sum fun d2 hd2 => ?_
    have h1v := (mem_filter.mp hd1).2
    have h2v := (mem_filter.mp hd2).2
    have hlcmv := validDiv_lcm h1v h2v
    have hrem := happrox (Nat.lcm d1 d2) hlcmv
    have hlam1 := abs_selbergLambda_le_one (P₀ := P₀) (w := w) (R := R) (d := d1) hP₀ hR
    have hlam2 := abs_selbergLambda_le_one (P₀ := P₀) (w := w) (R := R) (d := d2) hP₀ hR
    have hrho_lcm : rho P₀ (Nat.lcm d1 d2) ≤ rho P₀ d1 * rho P₀ d2 := by
      unfold rho
      rw [if_pos ⟨hlcmv.2.1, fun p hp => (hlcmv.2.2 p hp).1⟩,
          if_pos ⟨h1v.2.1, fun p hp => (h1v.2.2 p hp).1⟩,
          if_pos ⟨h2v.2.1, fun p hp => (h2v.2.2 p hp).1⟩, ← pow_add]
      have hcard : (Nat.lcm d1 d2).primeFactors.card ≤ d1.primeFactors.card + d2.primeFactors.card := by
        have hsub : (Nat.lcm d1 d2).primeFactors ⊆ d1.primeFactors ∪ d2.primeFactors := by
          intro p hp
          have hpr := Nat.prime_of_mem_primeFactors hp
          have hdvd := (Nat.dvd_of_mem_primeFactors hp).trans (Nat.lcm_dvd (dvd_mul_right d1 d2) (dvd_mul_left d2 d1))
          rw [mem_union]
          rcases hpr.dvd_mul.mp hdvd with h | h
          · exact Or.inl (Nat.mem_primeFactors.mpr ⟨hpr, h, h1v.1.ne'⟩)
          · exact Or.inr (Nat.mem_primeFactors.mpr ⟨hpr, h, h2v.1.ne'⟩)
        exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      exact pow_le_pow_right₀ (by norm_num) hcard
    calc selbergLambda P₀ w R d1 * selbergLambda P₀ w R d2 *
            (((I.filter (fun m => Nat.lcm d1 d2 ∣ F m)).card : ℝ) - gFunc P₀ (Nat.lcm d1 d2) * X)
        ≤ |selbergLambda P₀ w R d1 * selbergLambda P₀ w R d2 *
            (((I.filter (fun m => Nat.lcm d1 d2 ∣ F m)).card : ℝ) - gFunc P₀ (Nat.lcm d1 d2) * X)| :=
          le_abs_self _
      _ = |selbergLambda P₀ w R d1| * |selbergLambda P₀ w R d2| *
            |((I.filter (fun m => Nat.lcm d1 d2 ∣ F m)).card : ℝ) - gFunc P₀ (Nat.lcm d1 d2) * X| := by
          rw [abs_mul, abs_mul]
      _ ≤ 1 * 1 * (K_err * rho P₀ (Nat.lcm d1 d2)) := by
          have h12 : |selbergLambda P₀ w R d1| * |selbergLambda P₀ w R d2| ≤ 1 * 1 :=
            mul_le_mul hlam1 hlam2 (abs_nonneg _) zero_le_one
          exact mul_le_mul h12 hrem (abs_nonneg _) (by positivity)
      _ ≤ K_err * (rho P₀ d1 * rho P₀ d2) := by
          rw [one_mul, one_mul]
          exact mul_le_mul_of_nonneg_left hrho_lcm hK
  have hquad := selberg_quad_eq (P₀ := P₀) (w := w) (R := R) hP₀ hR
  have hsq_rho : ∑ d1 ∈ D, ∑ d2 ∈ D, rho P₀ d1 * rho P₀ d2 = (∑ d ∈ D, rho P₀ d) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  calc (S.card : ℝ)
      ≤ (∑ d1 ∈ D, ∑ d2 ∈ D,
          selbergLambda P₀ w R d1 * selbergLambda P₀ w R d2 * gFunc P₀ (Nat.lcm d1 d2)) * X +
        K_err * ∑ d1 ∈ D, ∑ d2 ∈ D, rho P₀ d1 * rho P₀ d2 := (hstep1.trans_eq hstep2).trans hstep3
    _ = 1 / GSum P₀ w R * X + K_err * (∑ d ∈ D, rho P₀ d) ^ 2 := by rw [hquad, hsq_rho]
    _ = X / GSum P₀ w R + K_err * (∑ d ∈ D, rho P₀ d) ^ 2 := by ring

/-- 5-Line Rankin Trick lower bound on `GSum P₀ w R * V7 P₀ w`! -/
theorem rankin_GSum_lower {P₀ w R : ℕ} (hP₀ : 100 ≤ P₀) (hR : 1 ≤ R) (α : ℝ) (hα : 0 < α) :
    1 - (R : ℝ) ^ (-α) * Real.exp
      (∑ p ∈ (Ioo P₀ w).filter Nat.Prime, (7 / ((p : ℝ) - 7)) * ((p : ℝ) ^ α - 1)) ≤
    GSum P₀ w R * Erdos946MertensAux.V7 P₀ w := by
  let Pset := (Ioo P₀ w).filter Nat.Prime
  let AllValid := Pset.powerset.image (fun S => ∏ p ∈ S, p)
  -- Step 1: ∏_{p ∈ Pset} (1 + h(p)) = (V7 P₀ w)⁻¹
  have hV_inv : ∏ p ∈ Pset, (1 + 7 / ((p : ℝ) - 7)) = (Erdos946MertensAux.V7 P₀ w)⁻¹ := by
    unfold Erdos946MertensAux.V7
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp100 : (100 : ℝ) < p := by exact_mod_cast lt_of_le_of_lt hP₀ (mem_Ioo.mp (mem_filter.mp hp).1).1
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp7 : (p : ℝ) - 7 ≠ 0 := by linarith
    field_simp; ring
  -- Step 2: ∑_{S ⊆ Pset} ∏_{p ∈ S} h(p) = ∏_{p ∈ Pset} (1 + h(p))
  have hsum_all : ∑ S ∈ Pset.powerset, ∏ p ∈ S, (7 / ((p : ℝ) - 7)) = (Erdos946MertensAux.V7 P₀ w)⁻¹ := by
    rw [← Finset.prod_one_add, hV_inv]
  -- Step 3: Split powerset into {S | ∏ S <= R} (which maps injectively into GSum!) and {S | R < ∏ S}
  let Good := Pset.powerset.filter (fun S => (∏ p ∈ S, p) ≤ R)
  let Bad := Pset.powerset.filter (fun S => R < ∏ p ∈ S, p)
  have hsplit :
      ∑ S ∈ Good, (∏ p ∈ S, (7 / ((p : ℝ) - 7))) + ∑ S ∈ Bad, (∏ p ∈ S, (7 / ((p : ℝ) - 7))) =
        (Erdos946MertensAux.V7 P₀ w)⁻¹ := by
    rw [← hsum_all]
    have hdisj : Disjoint Good Bad := by
      rw [Finset.disjoint_filter]
      intro S _ h1 h2; omega
    have hunion : Good ∪ Bad = Pset.powerset := by
      ext S; simp only [mem_union, mem_filter, Good, Bad]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h; by_cases hle : (∏ p ∈ S, p) ≤ R
        · exact Or.inl ⟨h, hle⟩
        · exact Or.inr ⟨h, by omega⟩
    rw [← Finset.sum_union hdisj, hunion]
  -- Step 4: ∑_{S ∈ Good} ∏ h(p) <= GSum P₀ w R (in fact equal!)
  have hgood_le : ∑ S ∈ Good, (∏ p ∈ S, (7 / ((p : ℝ) - 7))) ≤ GSum P₀ w R := by
    unfold GSum
    have hinj : Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) (Good : Set (Finset ℕ)) := by
      intro S1 hS1 S2 hS2 heq
      have h1sub : S1 ⊆ Pset := Finset.mem_powerset.mp (mem_filter.mp hS1).1
      have h2sub : S2 ⊆ Pset := Finset.mem_powerset.mp (mem_filter.mp hS2).1
      have hp1 : ∀ p ∈ S1, p.Prime := fun p hp => (mem_filter.mp (h1sub hp)).2
      have hp2 : ∀ p ∈ S2, p.Prime := fun p hp => (mem_filter.mp (h2sub hp)).2
      dsimp only at heq
      rw [← primeFactors_prod_primes hp1, ← primeFactors_prod_primes hp2, heq]
    have hsub : Good.image (fun S => ∏ p ∈ S, p) ⊆ (Icc 1 R).filter (fun r => ValidDiv P₀ w r) := by
      intro r hr
      obtain ⟨S, hS, rfl⟩ := mem_image.mp hr
      have hSsub : S ⊆ Pset := Finset.mem_powerset.mp (mem_filter.mp hS).1
      have hS_le : (∏ p ∈ S, p) ≤ R := (mem_filter.mp hS).2
      have hpS : ∀ p ∈ S, p.Prime := fun p hp => (mem_filter.mp (hSsub hp)).2
      have hpos : 0 < ∏ p ∈ S, p := Finset.prod_pos fun p hp => (hpS p hp).pos
      have hsf : Squarefree (∏ p ∈ S, p) := by
        clear hpos hr hS_le hS hSsub hinj
        induction S using Finset.induction_on with
        | empty => simp
        | insert p T hpT ih =>
          rw [Finset.prod_insert hpT]
          have hpp : p.Prime := hpS p (mem_insert_self p T)
          have hT : ∀ q ∈ T, q.Prime := fun q hq => hpS q (mem_insert_of_mem hq)
          have hcop : p.Coprime (∏ q ∈ T, q) :=
            Nat.Coprime.prod_right fun q hq =>
              (Nat.coprime_primes hpp (hT q hq)).mpr (fun heq => hpT (heq ▸ hq))
          exact (Nat.squarefree_mul hcop).mpr ⟨hpp.squarefree, ih hT⟩
      have hval : ValidDiv P₀ w (∏ p ∈ S, p) := by
        refine ⟨hpos, hsf, fun p hp => ?_⟩
        rw [primeFactors_prod_primes hpS] at hp
        exact mem_Ioo.mp (mem_filter.mp (hSsub hp)).1
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpos, hS_le⟩, hval⟩
    calc ∑ S ∈ Good, ∏ p ∈ S, (7 / ((p : ℝ) - 7))
        = ∑ S ∈ Good, hFunc P₀ (∏ p ∈ S, p) := by
          refine Finset.sum_congr rfl fun S hS => ?_
          have hSsub : S ⊆ Pset := Finset.mem_powerset.mp (mem_filter.mp hS).1
          have hpS : ∀ p ∈ S, p.Prime := fun p hp => (mem_filter.mp (hSsub hp)).2
          have hsf : Squarefree (∏ p ∈ S, p) := by
            clear hS hSsub
            induction S using Finset.induction_on with
            | empty => simp
            | insert p T hpT ih =>
              rw [Finset.prod_insert hpT]
              have hpp : p.Prime := hpS p (mem_insert_self p T)
              have hT : ∀ q ∈ T, q.Prime := fun q hq => hpS q (mem_insert_of_mem hq)
              have hcop : p.Coprime (∏ q ∈ T, q) :=
                Nat.Coprime.prod_right fun q hq =>
                  (Nat.coprime_primes hpp (hT q hq)).mpr (fun heq => hpT (heq ▸ hq))
              exact (Nat.squarefree_mul hcop).mpr ⟨hpp.squarefree, ih hT⟩
          unfold hFunc
          rw [if_pos ⟨hsf, fun p hp => by
            rw [primeFactors_prod_primes hpS] at hp
            exact (mem_Ioo.mp (mem_filter.mp (hSsub hp)).1).1⟩,
            primeFactors_prod_primes hpS]
      _ = ∑ r ∈ Good.image (fun S => ∏ p ∈ S, p), hFunc P₀ r := (Finset.sum_image hinj).symm
      _ ≤ ∑ r ∈ (Icc 1 R).filter (fun r => ValidDiv P₀ w r), hFunc P₀ r :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => hFunc_nonneg hP₀
  -- Step 5: Rankin trick on Bad!
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hbad_le :
      ∑ S ∈ Bad, (∏ p ∈ S, (7 / ((p : ℝ) - 7))) ≤
        (R : ℝ) ^ (-α) * (Erdos946MertensAux.V7 P₀ w)⁻¹ *
          Real.exp (∑ p ∈ Pset, (7 / ((p : ℝ) - 7)) * ((p : ℝ) ^ α - 1)) := by
    calc ∑ S ∈ Bad, (∏ p ∈ S, (7 / ((p : ℝ) - 7)))
        ≤ ∑ S ∈ Bad, (R : ℝ) ^ (-α) * ((∏ p ∈ S, p : ℕ) : ℝ) ^ α * (∏ p ∈ S, (7 / ((p : ℝ) - 7))) := by
          refine Finset.sum_le_sum fun S hS => ?_
          have hSsub : S ⊆ Pset := Finset.mem_powerset.mp (mem_filter.mp hS).1
          have hgt : (R : ℝ) < ((∏ p ∈ S, p : ℕ) : ℝ) := by exact_mod_cast (mem_filter.mp hS).2
          have h1le : 1 ≤ (R : ℝ) ^ (-α) * ((∏ p ∈ S, p : ℕ) : ℝ) ^ α := by
            rw [Real.rpow_neg hRpos.le, inv_mul_eq_div, one_le_div (Real.rpow_pos_of_pos hRpos α)]
            exact Real.rpow_le_rpow hRpos.le hgt.le hα.le
          have hprod_nn : 0 ≤ ∏ p ∈ S, (7 / ((p : ℝ) - 7)) := Finset.prod_nonneg fun p hp => by
            have hp100 : (100 : ℝ) < p := by exact_mod_cast lt_of_le_of_lt hP₀ (mem_Ioo.mp (mem_filter.mp (hSsub hp)).1).1
            exact div_nonneg (by norm_num) (by linarith)
          simpa using mul_le_mul_of_nonneg_right h1le hprod_nn
      _ ≤ ∑ S ∈ Pset.powerset, (R : ℝ) ^ (-α) * ((∏ p ∈ S, p : ℕ) : ℝ) ^ α * (∏ p ∈ S, (7 / ((p : ℝ) - 7))) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun S hS _ => by
            have hSsub : S ⊆ Pset := Finset.mem_powerset.mp hS
            have hprod_nn : 0 ≤ ∏ p ∈ S, (7 / ((p : ℝ) - 7)) := Finset.prod_nonneg fun p hp => by
              have hp100 : (100 : ℝ) < p := by exact_mod_cast lt_of_le_of_lt hP₀ (mem_Ioo.mp (mem_filter.mp (hSsub hp)).1).1
              exact div_nonneg (by norm_num) (by linarith)
            positivity
      _ = (R : ℝ) ^ (-α) * ∏ p ∈ Pset, (1 + (7 / ((p : ℝ) - 7)) * (p : ℝ) ^ α) := by
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum, Finset.prod_one_add]
          congr 1
          refine Finset.sum_congr rfl fun S hS => ?_
          rw [Nat.cast_prod, ← Real.finsetProd_rpow S (fun p => (p : ℝ)) (fun p _ => Nat.cast_nonneg p),
              ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun p _ => by ring
      _ = (R : ℝ) ^ (-α) * (Erdos946MertensAux.V7 P₀ w)⁻¹ *
            ∏ p ∈ Pset, ((1 + (7 / ((p : ℝ) - 7)) * (p : ℝ) ^ α) / (1 + 7 / ((p : ℝ) - 7))) := by
          rw [← hV_inv, mul_assoc]
          congr 1
          rw [Finset.prod_div_distrib, mul_div_cancel₀]
          exact (Finset.prod_pos fun p hp => by
            have hp100 : (100 : ℝ) < p := by exact_mod_cast lt_of_le_of_lt hP₀ (mem_Ioo.mp (mem_filter.mp hp).1).1
            have : 0 < 7 / ((p : ℝ) - 7) := div_pos (by norm_num) (by linarith)
            linarith).ne'
      _ ≤ (R : ℝ) ^ (-α) * (Erdos946MertensAux.V7 P₀ w)⁻¹ *
            Real.exp (∑ p ∈ Pset, (7 / ((p : ℝ) - 7)) * ((p : ℝ) ^ α - 1)) := by
          have hVpos := Erdos946MertensAux.V7_pos (w := w) hP₀
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [Real.exp_sum]
          refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
          · have hp100 : (100 : ℝ) < p := by exact_mod_cast lt_of_le_of_lt hP₀ (mem_Ioo.mp (mem_filter.mp hp).1).1
            have hhp : 0 < 7 / ((p : ℝ) - 7) := div_pos (by norm_num) (by linarith)
            have h1 : 0 ≤ (7 / ((p : ℝ) - 7)) * (p : ℝ) ^ α := mul_nonneg hhp.le (Real.rpow_nonneg (by linarith) _)
            have h2 : 0 < 1 + 7 / ((p : ℝ) - 7) := by linarith
            exact div_nonneg (by linarith) h2.le
          · have hp100 : (100 : ℝ) < p := by exact_mod_cast lt_of_le_of_lt hP₀ (mem_Ioo.mp (mem_filter.mp hp).1).1
            have hhp : 0 < 7 / ((p : ℝ) - 7) := div_pos (by norm_num) (by linarith)
            have hden : 1 ≤ 1 + 7 / ((p : ℝ) - 7) := by linarith
            have hp1 : (1 : ℝ) ≤ (p : ℝ) ^ α := Real.one_le_rpow (by linarith) hα.le
            have hfrac : (1 + (7 / ((p : ℝ) - 7)) * (p : ℝ) ^ α) / (1 + 7 / ((p : ℝ) - 7)) ≤
                1 + (7 / ((p : ℝ) - 7)) * ((p : ℝ) ^ α - 1) := by
              rw [div_le_iff₀ (by linarith)]
              nlinarith [mul_nonneg hhp.le (sub_nonneg.mpr hp1)]
            exact hfrac.trans (by linarith [Real.add_one_le_exp ((7 / ((p : ℝ) - 7)) * ((p : ℝ) ^ α - 1))])
  -- Multiply by V7 P₀ w > 0!
  have hVpos := Erdos946MertensAux.V7_pos (w := w) hP₀
  have hG_ge : (Erdos946MertensAux.V7 P₀ w)⁻¹ -
      (R : ℝ) ^ (-α) * (Erdos946MertensAux.V7 P₀ w)⁻¹ *
        Real.exp (∑ p ∈ Pset, (7 / ((p : ℝ) - 7)) * ((p : ℝ) ^ α - 1)) ≤ GSum P₀ w R := by
    linarith
  have hmul := mul_le_mul_of_nonneg_right hG_ge hVpos.le
  have hsimp : ((Erdos946MertensAux.V7 P₀ w)⁻¹ -
      (R : ℝ) ^ (-α) * (Erdos946MertensAux.V7 P₀ w)⁻¹ *
        Real.exp (∑ p ∈ Pset, (7 / ((p : ℝ) - 7)) * ((p : ℝ) ^ α - 1))) *
      Erdos946MertensAux.V7 P₀ w =
    1 - (R : ℝ) ^ (-α) * Real.exp (∑ p ∈ Pset, (7 / ((p : ℝ) - 7)) * ((p : ℝ) ^ α - 1)) := by
    have hV0 := hVpos.ne'
    field_simp
  linarith

/-- Elementary upper bound on the Selberg error sum:
`∑_{d <= R, valid} ρ(d) <= R * ∏_{P₀ < p <= R} (1 + 7/p)`. -/
lemma sum_rho_le_mul_prod {P₀ w R : ℕ} (_hP₀ : 100 ≤ P₀) :
    ∑ d ∈ (Icc 1 R).filter (fun d => ValidDiv P₀ w d), rho P₀ d ≤
      (R : ℝ) * ∏ p ∈ (Ioc P₀ R).filter Nat.Prime, (1 + 7 / (p : ℝ)) := by
  let D := (Icc 1 R).filter (fun d => ValidDiv P₀ w d)
  let Pset := (Ioc P₀ R).filter Nat.Prime
  calc ∑ d ∈ D, rho P₀ d
      ≤ ∑ d ∈ D, (R : ℝ) * (rho P₀ d / (d : ℝ)) := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hd1 := (mem_Icc.mp (mem_filter.mp hd).1).1
        have hdR : (d : ℝ) ≤ R := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hd).1).2
        have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
        have hdv := (mem_filter.mp hd).2
        have hrnn : 0 ≤ rho P₀ d := by
          unfold rho; split_ifs <;> positivity
        rw [mul_div_assoc', le_div_iff₀ hd0, mul_comm (R : ℝ)]
        exact mul_le_mul_of_nonneg_left hdR hrnn
    _ = (R : ℝ) * ∑ d ∈ D, rho P₀ d / (d : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ (R : ℝ) * ∏ p ∈ Pset, (1 + 7 / (p : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg R)
        rw [Finset.prod_one_add]
        have hinj : Set.InjOn (fun d : ℕ => d.primeFactors) (D : Set ℕ) := by
          intro d1 hd1 d2 hd2 heq
          dsimp only at heq
          have hs1 := (mem_filter.mp hd1).2.2.1
          have hs2 := (mem_filter.mp hd2).2.2.1
          rw [← Nat.prod_primeFactors_of_squarefree hs1, ← Nat.prod_primeFactors_of_squarefree hs2, heq]
        have hsub : D.image (fun d => d.primeFactors) ⊆ Pset.powerset := by
          intro S hS
          obtain ⟨d, hd, rfl⟩ := mem_image.mp hS
          rw [Finset.mem_powerset]
          intro p hp
          have hdv := (mem_filter.mp hd).2
          have hdR := (mem_Icc.mp (mem_filter.mp hd).1).2
          have hp_le : p ≤ R := (Nat.le_of_dvd hdv.1 (Nat.dvd_of_mem_primeFactors hp)).trans hdR
          exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(hdv.2.2 p hp).1, hp_le⟩, Nat.prime_of_mem_primeFactors hp⟩
        calc ∑ d ∈ D, rho P₀ d / (d : ℝ)
            = ∑ d ∈ D, ∏ p ∈ d.primeFactors, (7 / (p : ℝ)) := by
              refine Finset.sum_congr rfl fun d hd => ?_
              have hdv := (mem_filter.mp hd).2
              unfold rho
              rw [if_pos ⟨hdv.2.1, fun p hp => (hdv.2.2 p hp).1⟩]
              have hd_eq : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
                conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hdv.2.1]
                push_cast; rfl
              rw [hd_eq, Finset.prod_div_distrib, Finset.prod_const]
          _ = ∑ S ∈ D.image (fun d : ℕ => d.primeFactors), ∏ p ∈ S, (7 / (p : ℝ)) :=
              (Finset.sum_image (f := fun S : Finset ℕ => ∏ p ∈ S, (7 / (p : ℝ))) hinj).symm
          _ ≤ ∑ S ∈ Pset.powerset, ∏ p ∈ S, (7 / (p : ℝ)) :=
              Finset.sum_le_sum_of_subset_of_nonneg (f := fun S : Finset ℕ => ∏ p ∈ S, (7 / (p : ℝ))) hsub fun S _ _ =>
                Finset.prod_nonneg fun p _ => by positivity

end Erdos946Selberg
end

section
open Finset Filter Real
open scoped BigOperators Classical

namespace Erdos946Sieve1

open Erdos946MertensAux Erdos946Selberg

/-- Simultaneous CRT over a finite set of distinct primes. -/
lemma exists_crt_primes (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (t : ℕ → ℕ) :
    ∃ n₀ : ℕ, ∀ p ∈ P, n₀ ≡ t p [MOD p] := by
  induction P using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert p T hpT ih =>
    have hpp : p.Prime := hP p (mem_insert_self p T)
    have hT : ∀ q ∈ T, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    obtain ⟨nT, hnT⟩ := ih hT
    set M := ∏ q ∈ T, q
    have hcop : p.Coprime M :=
      Nat.Coprime.prod_right fun q hq =>
        (Nat.coprime_primes hpp (hT q hq)).mpr (fun h => hpT (h ▸ hq))
    let c := Nat.chineseRemainder hcop (t p) nT
    refine ⟨c.val, fun q hq => ?_⟩
    rw [mem_insert] at hq
    rcases hq with rfl | hqT
    · exact c.property.1
    · have hqM : q ∣ M := Finset.dvd_prod_of_mem _ hqT
      exact (c.property.2.of_dvd hqM).trans (hnT q hqT)

/-- Exact count of integers in `Icc 1 X` congruent to `r` mod `d` is within `1` of `X / d`. -/
lemma card_mod_Icc_bound (X d r : ℕ) (hd : 0 < d) (hr : r < d) :
    |(((Icc 1 X).filter (fun m => m % d = r)).card : ℝ) - (X : ℝ) / (d : ℝ)| ≤ 1 := by
  -- Show X / d ≤ card ≤ X / d + 1? Careful: for r = 0, multiples of d in [1, X] has card = X / d;
  -- for 1 <= r < d, card = (X + d - r) / d, which is X / d or X / d + 1!
  -- Actually in ALL cases: X / d ≤ card ∧ card ≤ X / d + 1 (Wait: if r > X % d, card = X / d; if 1 <= r <= X % d, card = X / d + 1; if r = 0, card = X / d!).
  -- Let's prove: X / d ≤ card ∧ card ≤ X / d + 1!
  set S := (Icc 1 X).filter (fun m => m % d = r)
  have hlo : X / d ≤ S.card := by
    by_cases hr0 : r = 0
    · subst hr0
      -- Map k ∈ Icc 1 (X / d) to k * d ∈ S
      have hinj : Set.InjOn (fun k : ℕ => k * d) ↑(Icc 1 (X / d)) := by
        intro a _ b _ heq; exact Nat.eq_of_mul_eq_mul_right hd heq
      have hsub : (Icc 1 (X / d)).image (fun k => k * d) ⊆ S := by
        intro m hm
        obtain ⟨k, hk, rfl⟩ := mem_image.mp hm
        have hk1 := (mem_Icc.mp hk).1
        have hk2 := (mem_Icc.mp hk).2
        refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hk1 hd, ?_⟩, Nat.mul_mod_left k d⟩
        exact (Nat.mul_le_mul_right d hk2).trans (Nat.div_mul_le_self X d)
      calc X / d = (Icc 1 (X / d)).card := by simp
        _ = ((Icc 1 (X / d)).image (fun k => k * d)).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ S.card := Finset.card_le_card hsub
    · -- 1 <= r < d: map k ∈ range (X / d) to k * d + r ∈ S!
      have hinj : Set.InjOn (fun k : ℕ => k * d + r) ↑(range (X / d)) := by
        intro a _ b _ heq
        exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_right_cancel heq)
      have hsub : (range (X / d)).image (fun k => k * d + r) ⊆ S := by
        intro m hm
        obtain ⟨k, hk, rfl⟩ := mem_image.mp hm
        have hk2 : k < X / d := mem_range.mp hk
        have hle : k * d + r ≤ X := by
          have h1 : (k + 1) * d ≤ (X / d) * d := Nat.mul_le_mul_right d hk2
          have h2 : (X / d) * d ≤ X := Nat.div_mul_le_self X d
          nlinarith
        refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hle⟩, ?_⟩
        rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hr]
      calc X / d = (range (X / d)).card := by simp
        _ = ((range (X / d)).image (fun k => k * d + r)).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ S.card := Finset.card_le_card hsub
  have hhi : S.card ≤ X / d + 1 := by
    -- Map m ∈ S injectively to m / d ∈ range (X / d + 1)
    have hinj : Set.InjOn (fun m : ℕ => m / d) ↑S := by
      intro m1 hm1 m2 hm2 heq
      dsimp only at heq
      have h1 := (mem_filter.mp hm1).2
      have h2 := (mem_filter.mp hm2).2
      have hd1 := Nat.div_add_mod m1 d
      have hd2 := Nat.div_add_mod m2 d
      rw [heq] at hd1
      omega
    have hsub : S.image (fun m => m / d) ⊆ range (X / d + 1) := by
      intro q hq
      obtain ⟨m, hm, rfl⟩ := mem_image.mp hq
      have hmX := (mem_Icc.mp (mem_filter.mp hm).1).2
      exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hmX))
    calc S.card = (S.image (fun m => m / d)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (range (X / d + 1)).card := Finset.card_le_card hsub
      _ = X / d + 1 := by simp
  -- Since (X / d : ℝ) <= X / d (in ℝ) < (X / d : ℝ) + 1:
  have hdiv_le : ((X / d : ℕ) : ℝ) ≤ (X : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ (by exact_mod_cast hd)]
    exact_mod_cast Nat.div_mul_le_self X d
  have hdiv_lt : (X : ℝ) / (d : ℝ) < ((X / d : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ (by exact_mod_cast hd)]
    have hlt : X < (X / d + 1) * d := by
      have := Nat.div_add_mod X d
      have := Nat.mod_lt X hd
      nlinarith
    have hlt' : (X : ℝ) < (((X / d + 1) * d : ℕ) : ℝ) := by exact_mod_cast hlt
    push_cast at hlt'
    linarith
  have hlo' : ((X / d : ℕ) : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hlo
  have hhi' : (S.card : ℝ) ≤ ((X / d : ℕ) : ℝ) + 1 := by exact_mod_cast hhi
  rw [abs_le]
  constructor <;> linarith

/-- Setup structure for 7 shifted admissible linear forms `L i m = s i * (M₀ * m + n₀) + c i`. -/
structure ShiftedForms where
  s : Fin 7 → ℕ
  c : Fin 7 → ℕ
  P₀ : ℕ
  hP₀ : 100 ≤ P₀
  M₀ : ℕ
  hM₀_pos : 0 < M₀
  n₀ : ℕ
  L : Fin 7 → ℕ → ℕ
  F : ℕ → ℕ
  hL_def : ∀ i m, L i m = s i * (M₀ * m + n₀) + c i
  hF_def : ∀ m, F m = ∏ i : Fin 7, L i m
  hs_pos : ∀ i, 0 < s i
  hF_pos : ∀ m, 1 ≤ m → 0 < F m
  hL_gt1 : ∀ i m, 1 ≤ m → 1 < L i m
  hsmall : ∀ p : ℕ, p.Prime → p ≤ P₀ → ∀ m : ℕ, ¬ p ∣ F m
  hcop_forms : ∀ p : ℕ, p.Prime → P₀ < p → ∀ m : ℕ, ∀ i j : Fin 7, i ≠ j → ¬ (p ∣ L i m ∧ p ∣ L j m)
  hroots_prime : ∀ p : ℕ, p.Prime → P₀ < p →
    ((range p).filter (fun r => p ∣ F r)).card = 7

/-- Construct `ShiftedForms` from any admissible 7-tuple `(s, c)`. -/
lemma build_shifted_forms (s c : Fin 7 → ℕ) (hs : ∀ i, 0 < s i)
    (hdistinct : ∀ i j, i ≠ j → s i * c j ≠ s j * c i)
    (hadm : ∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬ p ∣ s i * t + c i) :
    Nonempty (ShiftedForms) ∧
      ∃ sf : ShiftedForms, sf.s = s ∧ sf.c = c := by
  let Smax := Finset.univ.sup s
  let Cmax := Finset.univ.sup c
  let Dmax := Finset.univ.sup (fun ij : Fin 7 × Fin 7 => s ij.1 * c ij.2 + s ij.2 * c ij.1)
  let P₀ := max 100 (max Smax (max Cmax Dmax))
  have hP₀ : 100 ≤ P₀ := le_max_left _ _
  have hS_le : ∀ i, s i ≤ P₀ := fun i =>
    (Finset.le_sup (f := s) (mem_univ i)).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hC_le : ∀ i, c i ≤ P₀ := fun i =>
    (Finset.le_sup (f := c) (mem_univ i)).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hD_le : ∀ i j, s i * c j + s j * c i ≤ P₀ := fun i j =>
    (Finset.le_sup (f := fun ij : Fin 7 × Fin 7 => s ij.1 * c ij.2 + s ij.2 * c ij.1) (mem_univ (i, j))).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  let Psmall := (Icc 1 P₀).filter Nat.Prime
  let M₀ := ∏ p ∈ Psmall, p
  have hM₀_pos : 0 < M₀ := Finset.prod_pos fun p hp => (mem_filter.mp hp).2.pos
  have hM₀_ge2 : 2 ≤ M₀ := by
    have h2mem : 2 ∈ Psmall := mem_filter.mpr ⟨mem_Icc.mpr ⟨by norm_num, by omega⟩, Nat.prime_two⟩
    exact Nat.le_of_dvd hM₀_pos (Finset.dvd_prod_of_mem _ h2mem)
  -- Pick t_p for each prime p <= P₀
  let t : ℕ → ℕ := fun p => if hp : p.Prime then Classical.choose (hadm p hp) else 0
  have ht : ∀ p ∈ Psmall, ∀ i, ¬ p ∣ s i * t p + c i := by
    intro p hp i
    have hpr := (mem_filter.mp hp).2
    dsimp [t]; rw [dif_pos hpr]
    exact Classical.choose_spec (hadm p hpr) i
  obtain ⟨n₀, hn₀⟩ := exists_crt_primes Psmall (fun p hp => (mem_filter.mp hp).2) t
  let L : Fin 7 → ℕ → ℕ := fun i m => s i * (M₀ * m + n₀) + c i
  let F : ℕ → ℕ := fun m => ∏ i : Fin 7, L i m
  have hL_gt1 : ∀ i m, 1 ≤ m → 1 < L i m := by
    intro i m hm
    dsimp [L]
    have hsi := hs i
    have hm2 : 2 ≤ M₀ * m := by nlinarith
    have hsm2 : 2 ≤ s i * (M₀ * m + n₀) := by nlinarith
    omega
  have hF_pos : ∀ m, 1 ≤ m → 0 < F m := fun m hm =>
    Finset.prod_pos fun i _ => lt_trans zero_lt_one (hL_gt1 i m hm)
  have hsmall : ∀ p : ℕ, p.Prime → p ≤ P₀ → ∀ m : ℕ, ¬ p ∣ F m := by
    intro p hp hpP m hdvd
    have hpmem : p ∈ Psmall := mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.pos, hpP⟩, hp⟩
    have hpM : p ∣ M₀ := Finset.dvd_prod_of_mem _ hpmem
    obtain ⟨i, _, hi⟩ := hp.prime.dvd_finsetProd_iff _ |>.mp hdvd
    have hcong : L i m ≡ s i * t p + c i [MOD p] := by
      dsimp [L]
      have hm0 : M₀ * m ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hpM m)
      have h1 : M₀ * m + n₀ ≡ 0 + t p [MOD p] := hm0.add (hn₀ p hpmem)
      rw [zero_add] at h1
      exact (h1.mul_left (s i)).add_right (c i)
    have hdiv_t : p ∣ s i * t p + c i :=
      Nat.modEq_zero_iff_dvd.mp (hcong.symm.trans (Nat.modEq_zero_iff_dvd.mpr hi))
    exact ht p hpmem i hdiv_t
  have hcop_forms : ∀ p : ℕ, p.Prime → P₀ < p → ∀ m : ℕ, ∀ i j : Fin 7, i ≠ j → ¬ (p ∣ L i m ∧ p ∣ L j m) := by
    intro p hp hpP m i j hij ⟨hi, hj⟩
    have hne := hdistinct i j hij
    -- p | s j * L i m - s i * L j m = s j * c i - s i * c j (in ℤ)
    have h1 : (p : ℤ) ∣ (s j : ℤ) * (L i m : ℤ) := by exact_mod_cast dvd_mul_of_dvd_right hi (s j)
    have h2 : (p : ℤ) ∣ (s i : ℤ) * (L j m : ℤ) := by exact_mod_cast dvd_mul_of_dvd_right hj (s i)
    have hsub : (p : ℤ) ∣ (s j : ℤ) * (L i m : ℤ) - (s i : ℤ) * (L j m : ℤ) := dvd_sub h1 h2
    have heq : (s j : ℤ) * (L i m : ℤ) - (s i : ℤ) * (L j m : ℤ) = (s j : ℤ) * (c i : ℤ) - (s i : ℤ) * (c j : ℤ) := by
      dsimp [L]; push_cast; ring
    rw [heq] at hsub
    have hneZ : (s j : ℤ) * (c i : ℤ) - (s i : ℤ) * (c j : ℤ) ≠ 0 := by
      intro h0
      apply hne
      have : (s i : ℤ) * (c j : ℤ) = (s j : ℤ) * (c i : ℤ) := by linarith
      exact_mod_cast this
    have hsub_abs : (p : ℤ) ∣ |(s j : ℤ) * (c i : ℤ) - (s i : ℤ) * (c j : ℤ)| := by
      rcases abs_choice ((s j : ℤ) * (c i : ℤ) - (s i : ℤ) * (c j : ℤ)) with h | h <;> rw [h]
      · exact hsub
      · exact dvd_neg.mpr hsub
    have hle := Int.le_of_dvd (abs_pos.mpr hneZ) hsub_abs
    have habs_le : |(s j : ℤ) * (c i : ℤ) - (s i : ℤ) * (c j : ℤ)| ≤ (P₀ : ℤ) := by
      have hD : (s i * c j + s j * c i : ℤ) ≤ P₀ := by exact_mod_cast hD_le i j
      rw [abs_le]
      constructor <;> nlinarith [Nat.zero_le (s i * c j), Nat.zero_le (s j * c i)]
    have : (p : ℤ) ≤ P₀ := hle.trans habs_le
    omega
  have hroots_prime : ∀ p : ℕ, p.Prime → P₀ < p → ((range p).filter (fun r => p ∣ F r)).card = 7 := by
    intro p hp hpP
    have : Fact p.Prime := ⟨hp⟩
    have hM₀_cop : ¬ p ∣ M₀ := by
      intro hdvd
      obtain ⟨q, hq, hqp⟩ := hp.prime.dvd_finsetProd_iff _ |>.mp hdvd
      have hqpr := (mem_filter.mp hq).2
      have hqP := (mem_Icc.mp (mem_filter.mp hq).1).2
      have heq := (Nat.prime_dvd_prime_iff_eq hp hqpr).mp hqp
      omega
    have hcoef_ne : ∀ i : Fin 7, ((s i * M₀ : ℕ) : ZMod p) ≠ 0 := by
      intro i h0
      have hdvd : p ∣ s i * M₀ := (ZMod.natCast_eq_zero_iff _ _).mp h0
      rcases hp.dvd_mul.mp hdvd with hsi | hM
      · have := Nat.le_of_dvd (hs i) hsi
        have := hS_le i
        omega
      · exact hM₀_cop hM
    let root : Fin 7 → ℕ := fun i =>
      (-(((s i * n₀ + c i : ℕ) : ZMod p)) * (((s i * M₀ : ℕ) : ZMod p))⁻¹).val
    have hroot_lt : ∀ i, root i < p := fun i => ZMod.val_lt _
    have hroot_iff : ∀ i r, r < p → (p ∣ L i r ↔ r = root i) := by
      intro i r hr
      rw [← ZMod.natCast_eq_zero_iff]
      have hLcast : (L i r : ZMod p) = ((s i * M₀ : ℕ) : ZMod p) * (r : ZMod p) + ((s i * n₀ + c i : ℕ) : ZMod p) := by
        dsimp [L]; push_cast; ring
      rw [hLcast]
      have hc0 := hcoef_ne i
      constructor
      · intro h0
        have hrZ : (r : ZMod p) = -(((s i * n₀ + c i : ℕ) : ZMod p)) * (((s i * M₀ : ℕ) : ZMod p))⁻¹ := by
          have : ((s i * M₀ : ℕ) : ZMod p) * (r : ZMod p) = -((s i * n₀ + c i : ℕ) : ZMod p) := eq_neg_of_add_eq_zero_left h0
          calc (r : ZMod p) = ((s i * M₀ : ℕ) : ZMod p) * (r : ZMod p) * (((s i * M₀ : ℕ) : ZMod p))⁻¹ := by
                rw [mul_comm (((s i * M₀ : ℕ) : ZMod p)), mul_assoc, mul_inv_cancel₀ hc0, mul_one]
            _ = _ := by rw [this]
        have := congrArg ZMod.val hrZ
        rwa [ZMod.val_natCast_of_lt hr] at this
      · intro heq
        subst heq
        dsimp [root]
        rw [ZMod.natCast_zmod_val, mul_comm (((s i * M₀ : ℕ) : ZMod p)), mul_assoc,
            inv_mul_cancel₀ hc0, mul_one, neg_add_cancel]
    have hroot_inj : Function.Injective root := by
      intro i j heq
      by_contra hij
      have hi : p ∣ L i (root i) := (hroot_iff i (root i) (hroot_lt i)).mpr rfl
      have hj : p ∣ L j (root i) := (hroot_iff j (root i) (hroot_lt i)).mpr heq
      exact hcop_forms p hp hpP (root i) i j hij ⟨hi, hj⟩
    have hset_eq : (range p).filter (fun r => p ∣ F r) = Finset.univ.image root := by
      ext r
      simp only [mem_filter, mem_range, mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨hr, hdvd⟩
        obtain ⟨i, _, hi⟩ := hp.prime.dvd_finsetProd_iff _ |>.mp hdvd
        exact ⟨i, ((hroot_iff i r hr).mp hi).symm⟩
      · rintro ⟨i, rfl⟩
        refine ⟨hroot_lt i, Finset.dvd_prod_of_mem (fun j => L j (root i)) (mem_univ i) |> dvd_trans ?_⟩
        exact (hroot_iff i (root i) (hroot_lt i)).mpr rfl
    rw [hset_eq, Finset.card_image_of_injective _ hroot_inj, Finset.card_univ, Fintype.card_fin]
  let sf : ShiftedForms :=
    { s := s, c := c, P₀ := P₀, hP₀ := hP₀, M₀ := M₀, hM₀_pos := hM₀_pos, n₀ := n₀,
      L := L, F := F, hL_def := fun _ _ => rfl, hF_def := fun _ => rfl, hs_pos := hs,
      hF_pos := hF_pos, hL_gt1 := hL_gt1, hsmall := hsmall, hcop_forms := hcop_forms,
      hroots_prime := hroots_prime }
  exact ⟨⟨sf⟩, sf, rfl, rfl⟩

/-- Divisibility of `sf.F m` depends only on `m % d`. -/
lemma F_dvd_mod_iff (sf : ShiftedForms) {d m : ℕ} (_hd : 0 < d) :
    d ∣ sf.F m ↔ d ∣ sf.F (m % d) := by
  have hmod : m ≡ m % d [MOD d] := (Nat.mod_modEq m d).symm
  have hFmod : sf.F m ≡ sf.F (m % d) [MOD d] := by
    rw [sf.hF_def, sf.hF_def]
    -- Product of congruent terms
    have hL : ∀ i : Fin 7, sf.L i m ≡ sf.L i (m % d) [MOD d] := fun i => by
      rw [sf.hL_def, sf.hL_def]
      exact (((hmod.mul_left sf.M₀).add_right sf.n₀).mul_left (sf.s i)).add_right (sf.c i)
    -- Induction on Finset.univ
    have hprod : ∀ S : Finset (Fin 7), (∏ i ∈ S, sf.L i m) ≡ (∏ i ∈ S, sf.L i (m % d)) [MOD d] := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp [Nat.ModEq.refl]
      | insert a T haT ih =>
        rw [Finset.prod_insert haT, Finset.prod_insert haT]
        exact (hL a).mul ih
    exact hprod Finset.univ
  exact ⟨fun h => Nat.modEq_zero_iff_dvd.mp (hFmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr h)),
         fun h => Nat.modEq_zero_iff_dvd.mp (hFmod.trans (Nat.modEq_zero_iff_dvd.mpr h))⟩

/-- Exact root count modulo any squarefree `d` with all prime factors `> sf.P₀` is `7 ^ d.primeFactors.card`! -/
lemma card_roots_squarefree (sf : ShiftedForms) {d : ℕ}
    (hd0 : 0 < d) (hsf : Squarefree d) (hgt : ∀ p ∈ d.primeFactors, sf.P₀ < p) :
    ((range d).filter (fun r => d ∣ sf.F r)).card = 7 ^ d.primeFactors.card := by
  -- Induction on d.primeFactors.card (or strong induction on d)
  induction hd_card : d.primeFactors.card generalizing d with
  | zero =>
    have hd1 : d = 1 := by
      by_contra hne
      have hne' := Nat.nonempty_primeFactors.mpr (by omega : 1 < d)
      have := Finset.card_pos.mpr hne'
      omega
    subst hd1
    simp
  | succ k ih =>
    have hne : d.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p, hp⟩ := hne
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
    have hpP : sf.P₀ < p := hgt p hp
    set q := d / p
    have hmul : p * q = d := Nat.mul_div_cancel' hpd
    have hq0 : 0 < q := Nat.div_pos (Nat.le_of_dvd hd0 hpd) hpr.pos
    have hqsf : Squarefree q := hsf.squarefree_of_dvd (Nat.div_dvd_of_dvd hpd)
    have hcop : p.Coprime q := by
      refine Nat.coprime_of_dvd fun l hl hlp hlq => ?_
      have : l * l ∣ d := by rw [← hmul]; exact mul_dvd_mul hlp hlq
      exact (Nat.squarefree_iff_prime_squarefree.mp hsf l hl) this
    have hqgt : ∀ l ∈ q.primeFactors, sf.P₀ < l := fun l hl =>
      hgt l (Nat.primeFactors_mono (Nat.div_dvd_of_dvd hpd) hd0.ne' hl)
    have hpf_eq : d.primeFactors = insert p q.primeFactors := by
      rw [← hmul, Nat.primeFactors_mul hpr.ne_zero hq0.ne', hpr.primeFactors]
      ext l; simp
    have hp_not_q : p ∉ q.primeFactors := by
      intro hmem
      have : p ∣ q := Nat.dvd_of_mem_primeFactors hmem
      exact hpr.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd (dvd_refl p) this)
    have hqcard : q.primeFactors.card = k := by
      rw [hpf_eq, Finset.card_insert_of_notMem hp_not_q] at hd_card
      omega
    have ihq := ih hq0 hqsf hqgt hqcard
    have ihp := sf.hroots_prime p hpr hpP
    -- Biject roots mod d = p * q with (roots mod p) ×ˢ (roots mod q) via r ↦ (r % p, r % q)!
    set Rd := (range d).filter (fun r => d ∣ sf.F r)
    set Rp := (range p).filter (fun r => p ∣ sf.F r)
    set Rq := (range q).filter (fun r => q ∣ sf.F r)
    have hbij : Rd.card = (Rp ×ˢ Rq).card := by
      refine Finset.card_bij (fun r _ => (r % p, r % q)) ?_ ?_ ?_
      · intro r hr
        have hdr := (mem_filter.mp hr).2
        have hpr' : p ∣ sf.F (r % p) := (F_dvd_mod_iff sf hpr.pos).mp (hpd.trans hdr)
        have hqr' : q ∣ sf.F (r % q) := (F_dvd_mod_iff sf hq0).mp ((Nat.div_dvd_of_dvd hpd).trans hdr)
        exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt r hpr.pos), hpr'⟩,
          mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt r hq0), hqr'⟩⟩
      · intro r1 hr1 r2 hr2 heq
        have h1lt : r1 < p * q := hmul ▸ mem_range.mp (mem_filter.mp hr1).1
        have h2lt : r2 < p * q := hmul ▸ mem_range.mp (mem_filter.mp hr2).1
        have hp_eq : r1 ≡ r2 [MOD p] := congrArg Prod.fst heq
        have hq_eq : r1 ≡ r2 [MOD q] := congrArg Prod.snd heq
        have hpq_eq : r1 ≡ r2 [MOD p * q] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hp_eq, hq_eq⟩
        change r1 % (p * q) = r2 % (p * q) at hpq_eq
        rwa [Nat.mod_eq_of_lt h1lt, Nat.mod_eq_of_lt h2lt] at hpq_eq
      · intro ⟨a, b⟩ hab
        obtain ⟨ha, hb⟩ := mem_product.mp hab
        let c := Nat.chineseRemainder hcop a b
        have hc_lt : c.val < d := by rw [← hmul]; exact Nat.chineseRemainder_lt_mul hcop a b hpr.ne_zero hq0.ne'
        have hca : c.val % p = a := by
          have := c.property.1; change c.val % p = a % p at this
          rwa [Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp ha).1)] at this
        have hcb : c.val % q = b := by
          have := c.property.2; change c.val % q = b % q at this
          rwa [Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hb).1)] at this
        have hpc : p ∣ sf.F c.val := (F_dvd_mod_iff sf hpr.pos).mpr (by rw [hca]; exact (mem_filter.mp ha).2)
        have hqc : q ∣ sf.F c.val := (F_dvd_mod_iff sf hq0).mpr (by rw [hcb]; exact (mem_filter.mp hb).2)
        have hdc : d ∣ sf.F c.val := hmul ▸ hcop.mul_dvd_of_dvd_of_dvd hpc hqc
        exact ⟨c.val, mem_filter.mpr ⟨mem_range.mpr hc_lt, hdc⟩, Prod.ext hca hcb⟩
    rw [hbij, Finset.card_product, ihp, ihq, pow_succ']

/-- Master counting approximation: for any valid `d`, `|#{m ∈ Icc 1 X | d | F m} - g(d) * X| <= rho(d)`. -/
lemma count_dvd_approx (sf : ShiftedForms) (X d : ℕ)
    (hd0 : 0 < d) (hsf : Squarefree d) (hgt : ∀ p ∈ d.primeFactors, sf.P₀ < p) :
    |(((Icc 1 X).filter (fun m => d ∣ sf.F m)).card : ℝ) - gFunc sf.P₀ d * (X : ℝ)| ≤ rho sf.P₀ d := by
  set R := (range d).filter (fun r => d ∣ sf.F r)
  have hRcard : R.card = 7 ^ d.primeFactors.card := card_roots_squarefree sf hd0 hsf hgt
  -- Partition (Icc 1 X).filter (d | F m) by m % d ∈ R!
  have hpart : ((Icc 1 X).filter (fun m => d ∣ sf.F m)).card =
      ∑ r ∈ R, ((Icc 1 X).filter (fun m => m % d = r)).card := by
    have hbij : (Icc 1 X).filter (fun m => d ∣ sf.F m) =
        R.biUnion (fun r => (Icc 1 X).filter (fun m => m % d = r)) := by
      ext m
      simp only [mem_filter, mem_biUnion, R, mem_range]
      constructor
      · rintro ⟨hm, hdvd⟩
        exact ⟨m % d, ⟨Nat.mod_lt m hd0, (F_dvd_mod_iff sf hd0).mp hdvd⟩, hm, rfl⟩
      · rintro ⟨r, ⟨_, hr⟩, hm, rfl⟩
        exact ⟨hm, (F_dvd_mod_iff sf hd0).mpr hr⟩
    rw [hbij, Finset.card_biUnion]
    intro r1 _ r2 _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro m hm1 hm2
    exact hne ((mem_filter.mp hm1).2.symm.trans (mem_filter.mp hm2).2)
  have hrho : rho sf.P₀ d = (R.card : ℝ) := by
    unfold rho
    rw [if_pos ⟨hsf, hgt⟩, hRcard]
    push_cast; rfl
  have hg : gFunc sf.P₀ d * (X : ℝ) = ∑ _r ∈ R, ((X : ℝ) / (d : ℝ)) := by
    unfold gFunc
    rw [hrho, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hpart, Nat.cast_sum, hg, ← Finset.sum_sub_distrib, hrho]
  calc |∑ r ∈ R, ((((Icc 1 X).filter (fun m => m % d = r)).card : ℝ) - (X : ℝ) / (d : ℝ))|
      ≤ ∑ r ∈ R, |(((Icc 1 X).filter (fun m => m % d = r)).card : ℝ) - (X : ℝ) / (d : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ R, (1 : ℝ) := by
        refine Finset.sum_le_sum fun r hr => card_mod_Icc_bound X d r hd0 (mem_range.mp (mem_filter.mp hr).1)
    _ = (R.card : ℝ) := by simp

/-- Corollary for `I_p = (Icc 1 X).filter (p | F m)` when `p.Prime`, `sf.P₀ < p`, and `w <= p`:
ready to feed directly into `selberg_upper` with `K_err = 7`! -/
lemma count_dvd_approx_Ap (sf : ShiftedForms) {w p : ℕ} (X : ℕ)
    (hp : p.Prime) (hpP : sf.P₀ < p) (hwp : w ≤ p) :
    ∀ d : ℕ, ValidDiv sf.P₀ w d →
      |((((Icc 1 X).filter (fun m => p ∣ sf.F m)).filter (fun m => d ∣ sf.F m)).card : ℝ) -
        gFunc sf.P₀ d * ((7 / (p : ℝ)) * (X : ℝ))| ≤ 7 * rho sf.P₀ d := by
  intro d hd
  have hcop : p.Coprime d := by
    refine hp.coprime_iff_not_dvd.mpr fun hpd => ?_
    have hmem : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, hd.1.ne'⟩
    have := (hd.2.2 p hmem).2
    omega
  have hfilt : ((Icc 1 X).filter (fun m => p ∣ sf.F m)).filter (fun m => d ∣ sf.F m) =
      (Icc 1 X).filter (fun m => (p * d) ∣ sf.F m) := by
    ext m; simp only [mem_filter]
    constructor
    · rintro ⟨⟨hm, hpm⟩, hdm⟩; exact ⟨hm, hcop.mul_dvd_of_dvd_of_dvd hpm hdm⟩
    · rintro ⟨hm, hpdm⟩; exact ⟨⟨hm, (dvd_mul_right p d).trans hpdm⟩, (dvd_mul_left d p).trans hpdm⟩
  have hpd_pos : 0 < p * d := Nat.mul_pos hp.pos hd.1
  have hpd_sf : Squarefree (p * d) := (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, hd.2.1⟩
  have hpd_gt : ∀ q ∈ (p * d).primeFactors, sf.P₀ < q := by
    intro q hq
    rw [Nat.primeFactors_mul hp.ne_zero hd.1.ne', mem_union] at hq
    rcases hq with hqp | hqd
    · rw [hp.primeFactors, mem_singleton] at hqp; subst hqp; exact hpP
    · exact (hd.2.2 q hqd).1
  have happrox := count_dvd_approx sf X (p * d) hpd_pos hpd_sf hpd_gt
  have hrho_pd : rho sf.P₀ (p * d) = 7 * rho sf.P₀ d := by
    unfold rho
    rw [if_pos ⟨hpd_sf, hpd_gt⟩, if_pos ⟨hd.2.1, fun q hq => (hd.2.2 q hq).1⟩,
        Nat.primeFactors_mul hp.ne_zero hd.1.ne',
        Finset.card_union_of_disjoint hcop.disjoint_primeFactors, hp.primeFactors, card_singleton,
        pow_add, pow_one]
  have hg_pd : gFunc sf.P₀ (p * d) * (X : ℝ) = gFunc sf.P₀ d * ((7 / (p : ℝ)) * (X : ℝ)) := by
    unfold gFunc
    rw [hrho_pd, Nat.cast_mul]
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.1.ne'
    field_simp
  rwa [hfilt, ← hg_pd, ← hrho_pd]

/-- Sifted count `SCount sf X w = #{m ∈ Icc 1 X | ∀ p < w, p.Prime → sf.P₀ < p → ¬ p | F m}`. -/
noncomputable def SSet (sf : ShiftedForms) (X w : ℕ) : Finset ℕ :=
  (Icc 1 X).filter (fun m => ∀ p : ℕ, p.Prime → sf.P₀ < p → p < w → ¬ p ∣ sf.F m)

/-- Exact inclusion-exclusion lower bound at small cutoff `z₀`:
`|(SSet sf X z₀).card - X * V7 sf.P₀ z₀| <= 8 ^ z₀`! -/
lemma exact_crt_ie (sf : ShiftedForms) (X z₀ : ℕ) :
    (X : ℝ) * V7 sf.P₀ z₀ - (8 : ℝ) ^ z₀ ≤ ((SSet sf X z₀).card : ℝ) := by
  let Pset := (Ioo sf.P₀ z₀).filter Nat.Prime
  -- Indicator identity for every m ∈ Icc 1 X:
  -- 1_{m ∈ SSet} = ∏_{p ∈ Pset} (1 - 1_{p | F m}) = ∑_{S ⊆ Pset} (-1)^|S| * 1_{(∏ S) | F m}
  have hind : ∀ m ∈ Icc 1 X,
      (if ∀ p : ℕ, p.Prime → sf.P₀ < p → p < z₀ → ¬ p ∣ sf.F m then (1 : ℝ) else 0) =
        ∑ S ∈ Pset.powerset, (-1 : ℝ) ^ S.card * (if (∏ p ∈ S, p) ∣ sf.F m then (1 : ℝ) else 0) := by
    intro m _
    have hprod_ind :
        (if ∀ p : ℕ, p.Prime → sf.P₀ < p → p < z₀ → ¬ p ∣ sf.F m then (1 : ℝ) else 0) =
          ∏ p ∈ Pset, (1 + (if p ∣ sf.F m then (-1 : ℝ) else 0)) := by
      by_cases h : ∀ p : ℕ, p.Prime → sf.P₀ < p → p < z₀ → ¬ p ∣ sf.F m
      · rw [if_pos h]
        symm
        refine Finset.prod_eq_one fun p hp => ?_
        have h1 := mem_Ioo.mp (mem_filter.mp hp).1
        have h2 := (mem_filter.mp hp).2
        rw [if_neg (h p h2 h1.1 h1.2), add_zero]
      · rw [if_neg h]
        push Not at h
        obtain ⟨p, hp, hlo, hhi, hdvd⟩ := h
        symm
        refine Finset.prod_eq_zero (mem_filter.mpr ⟨mem_Ioo.mpr ⟨hlo, hhi⟩, hp⟩) ?_
        rw [if_pos hdvd]; norm_num
    rw [hprod_ind, Finset.prod_one_add]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hSsub := Finset.mem_powerset.mp hS
    have hS_dvd : (∏ p ∈ S, p) ∣ sf.F m ↔ ∀ p ∈ S, p ∣ sf.F m := by
      have hpS : ∀ p ∈ S, p.Prime := fun p hp => (mem_filter.mp (hSsub hp)).2
      clear hprod_ind hS hSsub
      induction S using Finset.induction_on with
      | empty => simp
      | insert p T hpT ih =>
        have hpp : p.Prime := hpS p (mem_insert_self p T)
        have hT : ∀ q ∈ T, q.Prime := fun q hq => hpS q (mem_insert_of_mem hq)
        have hcop : p.Coprime (∏ q ∈ T, q) :=
          Nat.Coprime.prod_right fun q hq =>
            (Nat.coprime_primes hpp (hT q hq)).mpr (fun h => hpT (h ▸ hq))
        rw [Finset.prod_insert hpT]
        constructor
        · intro h q hq
          rw [mem_insert] at hq
          rcases hq with rfl | hqT
          · exact (dvd_mul_right q _).trans h
          · exact (ih hT).mp ((dvd_mul_left _ p).trans h) q hqT
        · intro h
          exact hcop.mul_dvd_of_dvd_of_dvd (h p (mem_insert_self p T))
            ((ih hT).mpr fun q hq => h q (mem_insert_of_mem hq))
    by_cases hall : ∀ p ∈ S, p ∣ sf.F m
    · rw [if_pos (hS_dvd.mpr hall), mul_one]
      have : ∀ p ∈ S, (if p ∣ sf.F m then (-1 : ℝ) else 0) = -1 := fun p hp => if_pos (hall p hp)
      rw [Finset.prod_congr rfl this, Finset.prod_const]
    · rw [if_neg (fun h => hall (hS_dvd.mp h)), mul_zero]
      push Not at hall
      obtain ⟨p, hpS, hnd⟩ := hall
      exact Finset.prod_eq_zero hpS (if_neg hnd)
  -- Sum over m ∈ Icc 1 X and swap sums!
  have hsum_eq : ((SSet sf X z₀).card : ℝ) =
      ∑ S ∈ Pset.powerset, (-1 : ℝ) ^ S.card * (((Icc 1 X).filter (fun m => (∏ p ∈ S, p) ∣ sf.F m)).card : ℝ) := by
    have h1 : ((SSet sf X z₀).card : ℝ) =
        ∑ m ∈ Icc 1 X, if ∀ p : ℕ, p.Prime → sf.P₀ < p → p < z₀ → ¬ p ∣ sf.F m then (1 : ℝ) else 0 := by
      unfold SSet; rw [Finset.sum_boole]
    rw [h1, Finset.sum_congr rfl hind, Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [← Finset.mul_sum, Finset.sum_boole]
  -- Main term: ∑_{S ⊆ Pset} (-1)^|S| * g(∏ S) * X = X * ∏_{p ∈ Pset} (1 - 7/p) = X * V7 sf.P₀ z₀!
  have hmain_eq :
      ∑ S ∈ Pset.powerset, (-1 : ℝ) ^ S.card * (gFunc sf.P₀ (∏ p ∈ S, p) * (X : ℝ)) =
        (X : ℝ) * V7 sf.P₀ z₀ := by
    unfold V7
    have hprod_rew : ∏ p ∈ Pset, (1 - 7 / (p : ℝ)) = ∏ p ∈ Pset, (1 + (-(7 / (p : ℝ)))) := by
      refine Finset.prod_congr rfl fun p _ => by ring
    rw [hprod_rew, Finset.prod_one_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hSsub := Finset.mem_powerset.mp hS
    have hpS : ∀ p ∈ S, p.Prime := fun p hp => (mem_filter.mp (hSsub hp)).2
    have hsfS : Squarefree (∏ p ∈ S, p) := by
      clear hS hSsub hprod_rew hsum_eq hind
      induction S using Finset.induction_on with
      | empty => simp
      | insert p T hpT ih =>
        rw [Finset.prod_insert hpT]
        have hpp := hpS p (mem_insert_self p T)
        have hT : ∀ q ∈ T, q.Prime := fun q hq => hpS q (mem_insert_of_mem hq)
        have hcop : p.Coprime (∏ q ∈ T, q) :=
          Nat.Coprime.prod_right fun q hq =>
            (Nat.coprime_primes hpp (hT q hq)).mpr (fun h => hpT (h ▸ hq))
        exact (Nat.squarefree_mul hcop).mpr ⟨hpp.squarefree, ih hT⟩
    have hpfS : (∏ p ∈ S, p).primeFactors = S := by
      clear hsfS hS hSsub hprod_rew hsum_eq hind
      induction S using Finset.induction_on with
      | empty => simp
      | insert p T hpT ih =>
        have hpp := hpS p (mem_insert_self p T)
        have hT : ∀ q ∈ T, q.Prime := fun q hq => hpS q (mem_insert_of_mem hq)
        have hTpos : 0 < ∏ q ∈ T, q := Finset.prod_pos fun q hq => (hT q hq).pos
        rw [Finset.prod_insert hpT, Nat.primeFactors_mul hpp.ne_zero hTpos.ne', hpp.primeFactors, ih hT]
        ext q; simp
    have hgtS : ∀ p ∈ (∏ q ∈ S, q).primeFactors, sf.P₀ < p := by
      intro p hp; rw [hpfS] at hp; exact (mem_Ioo.mp (mem_filter.mp (hSsub hp)).1).1
    unfold gFunc rho
    rw [if_pos ⟨hsfS, hgtS⟩, hpfS, Nat.cast_prod]
    have hprod_neg : ∏ p ∈ S, (-(7 / (p : ℝ))) = (-1 : ℝ) ^ S.card * ((7 : ℝ) ^ S.card / ∏ p ∈ S, (p : ℝ)) := by
      have : ∏ p ∈ S, (-(7 / (p : ℝ))) = ∏ p ∈ S, ((-1 : ℝ) * (7 / (p : ℝ))) :=
        Finset.prod_congr rfl fun p _ => by ring
      rw [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_div_distrib, Finset.prod_const]
    rw [hprod_neg]
    ring
  -- Error bound: ≤ ∑_{S ⊆ Pset} 7^|S| = 8^Pset.card ≤ 8^z₀!
  have herr_le : |((SSet sf X z₀).card : ℝ) - (X : ℝ) * V7 sf.P₀ z₀| ≤ (8 : ℝ) ^ z₀ := by
    rw [hsum_eq, ← hmain_eq, ← Finset.sum_sub_distrib]
    calc |∑ S ∈ Pset.powerset,
            ((-1 : ℝ) ^ S.card * (((Icc 1 X).filter (fun m => (∏ p ∈ S, p) ∣ sf.F m)).card : ℝ) -
             (-1 : ℝ) ^ S.card * (gFunc sf.P₀ (∏ p ∈ S, p) * (X : ℝ)))|
        ≤ ∑ S ∈ Pset.powerset,
            |(-1 : ℝ) ^ S.card * ((((Icc 1 X).filter (fun m => (∏ p ∈ S, p) ∣ sf.F m)).card : ℝ) -
              gFunc sf.P₀ (∏ p ∈ S, p) * (X : ℝ))| := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
          refine Finset.sum_congr rfl fun S _ => by ring_nf
      _ ≤ ∑ S ∈ Pset.powerset, (7 : ℝ) ^ S.card := by
          refine Finset.sum_le_sum fun S hS => ?_
          have hSsub := Finset.mem_powerset.mp hS
          have hpS : ∀ p ∈ S, p.Prime := fun p hp => (mem_filter.mp (hSsub hp)).2
          have hposS : 0 < ∏ p ∈ S, p := Finset.prod_pos fun p hp => (hpS p hp).pos
          have hsfS : Squarefree (∏ p ∈ S, p) := by
            clear hposS hS hSsub hmain_eq hsum_eq hind
            induction S using Finset.induction_on with
            | empty => simp
            | insert p T hpT ih =>
              rw [Finset.prod_insert hpT]
              have hpp := hpS p (mem_insert_self p T)
              have hT : ∀ q ∈ T, q.Prime := fun q hq => hpS q (mem_insert_of_mem hq)
              have hcop : p.Coprime (∏ q ∈ T, q) :=
                Nat.Coprime.prod_right fun q hq =>
                  (Nat.coprime_primes hpp (hT q hq)).mpr (fun h => hpT (h ▸ hq))
              exact (Nat.squarefree_mul hcop).mpr ⟨hpp.squarefree, ih hT⟩
          have hpfS : (∏ p ∈ S, p).primeFactors = S := by
            clear hposS hsfS hS hSsub hmain_eq hsum_eq hind
            induction S using Finset.induction_on with
            | empty => simp
            | insert p T hpT ih =>
              have hpp := hpS p (mem_insert_self p T)
              have hT : ∀ q ∈ T, q.Prime := fun q hq => hpS q (mem_insert_of_mem hq)
              have hTpos : 0 < ∏ q ∈ T, q := Finset.prod_pos fun q hq => (hT q hq).pos
              rw [Finset.prod_insert hpT, Nat.primeFactors_mul hpp.ne_zero hTpos.ne', hpp.primeFactors, ih hT]
              ext q; simp
          have hgtS : ∀ p ∈ (∏ q ∈ S, q).primeFactors, sf.P₀ < p := by
            intro p hp; rw [hpfS] at hp; exact (mem_Ioo.mp (mem_filter.mp (hSsub hp)).1).1
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
          have hbound := count_dvd_approx sf X (∏ p ∈ S, p) hposS hsfS hgtS
          unfold rho at hbound
          rw [if_pos ⟨hsfS, hgtS⟩, hpfS] at hbound
          exact hbound
      _ = (8 : ℝ) ^ Pset.card := by
          have : (8 : ℝ) ^ Pset.card = ∏ _p ∈ Pset, (1 + (7 : ℝ)) := by
            rw [Finset.prod_const]; norm_num
          rw [this, Finset.prod_one_add]
          refine Finset.sum_congr rfl fun S _ => by rw [Finset.prod_const]
      _ ≤ (8 : ℝ) ^ z₀ := by
          refine pow_le_pow_right₀ (by norm_num) ?_
          have hsub : Pset ⊆ range z₀ := fun p hp => mem_range.mpr (mem_Ioo.mp (mem_filter.mp hp).1).2
          exact (Finset.card_le_card hsub).trans_eq (Finset.card_range z₀)
  linarith [(abs_le.mp herr_le).1]

/-- Exact finite telescoping identity for `V7`:
`V7 P₀ z₀ - ∑_{z₀ <= p < z, p.Prime} (7/p) * V7 P₀ p = V7 P₀ z` whenever `P₀ < z₀ <= z`. -/
lemma V7_telescope {P₀ z₀ z : ℕ} (hP₀ : P₀ < z₀) (hz : z₀ ≤ z) :
    V7 P₀ z₀ - ∑ p ∈ (Ico z₀ z).filter Nat.Prime, (7 / (p : ℝ)) * V7 P₀ p = V7 P₀ z := by
  induction z, hz using Nat.le_induction with
  | base => simp
  | succ w hw ih =>
    have hIco : (Ico z₀ (w + 1)).filter Nat.Prime =
        if w.Prime then insert w ((Ico z₀ w).filter Nat.Prime) else (Ico z₀ w).filter Nat.Prime := by
      have h1 : Ico z₀ (w + 1) = insert w (Ico z₀ w) := by
        ext x; simp only [mem_Ico, mem_insert]; omega
      rw [h1, Finset.filter_insert]
    have hVstep : V7 P₀ (w + 1) =
        if w.Prime then (1 - 7 / (w : ℝ)) * V7 P₀ w else V7 P₀ w := by
      unfold V7
      have h1 : Ioo P₀ (w + 1) = insert w (Ioo P₀ w) := by
        ext x; simp only [mem_Ioo, mem_insert]; omega
      have hnot : w ∉ (Ioo P₀ w).filter Nat.Prime := by simp
      rw [h1, Finset.filter_insert]
      split_ifs with hp
      · rw [Finset.prod_insert hnot]
      · rfl
    rw [hIco, hVstep]
    split_ifs with hp
    · have hnot : w ∉ (Ico z₀ w).filter Nat.Prime := by simp
      rw [Finset.sum_insert hnot]
      linarith
    · exact ih

/-- Exact finite Buchstab identity:
`SSet sf X z = SSet sf X z₀ \ ⋃_{z₀ <= p < z} S_p(p)` (disjoint union by least prime factor `>= z₀`),
hence `(SSet sf X z).card = (SSet sf X z₀).card - ∑_{z₀ <= p < z, p.Prime} (SSet_p sf X p).card`! -/
lemma buchstab_card_eq (sf : ShiftedForms) {X z₀ z : ℕ} (hP₀ : sf.P₀ < z₀) (hz : z₀ ≤ z) :
    ((SSet sf X z).card : ℝ) =
      ((SSet sf X z₀).card : ℝ) -
        ∑ p ∈ (Ico z₀ z).filter Nat.Prime,
          ((((Icc 1 X).filter (fun m => p ∣ sf.F m)).filter
            (fun m => ∀ q : ℕ, q.Prime → sf.P₀ < q → q < p → ¬ q ∣ sf.F m)).card : ℝ) := by
  induction z, hz using Nat.le_induction with
  | base => simp
  | succ w hw ih =>
    have hIco : (Ico z₀ (w + 1)).filter Nat.Prime =
        if w.Prime then insert w ((Ico z₀ w).filter Nat.Prime) else (Ico z₀ w).filter Nat.Prime := by
      have h1 : Ico z₀ (w + 1) = insert w (Ico z₀ w) := by
        ext x; simp only [mem_Ico, mem_insert]; omega
      rw [h1, Finset.filter_insert]
    rw [hIco]
    split_ifs with hp
    · have hnot : w ∉ (Ico z₀ w).filter Nat.Prime := by simp
      rw [Finset.sum_insert hnot]
      -- Show SSet sf X w = SSet sf X (w + 1) ⊔ ((Icc 1 X).filter (w | F m)).filter (rough < w)
      have hdisj : Disjoint (SSet sf X (w + 1))
          (((Icc 1 X).filter (fun m => w ∣ sf.F m)).filter
            (fun m => ∀ q : ℕ, q.Prime → sf.P₀ < q → q < w → ¬ q ∣ sf.F m)) := by
        rw [Finset.disjoint_left]
        intro m hm1 hm2
        have hrough := (mem_filter.mp hm1).2
        have hwdvd := (mem_filter.mp (mem_filter.mp hm2).1).2
        exact hrough w hp (lt_of_lt_of_le hP₀ hw) (Nat.lt_succ_self w) hwdvd
      have hunion : SSet sf X (w + 1) ∪
          (((Icc 1 X).filter (fun m => w ∣ sf.F m)).filter
            (fun m => ∀ q : ℕ, q.Prime → sf.P₀ < q → q < w → ¬ q ∣ sf.F m)) = SSet sf X w := by
        ext m; simp only [mem_union, SSet, mem_filter]
        constructor
        · rintro (⟨hm, h⟩ | ⟨⟨hm, _⟩, h⟩)
          · exact ⟨hm, fun q hq hlo hhi => h q hq hlo (Nat.lt_succ_of_lt hhi)⟩
          · exact ⟨hm, h⟩
        · rintro ⟨hm, h⟩
          by_cases hwdvd : w ∣ sf.F m
          · exact Or.inr ⟨⟨hm, hwdvd⟩, h⟩
          · refine Or.inl ⟨hm, fun q hq hlo hhi => ?_⟩
            by_cases hqw : q = w
            · subst hqw; exact hwdvd
            · exact h q hq hlo (by omega)
      have hcard : (SSet sf X (w + 1)).card +
          (((Icc 1 X).filter (fun m => w ∣ sf.F m)).filter
            (fun m => ∀ q : ℕ, q.Prime → sf.P₀ < q → q < w → ¬ q ∣ sf.F m)).card =
          (SSet sf X w).card := by
        rw [← Finset.card_union_of_disjoint hdisj, hunion]
      have hcardR : ((SSet sf X (w + 1)).card : ℝ) +
          ((((Icc 1 X).filter (fun m => w ∣ sf.F m)).filter
            (fun m => ∀ q : ℕ, q.Prime → sf.P₀ < q → q < w → ¬ q ∣ sf.F m)).card : ℝ) =
          ((SSet sf X w).card : ℝ) := by exact_mod_cast hcard
      linarith
    · have hsame : SSet sf X (w + 1) = SSet sf X w := by
        ext m; simp only [SSet, mem_filter]
        constructor
        · rintro ⟨hm, h⟩; exact ⟨hm, fun q hq hlo hhi => h q hq hlo (Nat.lt_succ_of_lt hhi)⟩
        · rintro ⟨hm, h⟩; refine ⟨hm, fun q hq hlo hhi => ?_⟩
          have hne : q ≠ w := fun heq => hp (heq ▸ hq)
          exact h q hq hlo (by omega)
      rw [hsame]; exact ih

end Erdos946Sieve1
end

section
open Finset Filter Real
open scoped BigOperators Classical

namespace Erdos946Sieve2

open Erdos946MertensAux Erdos946Selberg Erdos946Sieve1

/-! ### Part 1: Elementary numerical certificates for `exp` and `log` -/

lemma exp_le_inv_one_sub_div16 {c : ℝ} (_hc0 : 0 ≤ c) (hc1 : c < 16) :
    Real.exp c ≤ ((1 - c / 16) ^ 16)⁻¹ := by
  have h1 : 0 < 1 - c / 16 := by linarith
  have h2 : 1 - c / 16 ≤ Real.exp (-(c / 16)) := by
    linarith [Real.add_one_le_exp (-(c / 16))]
  have h3 : (1 - c / 16) ^ 16 ≤ Real.exp (-c) := by
    calc (1 - c / 16) ^ 16
        ≤ (Real.exp (-(c / 16))) ^ 16 := pow_le_pow_left₀ h1.le h2 16
      _ = Real.exp (((16 : ℕ) : ℝ) * (-(c / 16))) := (Real.exp_nat_mul _ 16).symm
      _ = Real.exp (-c) := by congr 1; push_cast; ring
  rw [Real.exp_neg] at h3
  calc Real.exp c = ((Real.exp c)⁻¹)⁻¹ := (inv_inv _).symm
    _ ≤ ((1 - c / 16) ^ 16)⁻¹ := inv_anti₀ (pow_pos h1 16) h3

lemma exp_neg_le_of_taylor12 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (h : 1 / b ≤ ∑ i ∈ range 13, a ^ i / (i.factorial : ℝ)) :
    Real.exp (-a) ≤ b := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos a) hb]
  rw [one_div] at h
  exact h.trans (Real.sum_le_exp_of_nonneg ha 13)

lemma log_le_of_taylor10 {x L : ℝ} (hx : 0 < x) (hL : 0 ≤ L)
    (h : x ≤ ∑ i ∈ range 11, L ^ i / (i.factorial : ℝ)) :
    Real.log x ≤ L :=
  (Real.log_le_iff_le_exp hx).mpr (h.trans (Real.sum_le_exp_of_nonneg hL 11))

/-- Buchstab tail kernel bound: for all `t >= 69/2`, `(t / 34)^7 * t^2 * exp(27/2 - (13/20) * t) <= 9/50`. -/
lemma buchstab_kernel_bound {t : ℝ} (ht : (69 / 2 : ℝ) ≤ t) :
    (t / 34) ^ 7 * t ^ 2 * Real.exp ((27 / 2 : ℝ) - (13 / 20 : ℝ) * t) ≤ 9 / 50 := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ 9 * Real.exp (-(13 / 20 : ℝ) * x)) (Set.Ici (69 / 2 : ℝ)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici (69 / 2 : ℝ)) ?_ ?_ ?_
    · exact (continuous_pow 9 |>.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn
    · exact ((differentiable_pow 9).mul (Real.differentiable_exp.comp ((differentiable_const _).mul differentiable_id))).differentiableOn
    · intro x hx
      have hx' : (69 / 2 : ℝ) < x := by simpa [interior_Ici] using hx
      have hd : HasDerivAt (fun z : ℝ => z ^ 9 * Real.exp (-(13 / 20 : ℝ) * z))
          ((9 - (13 / 20 : ℝ) * x) * x ^ 8 * Real.exp (-(13 / 20 : ℝ) * x)) x := by
        have d1 : HasDerivAt (fun z : ℝ => z ^ 9) (9 * x ^ 8) x := by
          simpa using hasDerivAt_pow 9 x
        have dlin : HasDerivAt (fun z : ℝ => -(13 / 20 : ℝ) * z) (-(13 / 20 : ℝ)) x := by
          simpa using (hasDerivAt_id x).const_mul (-(13 / 20 : ℝ))
        have d2 : HasDerivAt (fun z : ℝ => Real.exp (-(13 / 20 : ℝ) * z))
            (Real.exp (-(13 / 20 : ℝ) * x) * (-(13 / 20 : ℝ))) x :=
          (Real.hasDerivAt_exp (-(13 / 20 : ℝ) * x)).comp x dlin
        have dm := d1.mul d2
        have hdeq : 9 * x ^ 8 * Real.exp (-(13 / 20 : ℝ) * x) +
            x ^ 9 * (Real.exp (-(13 / 20 : ℝ) * x) * (-(13 / 20 : ℝ))) =
            (9 - (13 / 20 : ℝ) * x) * x ^ 8 * Real.exp (-(13 / 20 : ℝ) * x) := by ring
        rwa [hdeq] at dm
      rw [hd.deriv]
      have h1 : 9 - (13 / 20 : ℝ) * x ≤ 0 := by linarith
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg h1 (pow_nonneg (by linarith) 8))
        (Real.exp_pos _).le
  have hle_at : t ^ 9 * Real.exp (-(13 / 20 : ℝ) * t) ≤
      (69 / 2 : ℝ) ^ 9 * Real.exp (-(13 / 20 : ℝ) * (69 / 2)) :=
    hanti (Set.mem_Ici.mpr le_rfl) ht ht
  have hrew : (t / 34) ^ 7 * t ^ 2 * Real.exp ((27 / 2 : ℝ) - (13 / 20 : ℝ) * t) =
      (1 / 34 ^ 7) * (t ^ 9 * Real.exp (-(13 / 20 : ℝ) * t)) * Real.exp (27 / 2 : ℝ) := by
    rw [show (27 / 2 : ℝ) - (13 / 20 : ℝ) * t = (27 / 2 : ℝ) + (-(13 / 20 : ℝ) * t) by ring, Real.exp_add]
    ring
  have hval : (1 / 34 ^ 7 : ℝ) * ((69 / 2 : ℝ) ^ 9 * Real.exp (-(13 / 20 : ℝ) * (69 / 2))) * Real.exp (27 / 2 : ℝ) =
      ((69 / 2 / 34) ^ 7 * (69 / 2 : ℝ) ^ 2) * Real.exp (-(357 / 40 : ℝ)) := by
    rw [show (1 / 34 ^ 7 : ℝ) * ((69 / 2 : ℝ) ^ 9 * Real.exp (-(13 / 20 : ℝ) * (69 / 2))) * Real.exp (27 / 2 : ℝ) =
        ((69 / 2 / 34) ^ 7 * (69 / 2 : ℝ) ^ 2) * (Real.exp (-(13 / 20 : ℝ) * (69 / 2)) * Real.exp (27 / 2 : ℝ)) by ring,
        ← Real.exp_add]
    congr 2; norm_num
  have hexp_b : Real.exp (-(357 / 40 : ℝ)) ≤ 135 / 1000000 := by
    have h4 : (93 / 10 : ℝ) ≤ Real.exp ((357 / 40 : ℝ) / 4) := by
      have h1 := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ (357 / 40 : ℝ) / 4) 11
      have h2 : (93 / 10 : ℝ) ≤ ∑ i ∈ range 11, ((357 / 40 : ℝ) / 4) ^ i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
      exact h2.trans h1
    have hpow : (93 / 10 : ℝ) ^ 4 ≤ Real.exp (357 / 40 : ℝ) := by
      calc (93 / 10 : ℝ) ^ 4 ≤ (Real.exp ((357 / 40 : ℝ) / 4)) ^ 4 := pow_le_pow_left₀ (by norm_num) h4 4
        _ = Real.exp (((4 : ℕ) : ℝ) * ((357 / 40 : ℝ) / 4)) := (Real.exp_nat_mul _ 4).symm
        _ = Real.exp (357 / 40 : ℝ) := by congr 1; norm_num
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have hnum : ((135 / 1000000 : ℝ))⁻¹ ≤ (93 / 10 : ℝ) ^ 4 := by norm_num
    exact hnum.trans hpow
  rw [hrew]
  calc (1 / 34 ^ 7 : ℝ) * (t ^ 9 * Real.exp (-(13 / 20 : ℝ) * t)) * Real.exp (27 / 2 : ℝ)
      ≤ (1 / 34 ^ 7 : ℝ) * ((69 / 2 : ℝ) ^ 9 * Real.exp (-(13 / 20 : ℝ) * (69 / 2))) * Real.exp (27 / 2 : ℝ) := by
        gcongr
    _ = ((69 / 2 / 34) ^ 7 * (69 / 2 : ℝ) ^ 2) * Real.exp (-(357 / 40 : ℝ)) := hval
    _ ≤ ((69 / 2 / 34) ^ 7 * (69 / 2 : ℝ) ^ 2) * (135 / 1000000) := by gcongr
    _ ≤ 9 / 50 := by norm_num

/-! ### Part 2: Reusable Selberg+Rankin upper bound for `S_p(w)` -/

/-- Master reusable upper bound for `S_p(w)` using `selberg_upper` + `rankin_GSum_lower`. -/
lemma selberg_Ap_upper (sf : ShiftedForms) (c : ℝ) (hc : 0 < c) :
    ∃ C_rk C_err : ℝ, 0 < C_rk ∧ 0 < C_err ∧
      ∀ (X w p R : ℕ), sf.P₀ < w → w ≤ p → p.Prime → 2 ≤ R →
        let err := Real.exp (7 * EinUb c + C_rk / Real.log w - c * Real.log R / Real.log w)
        err < 1 →
        ((((Icc 1 X).filter (fun m => p ∣ sf.F m)).filter
          (fun m => ∀ q : ℕ, q.Prime → sf.P₀ < q → q < w → ¬ q ∣ sf.F m)).card : ℝ) ≤
        ((7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ w) / (1 - err) +
          C_err * (R : ℝ) ^ 2 * (Real.log R) ^ 14 := by
  obtain ⟨C_rk, hCrk_p, hCrk⟩ := sum_h_rpow_sub_one_le sf.P₀ sf.hP₀ c hc
  obtain ⟨C_pr, hCpr_p, hCpr⟩ := prod_one_add_seven_div_p_le sf.P₀ sf.hP₀
  refine ⟨C_rk, 7 * C_pr ^ 2, hCrk_p, by positivity, fun X w p R hw hwp hp hR herr => ?_⟩
  set err := Real.exp (7 * EinUb c + C_rk / Real.log w - c * Real.log R / Real.log w)
  have hpP : sf.P₀ < p := lt_of_lt_of_le hw hwp
  have hsel := selberg_upper sf.hP₀ (by omega : 1 ≤ R)
    ((Icc 1 X).filter (fun m => p ∣ sf.F m)) sf.F ((7 / (p : ℝ)) * (X : ℝ)) 7 (by norm_num)
    (count_dvd_approx_Ap sf X hp hpP hwp)
  have hlw : 0 < Real.log (w : ℝ) := Real.log_pos (by exact_mod_cast (by have := sf.hP₀; omega : 1 < w))
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hrk := rankin_GSum_lower (P₀ := sf.P₀) (w := w) (R := R) sf.hP₀ (by omega : 1 ≤ R)
    (c / Real.log w) (div_pos hc hlw)
  -- Show (R : ℝ)^(-(c/log w)) * exp(∑ h(p)(p^(c/log w) - 1)) <= err
  have hsum_ub := hCrk w hw
  have herr_ge : (R : ℝ) ^ (-(c / Real.log w)) *
      Real.exp (∑ q ∈ (Ioo sf.P₀ w).filter Nat.Prime, (7 / ((q : ℝ) - 7)) * ((q : ℝ) ^ (c / Real.log w) - 1)) ≤ err := by
    rw [Real.rpow_def_of_pos hRpos, ← Real.exp_add]
    dsimp [err]
    apply Real.exp_le_exp.mpr
    linarith [show Real.log (R : ℝ) * -(c / Real.log (w : ℝ)) = -(c * Real.log (R : ℝ) / Real.log (w : ℝ)) by ring]
  have hGV_lb : 1 - err ≤ GSum sf.P₀ w R * V7 sf.P₀ w := by linarith
  have hGpos := GSum_pos (w := w) sf.hP₀ (by omega : 1 ≤ R)
  have hVpos := V7_pos (w := w) sf.hP₀
  have h1merr_pos : 0 < 1 - err := by linarith
  have hmain_ub : ((7 / (p : ℝ)) * (X : ℝ)) / GSum sf.P₀ w R ≤
      ((7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ w) / (1 - err) := by
    rw [div_le_div_iff₀ hGpos h1merr_pos]
    have hXnn : 0 ≤ (7 / (p : ℝ)) * (X : ℝ) := by positivity
    calc (7 / (p : ℝ)) * (X : ℝ) * (1 - err)
        ≤ (7 / (p : ℝ)) * (X : ℝ) * (GSum sf.P₀ w R * V7 sf.P₀ w) :=
          mul_le_mul_of_nonneg_left hGV_lb hXnn
      _ = (7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ w * GSum sf.P₀ w R := by ring
  have herr_sum : (∑ d ∈ (Icc 1 R).filter (fun d => ValidDiv sf.P₀ w d), rho sf.P₀ d) ^ 2 ≤
      C_pr ^ 2 * (R : ℝ) ^ 2 * (Real.log R) ^ 14 := by
    have h1 := sum_rho_le_mul_prod (P₀ := sf.P₀) (w := w) (R := R) sf.hP₀
    have h2 := hCpr R hR
    have hnn : 0 ≤ ∑ d ∈ (Icc 1 R).filter (fun d => ValidDiv sf.P₀ w d), rho sf.P₀ d :=
      Finset.sum_nonneg fun d _ => by unfold rho; split_ifs <;> positivity
    have h3 : ∑ d ∈ (Icc 1 R).filter (fun d => ValidDiv sf.P₀ w d), rho sf.P₀ d ≤
        (R : ℝ) * (C_pr * (Real.log R) ^ 7) := h1.trans (mul_le_mul_of_nonneg_left h2 hRpos.le)
    calc (∑ d ∈ (Icc 1 R).filter (fun d => ValidDiv sf.P₀ w d), rho sf.P₀ d) ^ 2
        ≤ ((R : ℝ) * (C_pr * (Real.log R) ^ 7)) ^ 2 := pow_le_pow_left₀ hnn h3 2
      _ = C_pr ^ 2 * (R : ℝ) ^ 2 * (Real.log R) ^ 14 := by ring
  calc ((((Icc 1 X).filter (fun m => p ∣ sf.F m)).filter
          (fun m => ∀ q : ℕ, q.Prime → sf.P₀ < q → q < w → ¬ q ∣ sf.F m)).card : ℝ)
      ≤ ((7 / (p : ℝ)) * (X : ℝ)) / GSum sf.P₀ w R +
          7 * (∑ d ∈ (Icc 1 R).filter (fun d => ValidDiv sf.P₀ w d), rho sf.P₀ d) ^ 2 := hsel
    _ ≤ ((7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ w) / (1 - err) +
          7 * (C_pr ^ 2 * (R : ℝ) ^ 2 * (Real.log R) ^ 14) := by gcongr
    _ = ((7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ w) / (1 - err) +
          7 * C_pr ^ 2 * (R : ℝ) ^ 2 * (Real.log R) ^ 14 := by ring

/-! ### Part 3: Buchstab lower bound `S(z) >= 0.995 * X * V7(z)` at `z = ⌈X^(1/36)⌉₊` -/

set_option maxHeartbeats 800000 in
lemma buchstab_lower_bound (sf : ShiftedForms) :
    ∀ᶠ X : ℕ in atTop,
      let z := ⌈(X : ℝ) ^ ((1 : ℝ) / 36)⌉₊
      (995 / 1000 : ℝ) * (X : ℝ) * V7 sf.P₀ z ≤ ((SSet sf X z).card : ℝ) := by
  obtain ⟨C_rk, C_err, hCrk_p, hCerr_p, hAp⟩ := selberg_Ap_upper sf (13 / 10 : ℝ) (by norm_num)
  obtain ⟨cV1, cV2, hcV1p, hcV2p, hV_ord⟩ := (V7_asymptotics sf.P₀ sf.hP₀).1
  obtain ⟨CV_rat, hCVrat_p, hV_rat⟩ := (V7_asymptotics sf.P₀ sf.hP₀).2
  obtain ⟨C_m1, hCm1p, hM1⟩ := sum_log_pow_div_p_le 1 (by norm_num)
  have hEin13 : 7 * EinUb (13 / 10 : ℝ) + 1 / 5 ≤ 27 / 2 := by
    have he13 : Real.exp (13 / 10 : ℝ) ≤ 3881 / 1000 := by
      have h1 := exp_le_inv_one_sub_div16 (c := 13 / 10) (by norm_num) (by norm_num)
      refine h1.trans ?_
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      norm_num
    unfold EinUb
    nlinarith [show (0 : ℝ) ≤ (13 / 10 : ℝ) ^ 5 / 600 by positivity]
  have hlogX : Filter.Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev_z0 : ∀ᶠ X : ℕ in atTop,
      (sf.P₀ : ℝ) + 100 ≤ Real.log (X : ℝ) / 20 ∧
      max (C_rk / (1 / 5)) (CV_rat / Real.log (3 / 2)) ≤ Real.log (Real.log (X : ℝ) / 40) := by
    have h1 := hlogX.atTop_div_const (by norm_num : (0 : ℝ) < 20) |>.eventually_ge_atTop ((sf.P₀ : ℝ) + 100)
    have h2 := (Real.tendsto_log_atTop.comp (hlogX.atTop_div_const (by norm_num : (0 : ℝ) < 40))).eventually_ge_atTop
      (max (C_rk / (1 / 5)) (CV_rat / Real.log (3 / 2)))
    exact h1.and h2
  have hev_log_ratio : ∀ᶠ X : ℕ in atTop,
      26 * Real.log (Real.log (X : ℝ)) + 10 ≤ (1 / 1000 : ℝ) * Real.log (X : ℝ) := by
    have hlo := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).bound (by norm_num : (0 : ℝ) < 1 / 52000)
    have h1 := hlogX.eventually hlo
    filter_upwards [h1, hlogX.eventually_ge_atTop 20000] with X hX hXbig
    have hlX : 0 < Real.log (X : ℝ) := by linarith
    have hllX : 0 ≤ Real.log (Real.log (X : ℝ)) := Real.log_nonneg (by linarith)
    change ‖Real.log (Real.log (X : ℝ))‖ ≤ (1 / 52000) * ‖(Real.log (X : ℝ)) ^ (1 : ℝ)‖ at hX
    rw [Real.rpow_one, Real.norm_of_nonneg hllX, Real.norm_of_nonneg hlX.le] at hX
    linarith
  have hev_err_pow : ∀ᶠ X : ℕ in atTop,
      (X : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log (X : ℝ)) ^ 7 ≤ cV1 / (10000 * 36 ^ 7) ∧
      C_err * (Real.log (X : ℝ)) ^ (-3 : ℝ) ≤ cV1 / (10000 * 36 ^ 7) ∧
      (1 / 100 : ℝ) * Real.log (X : ℝ) ≥ C_m1 ∧
      (20000 : ℝ) ≤ Real.log (X : ℝ) := by
    have h1 : Tendsto (fun X : ℕ => (X : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log (X : ℝ)) ^ 7) atTop (nhds 0) := by
      have hlo := (isLittleO_log_rpow_rpow_atTop (7 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
      refine (hlo.comp tendsto_natCast_atTop_atTop).congr' ?_
      filter_upwards [eventually_ge_atTop 2] with X hX
      have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
      rw [Real.rpow_neg hXp.le, ← div_eq_inv_mul]
      simp
    have h2 : Tendsto (fun X : ℕ => C_err * (Real.log (X : ℝ)) ^ (-3 : ℝ)) atTop (nhds 0) := by
      have h3 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)).comp hlogX
      simpa using h3.const_mul C_err
    exact ((h1.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < cV1 / (10000 * 36 ^ 7)))).and
      (h2.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < cV1 / (10000 * 36 ^ 7))))).and
      ((hlogX.eventually_ge_atTop (100 * C_m1)).and (hlogX.eventually_ge_atTop 20000)) |>.mono
        fun X ⟨⟨a, b⟩, ⟨c, d⟩⟩ => ⟨a.le, b.le, by linarith, d⟩
  have hev_z_gt : ∀ᶠ X : ℕ in atTop,
      Real.log (X : ℝ) / 20 + 10 ≤ (X : ℝ) ^ ((1 : ℝ) / 36) ∧
      (100 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 4) / (Real.log (X : ℝ)) ^ 25 := by
    have h1 := tendsto_natCast_atTop_atTop.eventually
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 36)).bound (by norm_num : (0 : ℝ) < 1 / 40))
    have h2 := ((isLittleO_log_rpow_rpow_atTop (25 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
    filter_upwards [h1, h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100)),
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 36)).comp tendsto_natCast_atTop_atTop |>.eventually_ge_atTop 100,
      eventually_ge_atTop 100] with X hX1 hX2 hX3 hX100
    have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
    have hlX : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
    dsimp only [Function.comp_apply] at hX2 hX3
    change ‖Real.log (X : ℝ)‖ ≤ (1 / 40) * ‖(X : ℝ) ^ ((1 : ℝ) / 36)‖ at hX1
    rw [Real.norm_of_nonneg hlX.le, Real.norm_of_nonneg (Real.rpow_nonneg hXp.le _)] at hX1
    have hX2' : (Real.log (X : ℝ)) ^ (25 : ℕ) / (X : ℝ) ^ ((1 : ℝ) / 4) < 1 / 100 := by
      simpa only [show (25 : ℝ) = ((25 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] using hX2
    have hdiv : (100 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 4) / (Real.log (X : ℝ)) ^ 25 := by
      have hpos1 : 0 < (X : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hXp _
      have hpos2 : 0 < (Real.log (X : ℝ)) ^ 25 := pow_pos hlX 25
      rw [div_lt_iff₀ hpos1] at hX2'
      rw [le_div_iff₀ hpos2]
      linarith only [hX2']
    exact ⟨by linarith only [hX1, hX3], hdiv⟩
  filter_upwards [hev_z0, hev_log_ratio, hev_err_pow, hev_z_gt, eventually_ge_atTop 1000]
    with X ⟨hz0_big, hz0_log⟩ hlog_rat ⟨herr_ie, herr_sel, hCm1_le, hlX_big⟩ ⟨hz_gt_z0, hR_big⟩ hX1000
  intro z
  set z₀ := ⌊Real.log (X : ℝ) / 20⌋₊
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hlX : 0 < Real.log (X : ℝ) := by linarith
  have hz0_ge : sf.P₀ < z₀ := by
    have h1 : (sf.P₀ : ℝ) + 99 ≤ (z₀ : ℝ) := by
      have := Nat.lt_floor_add_one (Real.log (X : ℝ) / 20)
      linarith
    have : sf.P₀ + 99 ≤ z₀ := by exact_mod_cast h1
    omega
  have hz0_lb : Real.log (X : ℝ) / 40 ≤ (z₀ : ℝ) := by
    have := Nat.lt_floor_add_one (Real.log (X : ℝ) / 20)
    linarith
  have hz0_ub : (z₀ : ℝ) ≤ Real.log (X : ℝ) / 20 := Nat.floor_le (by positivity)
  have hz_ge_r : (X : ℝ) ^ ((1 : ℝ) / 36) ≤ (z : ℝ) := Nat.le_ceil _
  have hz_le_r : (z : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 36) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hz0_le_z : z₀ ≤ z := by
    have : (z₀ : ℝ) ≤ (z : ℝ) := by linarith
    exact_mod_cast this
  have hlogz_ub : Real.log (z : ℝ) ≤ Real.log (X : ℝ) / (359 / 10 : ℝ) := by
    have hz_le2 : (z : ℝ) ≤ 2 * (X : ℝ) ^ ((1 : ℝ) / 36) := by
      have : (1 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 36) := Real.one_le_rpow hX1 (by norm_num)
      linarith
    calc Real.log (z : ℝ) ≤ Real.log (2 * (X : ℝ) ^ ((1 : ℝ) / 36)) :=
          Real.log_le_log (by exact_mod_cast (by have := sf.hP₀; omega : 0 < z)) hz_le2
      _ = Real.log 2 + (1 / 36 : ℝ) * Real.log (X : ℝ) := by
          rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hXp _).ne', Real.log_rpow hXp]
      _ ≤ Real.log (X : ℝ) / (359 / 10 : ℝ) := by
          have hlog2 : Real.log 2 ≤ 1 :=
            (Real.log_le_iff_le_exp (by norm_num)).mpr (le_trans (by norm_num) (Real.add_one_le_exp 1))
          linarith only [hlog2, hlX_big]
  have hlogz_lb : Real.log (X : ℝ) / 36 ≤ Real.log (z : ℝ) := by
    calc Real.log (X : ℝ) / 36 = Real.log ((X : ℝ) ^ ((1 : ℝ) / 36)) := by rw [Real.log_rpow hXp]; ring
      _ ≤ Real.log (z : ℝ) := Real.log_le_log (Real.rpow_pos_of_pos hXp _) hz_ge_r
  have hVz_lb : cV1 / (Real.log (X : ℝ)) ^ 7 ≤ V7 sf.P₀ z := by
    have h1 := (hV_ord z (lt_of_lt_of_le hz0_ge hz0_le_z)).1
    have hlogz_le_X : Real.log (z : ℝ) ≤ Real.log (X : ℝ) := by linarith only [hlogz_ub, hlX]
    have hlogz_pos : 0 < Real.log (z : ℝ) := by linarith only [hlogz_lb, hlX]
    have hpow : (Real.log (z : ℝ)) ^ 7 ≤ (Real.log (X : ℝ)) ^ 7 :=
      pow_le_pow_left₀ hlogz_pos.le hlogz_le_X 7
    exact (div_le_div_of_nonneg_left hcV1p.le (pow_pos hlogz_pos 7) hpow).trans h1
  -- Step 1: Exact Buchstab + Exact V7 telescoping + Exact CRT IE at z₀:
  have hbuch := buchstab_card_eq sf (X := X) hz0_ge hz0_le_z
  have htele := V7_telescope hz0_ge hz0_le_z
  have hie := exact_crt_ie sf X z₀
  -- Step 2: Bound 8^z₀ <= (1/10000) * X * V7 sf.P₀ z
  have h8z0_le : (8 : ℝ) ^ z₀ ≤ (1 / 10000 : ℝ) * (X : ℝ) * V7 sf.P₀ z := by
    have h8pow : (8 : ℝ) ^ z₀ ≤ (X : ℝ) ^ ((1 : ℝ) / 2) := by
      have hlog8 : Real.log 8 ≤ 3 := by
        have : (8 : ℝ) ≤ Real.exp 3 := by
          have h1 : (2 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) (Real.add_one_le_exp 1)
          have h3 : (2 : ℝ) ^ 3 ≤ Real.exp 3 := by
            rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
            exact pow_le_pow_left₀ (by norm_num) h1 3
          linarith [show (2 : ℝ) ^ 3 = 8 by norm_num]
        exact (Real.log_le_iff_le_exp (by norm_num)).mpr this
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hXp]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hstep : (X : ℝ) ^ ((1 : ℝ) / 2) ≤ (1 / 10000 : ℝ) * (X : ℝ) * (cV1 / (Real.log (X : ℝ)) ^ 7) := by
      have hmul : (X : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log (X : ℝ)) ^ 7 ≤ cV1 / 10000 :=
        herr_ie.trans (div_le_div_of_nonneg_left hcV1p.le (by norm_num) (by norm_num))
      rw [Real.rpow_neg hXp.le, inv_mul_eq_div, div_le_iff₀ (Real.rpow_pos_of_pos hXp _)] at hmul
      have hXeq : (X : ℝ) = (X : ℝ) ^ ((1 : ℝ) / 2) * (X : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add hXp]; norm_num
      have hpos7 : 0 < (Real.log (X : ℝ)) ^ 7 := pow_pos hlX 7
      have : (X : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (X : ℝ)) ^ 7 ≤ (1 / 10000 : ℝ) * (X : ℝ) * cV1 := by
        calc (X : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (X : ℝ)) ^ 7
            ≤ (X : ℝ) ^ ((1 : ℝ) / 2) * ((cV1 / 10000) * (X : ℝ) ^ ((1 : ℝ) / 2)) := by gcongr
          _ = (1 / 10000 : ℝ) * ((X : ℝ) ^ ((1 : ℝ) / 2) * (X : ℝ) ^ ((1 : ℝ) / 2)) * cV1 := by ring
          _ = (1 / 10000 : ℝ) * (X : ℝ) * cV1 := by rw [← hXeq]
      rw [mul_div_assoc', le_div_iff₀ hpos7]
      exact this
    exact h8pow.trans (hstep.trans (mul_le_mul_of_nonneg_left hVz_lb (by positivity)))
  -- Step 3: For each prime p ∈ [z₀, z), apply hAp with R_p = ⌊sqrt(X / (p * (log X)^25))⌋₊!
  have hterm_ub : ∀ p ∈ (Ico z₀ z).filter Nat.Prime,
      ((((Icc 1 X).filter (fun m => p ∣ sf.F m)).filter
        (fun m => ∀ q : ℕ, q.Prime → sf.P₀ < q → q < p → ¬ q ∣ sf.F m)).card : ℝ) -
      (7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ p ≤
        (7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ z * ((3 / 5 : ℝ) * (Real.log p / Real.log X) ^ 2) +
        C_err * (X : ℝ) / ((p : ℝ) * (Real.log X) ^ 11) := by
    intro p hp
    have hp_lo := (mem_Ico.mp (mem_filter.mp hp).1).1
    have hp_hi := (mem_Ico.mp (mem_filter.mp hp).1).2
    have hpr := (mem_filter.mp hp).2
    have hpP : sf.P₀ < p := lt_of_lt_of_le hz0_ge hp_lo
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hpr.pos
    have hlogp_ge : Real.log (Real.log (X : ℝ) / 40) ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by positivity) (hz0_lb.trans (by exact_mod_cast hp_lo))
    have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hpr.one_lt)
    have hlogp_le_z : Real.log (p : ℝ) ≤ Real.log (z : ℝ) :=
      Real.log_le_log hp_pos (by exact_mod_cast hp_hi.le)
    set D_p : ℝ := (X : ℝ) / ((p : ℝ) * (Real.log (X : ℝ)) ^ 25)
    set R_p : ℕ := ⌊Real.sqrt D_p⌋₊
    have hp_le_X14 : (p : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 4) := by
      calc (p : ℝ) ≤ (z : ℝ) := by exact_mod_cast hp_hi.le
        _ ≤ (X : ℝ) ^ ((1 : ℝ) / 36) + 1 := hz_le_r
        _ ≤ 2 * (X : ℝ) ^ ((1 : ℝ) / 36) := by
            have : (1 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 36) := Real.one_le_rpow hX1 (by norm_num)
            linarith
        _ ≤ (X : ℝ) ^ ((1 : ℝ) / 4) := by
            have hX2 : (2 : ℝ) ≤ (X : ℝ) ^ ((2 : ℝ) / 9) := by
              have h2 : Real.log 2 ≤ (2 / 9 : ℝ) * Real.log (X : ℝ) := by
                have hlog2 : Real.log 2 ≤ 1 :=
                  (Real.log_le_iff_le_exp (by norm_num)).mpr (le_trans (by norm_num) (Real.add_one_le_exp 1))
                linarith only [hlog2, hlX_big]
              rw [Real.rpow_def_of_pos hXp]
              calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
                _ ≤ Real.exp (Real.log (X : ℝ) * (2 / 9)) := Real.exp_le_exp.mpr (by linarith only [h2])
            calc 2 * (X : ℝ) ^ ((1 : ℝ) / 36)
                ≤ (X : ℝ) ^ ((2 : ℝ) / 9) * (X : ℝ) ^ ((1 : ℝ) / 36) :=
                  mul_le_mul_of_nonneg_right hX2 (Real.rpow_nonneg hXp.le _)
              _ = (X : ℝ) ^ ((2 : ℝ) / 9 + 1 / 36) := (Real.rpow_add hXp _ _).symm
              _ = (X : ℝ) ^ ((1 : ℝ) / 4) := by congr 1; norm_num
    have hDp_ge : (100 : ℝ) ≤ D_p := by
      dsimp [D_p]
      calc (100 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 4) / (Real.log (X : ℝ)) ^ 25 := hR_big
        _ ≤ ((X : ℝ) / (X : ℝ) ^ ((1 : ℝ) / 4)) / (Real.log (X : ℝ)) ^ 25 := by
            gcongr
            rw [le_div_iff₀ (Real.rpow_pos_of_pos hXp _), ← Real.rpow_add hXp]
            have : (X : ℝ) ^ ((1 : ℝ) / 4 + 1 / 4) ≤ (X : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
            simpa using this
        _ = (X : ℝ) / ((X : ℝ) ^ ((1 : ℝ) / 4) * (Real.log (X : ℝ)) ^ 25) := by rw [div_div]
        _ ≤ (X : ℝ) / ((p : ℝ) * (Real.log (X : ℝ)) ^ 25) := by gcongr
    have hsqrt_ge : (10 : ℝ) ≤ Real.sqrt D_p := by
      rw [show (10 : ℝ) = Real.sqrt 100 by norm_num]
      exact Real.sqrt_le_sqrt hDp_ge
    have hRp_ge2 : 2 ≤ R_p := by
      have : (9 : ℝ) ≤ (R_p : ℝ) := by linarith [Nat.lt_floor_add_one (Real.sqrt D_p)]
      have : 9 ≤ R_p := by exact_mod_cast this
      omega
    have hRp_ub : (R_p : ℝ) ≤ Real.sqrt D_p := Nat.floor_le (Real.sqrt_nonneg D_p)
    have hRp_lb : Real.sqrt D_p / 2 ≤ (R_p : ℝ) := by linarith [Nat.lt_floor_add_one (Real.sqrt D_p)]
    have hRp_le_X : (R_p : ℝ) ≤ (X : ℝ) := by
      have hDp_le : D_p ≤ (X : ℝ) := by
        dsimp [D_p]
        refine div_le_self hXp.le ?_
        have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.one_lt.le
        have h2 : (1 : ℝ) ≤ (Real.log (X : ℝ)) ^ 25 := one_le_pow₀ (by linarith only [hlX_big])
        nlinarith only [h1, h2]
      calc (R_p : ℝ) ≤ Real.sqrt D_p := hRp_ub
        _ ≤ Real.sqrt (X : ℝ) := Real.sqrt_le_sqrt hDp_le
        _ ≤ (X : ℝ) := by rw [Real.sqrt_le_left hXp.le]; nlinarith only [hX1]
    set t : ℝ := 2 * Real.log (R_p : ℝ) / Real.log (p : ℝ)
    have h2logRp_lb : (998 / 1000 : ℝ) * Real.log (X : ℝ) - Real.log (p : ℝ) ≤ 2 * Real.log (R_p : ℝ) := by
      have h1 : Real.log (Real.sqrt D_p / 2) ≤ Real.log (R_p : ℝ) :=
        Real.log_le_log (by positivity) hRp_lb
      rw [Real.log_div (Real.sqrt_pos.mpr (by linarith only [hDp_ge])).ne' (by norm_num),
          Real.log_sqrt (by linarith only [hDp_ge])] at h1
      have hlogDp : Real.log D_p = Real.log (X : ℝ) - Real.log (p : ℝ) - 25 * Real.log (Real.log (X : ℝ)) := by
        dsimp [D_p]
        rw [Real.log_div hXp.ne' (by positivity), Real.log_mul hp_pos.ne' (pow_pos hlX 25).ne', Real.log_pow]
        ring
      have hlog2 : Real.log 2 ≤ 1 :=
        (Real.log_le_iff_le_exp (by norm_num)).mpr (le_trans (by norm_num) (Real.add_one_le_exp 1))
      have hll_nn : 0 ≤ Real.log (Real.log (X : ℝ)) := Real.log_nonneg (by linarith only [hlX_big])
      linarith only [h1, hlog_rat, hlogDp, hlog2, hll_nn]
    have ht_ge : (69 / 2 : ℝ) ≤ t := by
      dsimp [t]
      rw [le_div_iff₀ hlogp_pos]
      have h1 : Real.log (p : ℝ) ≤ Real.log (X : ℝ) / (359 / 10 : ℝ) := hlogp_le_z.trans hlogz_ub
      linarith only [h2logRp_lb, h1, hlX]
    set err := Real.exp (7 * EinUb (13 / 10) + C_rk / Real.log (p : ℝ) - (13 / 10) * Real.log (R_p : ℝ) / Real.log (p : ℝ))
    have hCrk_small : C_rk / Real.log (p : ℝ) ≤ 1 / 5 := by
      rw [div_le_iff₀ hlogp_pos]
      have h1 : C_rk / (1 / 5 : ℝ) ≤ Real.log (p : ℝ) := (le_max_left _ _).trans (hz0_log.trans hlogp_ge)
      linarith only [h1]
    have herr_ub : err ≤ Real.exp ((27 / 2 : ℝ) - (13 / 20 : ℝ) * t) := by
      dsimp [err, t]
      apply Real.exp_le_exp.mpr
      have hrew : (13 / 10 : ℝ) * Real.log (R_p : ℝ) / Real.log (p : ℝ) =
          (13 / 20 : ℝ) * (2 * Real.log (R_p : ℝ) / Real.log (p : ℝ)) := by ring
      linarith only [hEin13, hCrk_small, hrew]
    have herr_lt_half : err ≤ 1 / 2 := by
      have hk := buchstab_kernel_bound ht_ge
      have h1 : (1 : ℝ) ≤ (t / 34) ^ 7 * t ^ 2 := by
        have h34 : (69 / 2 / 34 : ℝ) ^ 7 * (69 / 2 : ℝ) ^ 2 ≥ 1000 := by norm_num
        have hmono1 : (69 / 2 / 34 : ℝ) ^ 7 ≤ (t / 34) ^ 7 := pow_le_pow_left₀ (by norm_num) (by linarith only [ht_ge]) 7
        have hmono2 : (69 / 2 : ℝ) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by norm_num) ht_ge 2
        nlinarith only [h34, mul_le_mul hmono1 hmono2 (by norm_num) (by positivity)]
      have hexp_le : Real.exp ((27 / 2 : ℝ) - (13 / 20 : ℝ) * t) ≤ 9 / 50 := by
        nlinarith only [hk, h1, Real.exp_pos ((27 / 2 : ℝ) - (13 / 20 : ℝ) * t)]
      linarith only [herr_ub, hexp_le]
    have hsel_p := hAp X p p R_p hpP le_rfl hpr hRp_ge2 (by linarith only [herr_lt_half])
    have hVrat_p : V7 sf.P₀ p / V7 sf.P₀ z ≤ (3 / 2 : ℝ) * (t / 34) ^ 7 := by
      have hr := hV_rat p z hpP hp_hi.le
      have hexp_15 : Real.exp (CV_rat / Real.log (p : ℝ)) ≤ 3 / 2 := by
        have h1 : CV_rat / Real.log (3 / 2 : ℝ) ≤ Real.log (p : ℝ) :=
          (le_max_right _ _).trans (hz0_log.trans hlogp_ge)
        have h2 : CV_rat / Real.log (p : ℝ) ≤ Real.log (3 / 2 : ℝ) := by
          rw [div_le_iff₀ hlogp_pos]
          have hlog15 : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
          have := mul_le_mul_of_nonneg_left h1 hlog15.le
          rwa [mul_div_cancel₀ _ hlog15.ne'] at this
        calc Real.exp (CV_rat / Real.log (p : ℝ))
            ≤ Real.exp (Real.log (3 / 2 : ℝ)) := Real.exp_le_exp.mpr h2
          _ = 3 / 2 := Real.exp_log (by norm_num)
      have hlogz_div : Real.log (z : ℝ) / Real.log (p : ℝ) ≤ t / 34 := by
        dsimp [t]
        rw [div_div, div_le_div_iff₀ hlogp_pos (by positivity)]
        have h1 : Real.log (p : ℝ) ≤ Real.log (X : ℝ) / (359 / 10 : ℝ) := hlogp_le_z.trans hlogz_ub
        have h3 : 34 * Real.log (z : ℝ) ≤ 2 * Real.log (R_p : ℝ) := by linarith only [hlogz_ub, h1, h2logRp_lb, hlX]
        have h4 := mul_le_mul_of_nonneg_right h3 hlogp_pos.le
        linarith only [h4]
      calc V7 sf.P₀ p / V7 sf.P₀ z
          ≤ Real.exp (CV_rat / Real.log (p : ℝ)) * (Real.log (z : ℝ) / Real.log (p : ℝ)) ^ 7 := hr
        _ ≤ (3 / 2 : ℝ) * (t / 34) ^ 7 :=
            mul_le_mul hexp_15 (pow_le_pow_left₀ (by positivity) hlogz_div 7) (by positivity) (by norm_num)
    have hVpos_z := V7_pos (w := z) sf.hP₀
    have hexcess :
        ((7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ p) / (1 - err) - (7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ p ≤
          (7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ z * ((3 / 5 : ℝ) * (Real.log (p : ℝ) / Real.log (X : ℝ)) ^ 2) := by
      have h1 : ((7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ p) / (1 - err) - (7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ p =
          (7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ z * ((V7 sf.P₀ p / V7 sf.P₀ z) * (err / (1 - err))) := by
        have h1m : 1 - err ≠ 0 := by linarith only [herr_lt_half]
        have hVz0 := hVpos_z.ne'
        field_simp; ring
      rw [h1]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have herr_frac : err / (1 - err) ≤ 2 * Real.exp ((27 / 2 : ℝ) - (13 / 20 : ℝ) * t) := by
        rw [div_le_iff₀ (by linarith only [herr_lt_half])]
        nlinarith only [herr_ub, herr_lt_half, Real.exp_pos ((27 / 2 : ℝ) - (13 / 20 : ℝ) * t)]
      have ht_inv_ub : (1 / t) ^ 2 ≤ (107 / 100 : ℝ) * (Real.log (p : ℝ) / Real.log (X : ℝ)) ^ 2 := by
        have h2logRp_ge : (97 / 100 : ℝ) * Real.log (X : ℝ) ≤ 2 * Real.log (R_p : ℝ) := by
          have : Real.log (p : ℝ) ≤ Real.log (X : ℝ) / (359 / 10 : ℝ) := hlogp_le_z.trans hlogz_ub
          linarith only [h2logRp_lb, this, hlX]
        have ht_ge_ratio : (97 / 100 : ℝ) * (Real.log (X : ℝ) / Real.log (p : ℝ)) ≤ t := by
          dsimp [t]
          rw [mul_div_assoc', div_le_div_iff_of_pos_right hlogp_pos]
          exact h2logRp_ge
        have hle1 : 1 / t ≤ (100 / 97 : ℝ) * (Real.log (p : ℝ) / Real.log (X : ℝ)) := by
          have hpos_rhs : 0 < (97 / 100 : ℝ) * (Real.log (X : ℝ) / Real.log (p : ℝ)) := by positivity
          have hinv := one_div_le_one_div_of_le hpos_rhs ht_ge_ratio
          calc 1 / t ≤ 1 / ((97 / 100 : ℝ) * (Real.log (X : ℝ) / Real.log (p : ℝ))) := hinv
            _ = (100 / 97 : ℝ) * (Real.log (p : ℝ) / Real.log (X : ℝ)) := by
                have hlX0 := hlX.ne'
                have hlp0 := hlogp_pos.ne'
                field_simp
        have hsq : (1 / t) ^ 2 ≤ ((100 / 97 : ℝ) * (Real.log (p : ℝ) / Real.log (X : ℝ))) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hle1 2
        calc (1 / t) ^ 2 ≤ (100 / 97 : ℝ) ^ 2 * (Real.log (p : ℝ) / Real.log (X : ℝ)) ^ 2 := by
              simpa [mul_pow] using hsq
          _ ≤ (107 / 100 : ℝ) * (Real.log (p : ℝ) / Real.log (X : ℝ)) ^ 2 := by
              nlinarith only [sq_nonneg (Real.log (p : ℝ) / Real.log (X : ℝ))]
      have hk := buchstab_kernel_bound ht_ge
      calc (V7 sf.P₀ p / V7 sf.P₀ z) * (err / (1 - err))
          ≤ ((3 / 2 : ℝ) * (t / 34) ^ 7) * (2 * Real.exp ((27 / 2 : ℝ) - (13 / 20 : ℝ) * t)) :=
            mul_le_mul hVrat_p herr_frac (div_nonneg (Real.exp_pos _).le (by linarith only [herr_lt_half])) (by positivity)
        _ = 3 * ((t / 34) ^ 7 * t ^ 2 * Real.exp ((27 / 2 : ℝ) - (13 / 20 : ℝ) * t)) * (1 / t) ^ 2 := by
            have ht0 : t ≠ 0 := by linarith only [ht_ge]
            field_simp
        _ ≤ 3 * (9 / 50 : ℝ) * (1 / t) ^ 2 := by
            nlinarith only [hk, sq_nonneg (1 / t)]
        _ = (27 / 50 : ℝ) * (1 / t) ^ 2 := by norm_num
        _ ≤ (27 / 50 : ℝ) * ((107 / 100 : ℝ) * (Real.log (p : ℝ) / Real.log (X : ℝ)) ^ 2) := by
            nlinarith only [ht_inv_ub]
        _ ≤ (3 / 5 : ℝ) * (Real.log (p : ℝ) / Real.log (X : ℝ)) ^ 2 := by
            nlinarith only [sq_nonneg (Real.log (p : ℝ) / Real.log (X : ℝ))]
    have herr_Rp : C_err * (R_p : ℝ) ^ 2 * (Real.log (R_p : ℝ)) ^ 14 ≤
        C_err * (X : ℝ) / ((p : ℝ) * (Real.log (X : ℝ)) ^ 11) := by
      have hRp2 : (R_p : ℝ) ^ 2 ≤ D_p := by
        calc (R_p : ℝ) ^ 2 ≤ (Real.sqrt D_p) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hRp_ub 2
          _ = D_p := Real.sq_sqrt (by linarith only [hDp_ge])
      have hlogRp_le : Real.log (R_p : ℝ) ≤ Real.log (X : ℝ) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < R_p)) hRp_le_X
      calc C_err * (R_p : ℝ) ^ 2 * (Real.log (R_p : ℝ)) ^ 14
          ≤ C_err * D_p * (Real.log (X : ℝ)) ^ 14 := by
            have h1 : (Real.log (R_p : ℝ)) ^ 14 ≤ (Real.log (X : ℝ)) ^ 14 :=
              pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ R_p))) hlogRp_le 14
            have h2 := mul_le_mul hRp2 h1 (by positivity) (by linarith only [hDp_ge])
            have := mul_le_mul_of_nonneg_left h2 hCerr_p.le
            linarith only [this]
        _ = C_err * (X : ℝ) / ((p : ℝ) * (Real.log (X : ℝ)) ^ 11) := by
            dsimp [D_p]; have := hlX.ne'; have := hp_pos.ne'; field_simp
    linarith only [hsel_p, hexcess, herr_Rp]
  have hsum_excess := Finset.sum_le_sum hterm_ub
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum_excess
  have hz2 : 2 ≤ z := by have := sf.hP₀; omega
  have hM1_z : ∑ p ∈ (Ioo 0 z).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log (z : ℝ) + C_m1 := by
    have h := hM1 z hz2
    simpa only [pow_one, Nat.cast_one, div_one, Nat.sub_self, pow_zero, mul_one] using h
  have hsub_z : (Ico z₀ z).filter Nat.Prime ⊆ (Ioo 0 z).filter Nat.Prime := by
    intro p hp; simp only [mem_filter, mem_Ico, mem_Ioo] at hp ⊢
    exact ⟨⟨hp.2.pos, hp.1.2⟩, hp.2⟩
  have hsum_logp_div : ∑ p ∈ (Ico z₀ z).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) ≤
      Real.log (z : ℝ) + C_m1 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub_z ?_) hM1_z
    intro p hp _
    have hpr := (mem_filter.mp hp).2
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)) (Nat.cast_nonneg p)
  have hsum_term1 :
      ∑ p ∈ (Ico z₀ z).filter Nat.Prime,
        (7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ z * ((3 / 5 : ℝ) * (Real.log (p : ℝ) / Real.log (X : ℝ)) ^ 2) ≤
      (45 / 10000 : ℝ) * (X : ℝ) * V7 sf.P₀ z := by
    have hVpos_z := V7_pos (w := z) sf.hP₀
    have hlogz_pos : 0 < Real.log (z : ℝ) := by linarith only [hlogz_lb, hlX]
    have h1 :
        ∑ p ∈ (Ico z₀ z).filter Nat.Prime,
          (7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ z * ((3 / 5 : ℝ) * (Real.log (p : ℝ) / Real.log (X : ℝ)) ^ 2) ≤
        ∑ p ∈ (Ico z₀ z).filter Nat.Prime,
          (((21 / 5 : ℝ) * (X : ℝ) * V7 sf.P₀ z * Real.log (z : ℝ)) / (Real.log (X : ℝ)) ^ 2) *
            (Real.log (p : ℝ) / (p : ℝ)) := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hp_hi := (mem_Ico.mp (mem_filter.mp hp).1).2
      have hpr := (mem_filter.mp hp).2
      have hlp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
      have hlp_le : Real.log (p : ℝ) ≤ Real.log (z : ℝ) :=
        Real.log_le_log (by exact_mod_cast hpr.pos) (by exact_mod_cast hp_hi.le)
      have hsq_le : (Real.log (p : ℝ)) ^ 2 ≤ Real.log (z : ℝ) * Real.log (p : ℝ) := by
        rw [sq]; exact mul_le_mul_of_nonneg_right hlp_le hlp_nn
      have heq1 : (7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ z * ((3 / 5 : ℝ) * (Real.log (p : ℝ) / Real.log (X : ℝ)) ^ 2) =
          ((21 / 5 : ℝ) * (X : ℝ) * V7 sf.P₀ z / ((p : ℝ) * (Real.log (X : ℝ)) ^ 2)) * (Real.log (p : ℝ)) ^ 2 := by
        ring
      have heq2 : (((21 / 5 : ℝ) * (X : ℝ) * V7 sf.P₀ z * Real.log (z : ℝ)) / (Real.log (X : ℝ)) ^ 2) *
            (Real.log (p : ℝ) / (p : ℝ)) =
          ((21 / 5 : ℝ) * (X : ℝ) * V7 sf.P₀ z / ((p : ℝ) * (Real.log (X : ℝ)) ^ 2)) * (Real.log (z : ℝ) * Real.log (p : ℝ)) := by
        ring
      rw [heq1, heq2]
      exact mul_le_mul_of_nonneg_left hsq_le (by positivity)
    rw [← Finset.mul_sum] at h1
    have hcoeff_nn : 0 ≤ ((21 / 5 : ℝ) * (X : ℝ) * V7 sf.P₀ z * Real.log (z : ℝ)) / (Real.log (X : ℝ)) ^ 2 := by
      positivity
    have h2 := h1.trans (mul_le_mul_of_nonneg_left hsum_logp_div hcoeff_nn)
    have hprod_le : Real.log (z : ℝ) * (Real.log (z : ℝ) + C_m1) ≤
        ((45 / 10000 : ℝ) / (21 / 5 : ℝ)) * (Real.log (X : ℝ)) ^ 2 := by
      have h1' : Real.log (z : ℝ) ≤ (10 / 359 : ℝ) * Real.log (X : ℝ) := by linarith only [hlogz_ub]
      have h2' : Real.log (z : ℝ) + C_m1 ≤ (10 / 359 + 1 / 100 : ℝ) * Real.log (X : ℝ) := by
        linarith only [h1', hCm1_le]
      have hmul := mul_le_mul h1' h2' (by linarith only [hlogz_pos, hCm1p]) (by positivity)
      have hconst : (10 / 359 : ℝ) * (10 / 359 + 1 / 100) ≤ (45 / 10000 : ℝ) / (21 / 5 : ℝ) := by norm_num
      calc Real.log (z : ℝ) * (Real.log (z : ℝ) + C_m1)
          ≤ ((10 / 359 : ℝ) * Real.log (X : ℝ)) * ((10 / 359 + 1 / 100 : ℝ) * Real.log (X : ℝ)) := hmul
        _ = ((10 / 359 : ℝ) * (10 / 359 + 1 / 100)) * (Real.log (X : ℝ)) ^ 2 := by ring
        _ ≤ ((45 / 10000 : ℝ) / (21 / 5 : ℝ)) * (Real.log (X : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hconst (sq_nonneg _)
    have h3 : (((21 / 5 : ℝ) * (X : ℝ) * V7 sf.P₀ z * Real.log (z : ℝ)) / (Real.log (X : ℝ)) ^ 2) *
          (Real.log (z : ℝ) + C_m1) ≤ (45 / 10000 : ℝ) * (X : ℝ) * V7 sf.P₀ z := by
      have hlX2 : 0 < (Real.log (X : ℝ)) ^ 2 := sq_pos_of_pos hlX
      rw [show (((21 / 5 : ℝ) * (X : ℝ) * V7 sf.P₀ z * Real.log (z : ℝ)) / (Real.log (X : ℝ)) ^ 2) *
            (Real.log (z : ℝ) + C_m1) =
          ((21 / 5 : ℝ) * (X : ℝ) * V7 sf.P₀ z / (Real.log (X : ℝ)) ^ 2) *
            (Real.log (z : ℝ) * (Real.log (z : ℝ) + C_m1)) by ring]
      calc ((21 / 5 : ℝ) * (X : ℝ) * V7 sf.P₀ z / (Real.log (X : ℝ)) ^ 2) *
              (Real.log (z : ℝ) * (Real.log (z : ℝ) + C_m1))
          ≤ ((21 / 5 : ℝ) * (X : ℝ) * V7 sf.P₀ z / (Real.log (X : ℝ)) ^ 2) *
              (((45 / 10000 : ℝ) / (21 / 5 : ℝ)) * (Real.log (X : ℝ)) ^ 2) :=
            mul_le_mul_of_nonneg_left hprod_le (by positivity)
        _ = (45 / 10000 : ℝ) * (X : ℝ) * V7 sf.P₀ z := by
            have := hlX2.ne'; field_simp
    exact h2.trans h3
  have hsum_term2 :
      ∑ p ∈ (Ico z₀ z).filter Nat.Prime, C_err * (X : ℝ) / ((p : ℝ) * (Real.log (X : ℝ)) ^ 11) ≤
      (1 / 10000 : ℝ) * (X : ℝ) * V7 sf.P₀ z := by
    have hsum_inv_p : ∑ p ∈ (Ico z₀ z).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤ Real.log (X : ℝ) := by
      have hle1 : ∑ p ∈ (Ico z₀ z).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
          ∑ p ∈ (Ico z₀ z).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp_lo := (mem_Ico.mp (mem_filter.mp hp).1).1
        have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
          have := sf.hP₀
          exact_mod_cast (by omega : 3 ≤ p)
        have h1_le_logp : (1 : ℝ) ≤ Real.log (p : ℝ) := by
          rw [Real.le_log_iff_exp_le (by linarith only [hp3])]
          exact le_trans (by linarith [Real.exp_one_lt_d9]) hp3
        exact div_le_div_of_nonneg_right h1_le_logp (by linarith only [hp3])
      linarith only [hle1, hsum_logp_div, hlogz_ub, hCm1_le, hlX]
    have hrew : ∑ p ∈ (Ico z₀ z).filter Nat.Prime, C_err * (X : ℝ) / ((p : ℝ) * (Real.log (X : ℝ)) ^ 11) =
        (C_err * (X : ℝ) / (Real.log (X : ℝ)) ^ 11) * ∑ p ∈ (Ico z₀ z).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
    rw [hrew]
    have hstep1 : (C_err * (X : ℝ) / (Real.log (X : ℝ)) ^ 11) *
          (∑ p ∈ (Ico z₀ z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤
        C_err * (X : ℝ) / (Real.log (X : ℝ)) ^ 10 := by
      calc (C_err * (X : ℝ) / (Real.log (X : ℝ)) ^ 11) *
              (∑ p ∈ (Ico z₀ z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
          ≤ (C_err * (X : ℝ) / (Real.log (X : ℝ)) ^ 11) * Real.log (X : ℝ) :=
            mul_le_mul_of_nonneg_left hsum_inv_p (by positivity)
        _ = C_err * (X : ℝ) / (Real.log (X : ℝ)) ^ 10 := by
            have := hlX.ne'; field_simp
    have hstep2 : C_err * (X : ℝ) / (Real.log (X : ℝ)) ^ 10 ≤
        (1 / 10000 : ℝ) * (X : ℝ) * (cV1 / (Real.log (X : ℝ)) ^ 7) := by
      have herr_sel' : C_err * (Real.log (X : ℝ)) ^ (-3 : ℝ) ≤ cV1 / 10000 :=
        herr_sel.trans (div_le_div_of_nonneg_left hcV1p.le (by norm_num) (by norm_num))
      have hpow_neg3 : (Real.log (X : ℝ)) ^ (-3 : ℝ) = ((Real.log (X : ℝ)) ^ 3)⁻¹ := by
        rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hlX.le, Real.rpow_natCast]
      rw [hpow_neg3] at herr_sel'
      have heq_lhs : C_err * (X : ℝ) / (Real.log (X : ℝ)) ^ 10 =
          (C_err * ((Real.log (X : ℝ)) ^ 3)⁻¹) * ((X : ℝ) / (Real.log (X : ℝ)) ^ 7) := by
        have := hlX.ne'; field_simp
      rw [heq_lhs]
      calc (C_err * ((Real.log (X : ℝ)) ^ 3)⁻¹) * ((X : ℝ) / (Real.log (X : ℝ)) ^ 7)
          ≤ (cV1 / 10000) * ((X : ℝ) / (Real.log (X : ℝ)) ^ 7) :=
            mul_le_mul_of_nonneg_right herr_sel' (by positivity)
        _ = (1 / 10000 : ℝ) * (X : ℝ) * (cV1 / (Real.log (X : ℝ)) ^ 7) := by ring
    exact hstep1.trans (hstep2.trans (mul_le_mul_of_nonneg_left hVz_lb (by positivity)))
  have htele_mul :
      (X : ℝ) * V7 sf.P₀ z₀ - ∑ p ∈ (Ico z₀ z).filter Nat.Prime, (7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ p =
      (X : ℝ) * V7 sf.P₀ z := by
    have h1 : ∑ p ∈ (Ico z₀ z).filter Nat.Prime, (7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ p =
        (X : ℝ) * ∑ p ∈ (Ico z₀ z).filter Nat.Prime, (7 / (p : ℝ)) * V7 sf.P₀ p := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
    rw [h1, ← mul_sub, htele]
  have hVpos_z := V7_pos (w := z) sf.hP₀
  linarith only [hbuch, hie, htele_mul, hsum_excess, hsum_term1, hsum_term2, h8z0_le, mul_pos hXp hVpos_z]

/-! ### Part 4: Reusable Richert bin upper bound + 8 verified rational bins -/

set_option maxHeartbeats 800000 in
lemma richert_bin_bound (sf : ShiftedForms)
    {t₀ t₁ c gap_r err_r F_r L_r : ℝ}
    (ht₀ : 1 / 36 ≤ t₀) (ht01 : t₀ < t₁) (ht₁ : t₁ ≤ 20 / 37)
    (hc : 0 < c) (hc16 : c < 16)
    (hgap : 0 < gap_r)
    (hEin_gap : 7 * (c + c ^ 2 / 4 + c ^ 3 / 18 + c ^ 4 / 96 + ((1 - c / 16) ^ 16)⁻¹ * c ^ 5 / 600) +
        1 / 50 - (c / 2) * (36 * (1 - t₁) - 1 / 20) ≤ -gap_r)
    (herr_pos : 0 < err_r) (herr_lt1 : err_r < 1)
    (herr_cert : 1 / err_r ≤ ∑ i ∈ range 13, gap_r ^ i / (i.factorial : ℝ))
    (hF : (1 - err_r)⁻¹ ≤ F_r)
    (hL_nn : 0 ≤ L_r)
    (hL_cert : t₁ / t₀ ≤ ∑ i ∈ range 11, L_r ^ i / (i.factorial : ℝ)) :
    ∀ᶠ X : ℕ in atTop,
      let z := ⌈(X : ℝ) ^ ((1 : ℝ) / 36)⌉₊
      ∑ p ∈ (Ico ⌈(X : ℝ) ^ t₀⌉₊ ⌈(X : ℝ) ^ t₁⌉₊).filter Nat.Prime,
        (1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ)) *
          (((SSet sf X z).filter (fun m => p ∣ sf.F m)).card : ℝ) ≤
      (7 * F_r * (L_r - (37 / 20 : ℝ) * (t₁ - t₀)) + 1 / 1000) * (X : ℝ) * V7 sf.P₀ z := by
  obtain ⟨C_rk, C_err, hCrk_p, hCerr_p, hAp⟩ := selberg_Ap_upper sf c hc
  obtain ⟨C_bin, hCbin_p, hBin⟩ := sum_richert_bin_le (by linarith : (0 : ℝ) < t₀) ht01 (by linarith : t₁ < 1) (by norm_num : (0 : ℝ) < 37 / 20)
  obtain ⟨cV1, _, hcV1p, _, hV_ord⟩ := (V7_asymptotics sf.P₀ sf.hP₀).1
  obtain ⟨C_m1, hCm1p, hM1⟩ := sum_log_pow_div_p_le 1 (by norm_num)
  have hF_pos : 0 < F_r := lt_of_lt_of_le (inv_pos.mpr (by linarith)) hF
  have hEin_c : 7 * EinUb c + 1 / 50 - (c / 2) * (36 * (1 - t₁) - 1 / 20) ≤ -gap_r := by
    have hexp_c := exp_le_inv_one_sub_div16 hc.le hc16
    unfold EinUb
    have hc5 : 0 ≤ c ^ 5 / 600 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hexp_c hc5]
  have hexp_gap : Real.exp (-gap_r) ≤ err_r := exp_neg_le_of_taylor12 hgap.le herr_pos herr_cert
  have hlog_ratio : Real.log (t₁ / t₀) ≤ L_r := log_le_of_taylor10 (div_pos (by linarith) (by linarith)) hL_nn hL_cert
  have hlogX : Filter.Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev_log_rat : ∀ᶠ X : ℕ in atTop,
      26 * Real.log (Real.log (X : ℝ)) + 50 ≤ (1 / 1000 : ℝ) * Real.log (X : ℝ) := by
    have hlo := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).bound (by norm_num : (0 : ℝ) < 1 / 52000)
    filter_upwards [hlogX.eventually hlo, hlogX.eventually_ge_atTop 100000] with X hX hXbig
    have hlX : 0 < Real.log (X : ℝ) := by linarith
    have hllX : 0 ≤ Real.log (Real.log (X : ℝ)) := Real.log_nonneg (by linarith)
    change ‖Real.log (Real.log (X : ℝ))‖ ≤ (1 / 52000) * ‖(Real.log (X : ℝ)) ^ (1 : ℝ)‖ at hX
    rw [Real.rpow_one, Real.norm_of_nonneg hllX, Real.norm_of_nonneg hlX.le] at hX
    linarith
  have hev_big : ∀ᶠ X : ℕ in atTop,
      (sf.P₀ : ℝ) + 10 ≤ (X : ℝ) ^ ((1 : ℝ) / 36) ∧
      (100 : ℝ) ≤ (X : ℝ) ^ (1 - t₁) / (Real.log (X : ℝ)) ^ 25 ∧
      C_rk / (1 / 50 : ℝ) ≤ (1 / 36 : ℝ) * Real.log (X : ℝ) ∧
      F_r * C_bin / Real.log (X : ℝ) ≤ 1 / 2000 ∧
      2 * C_err * (Real.log (X : ℝ)) ^ (-3 : ℝ) ≤ cV1 / 2000 ∧
      C_m1 ≤ Real.log (X : ℝ) ∧
      (10000 : ℝ) ≤ Real.log (X : ℝ) := by
    have h1 := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 36)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop ((sf.P₀ : ℝ) + 10)
    have h2 : ∀ᶠ X : ℕ in atTop, (100 : ℝ) ≤ (X : ℝ) ^ (1 - t₁) / (Real.log (X : ℝ)) ^ 25 := by
      have hlo := ((isLittleO_log_rpow_rpow_atTop (25 : ℝ) (by linarith : (0 : ℝ) < 1 - t₁)).tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
      filter_upwards [hlo.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100)), eventually_ge_atTop 100] with X hX hX100
      have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
      have hlX : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
      have hX' : (Real.log (X : ℝ)) ^ (25 : ℕ) / (X : ℝ) ^ (1 - t₁) < 1 / 100 := by
        dsimp only [Function.comp_apply] at hX
        simpa only [show (25 : ℝ) = ((25 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] using hX
      have hpos1 : 0 < (X : ℝ) ^ (1 - t₁) := Real.rpow_pos_of_pos hXp _
      have hpos2 : 0 < (Real.log (X : ℝ)) ^ 25 := pow_pos hlX 25
      rw [div_lt_iff₀ hpos1] at hX'
      rw [le_div_iff₀ hpos2]
      linarith
    have h3 := hlogX.eventually_ge_atTop (36 * (C_rk / (1 / 50)))
    have h4 := hlogX.eventually_ge_atTop (2000 * F_r * C_bin)
    have h5 : ∀ᶠ X : ℕ in atTop, 2 * C_err * (Real.log (X : ℝ)) ^ (-3 : ℝ) ≤ cV1 / 2000 := by
      have ht := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)).comp hlogX).const_mul (2 * C_err)
      have ht' : Tendsto (fun X : ℕ => 2 * C_err * (Real.log (X : ℝ)) ^ (-3 : ℝ)) atTop (nhds 0) := by
        simpa using ht
      exact (ht'.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < cV1 / 2000))).mono fun _ h => h.le
    have h6 := hlogX.eventually_ge_atTop C_m1
    have h7 := hlogX.eventually_ge_atTop 10000
    filter_upwards [h1, h2, h3, h4, h5, h6, h7] with X a b c' d e f g
    refine ⟨a, b, by linarith, ?_, e, f, g⟩
    rw [div_le_iff₀ (by linarith)]
    linarith
  filter_upwards [hBin, hev_log_rat, hev_big, eventually_ge_atTop 1000] with X hBinX hlog_rat ⟨hz_gtP, hDp_big, hCrk_big, hCbin_sm, hCerr_sm, hCm1_le, hlX_big⟩ hX1000
  intro z
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) < X := by exact_mod_cast (by omega : 1 < X)
  have hlX : 0 < Real.log (X : ℝ) := by linarith
  have hzP : sf.P₀ < z := by
    have : (sf.P₀ : ℝ) + 10 ≤ (z : ℝ) := hz_gtP.trans (Nat.le_ceil _)
    have : sf.P₀ + 10 ≤ z := by exact_mod_cast this
    omega
  have hz_ge_r : (X : ℝ) ^ ((1 : ℝ) / 36) ≤ (z : ℝ) := Nat.le_ceil _
  have hz_le_r : (z : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 36) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hlogz_lb : (1 / 36 : ℝ) * Real.log (X : ℝ) ≤ Real.log (z : ℝ) := by
    calc (1 / 36 : ℝ) * Real.log (X : ℝ) = Real.log ((X : ℝ) ^ ((1 : ℝ) / 36)) := by rw [Real.log_rpow hXp]
      _ ≤ Real.log (z : ℝ) := Real.log_le_log (Real.rpow_pos_of_pos hXp _) hz_ge_r
  have hlogz_ub : Real.log (z : ℝ) ≤ (1 / 36 : ℝ) * Real.log (X : ℝ) + 1 := by
    have hz_le2 : (z : ℝ) ≤ 2 * (X : ℝ) ^ ((1 : ℝ) / 36) := by
      have : (1 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 36) := Real.one_le_rpow hX1.le (by norm_num)
      linarith
    have hlog2 : Real.log 2 ≤ 1 :=
      (Real.log_le_iff_le_exp (by norm_num)).mpr (le_trans (by norm_num) (Real.add_one_le_exp 1))
    calc Real.log (z : ℝ) ≤ Real.log (2 * (X : ℝ) ^ ((1 : ℝ) / 36)) :=
          Real.log_le_log (by exact_mod_cast (by have := sf.hP₀; omega : 0 < z)) hz_le2
      _ = Real.log 2 + (1 / 36 : ℝ) * Real.log (X : ℝ) := by
          rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hXp _).ne', Real.log_rpow hXp]
      _ ≤ (1 / 36 : ℝ) * Real.log (X : ℝ) + 1 := by linarith
  have hlogz_pos : 0 < Real.log (z : ℝ) := by linarith
  have hVpos_z := V7_pos (w := z) sf.hP₀
  have hVz_lb : cV1 / (Real.log (X : ℝ)) ^ 7 ≤ V7 sf.P₀ z := by
    have h1 := (hV_ord z hzP).1
    have hlogz_le_X : Real.log (z : ℝ) ≤ Real.log (X : ℝ) := by linarith only [hlogz_ub, hlX_big]
    have hpow : (Real.log (z : ℝ)) ^ 7 ≤ (Real.log (X : ℝ)) ^ 7 :=
      pow_le_pow_left₀ hlogz_pos.le hlogz_le_X 7
    exact (div_le_div_of_nonneg_left hcV1p.le (pow_pos hlogz_pos 7) hpow).trans h1
  -- For every prime p ∈ [⌈X^t₀⌉₊, ⌈X^t₁⌉₊), bound S_p(z) using hAp!
  have hSp_ub : ∀ p ∈ (Ico ⌈(X : ℝ) ^ t₀⌉₊ ⌈(X : ℝ) ^ t₁⌉₊).filter Nat.Prime,
      (1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ)) *
        (((SSet sf X z).filter (fun m => p ∣ sf.F m)).card : ℝ) ≤
      F_r * (X : ℝ) * V7 sf.P₀ z * ((1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ)) * (7 / (p : ℝ))) +
      C_err * (X : ℝ) / ((p : ℝ) * (Real.log (X : ℝ)) ^ 11) := by
    intro p hp
    have hp_lo := (mem_Ico.mp (mem_filter.mp hp).1).1
    have hp_hi := (mem_Ico.mp (mem_filter.mp hp).1).2
    have hpr := (mem_filter.mp hp).2
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hpr.pos
    have hz_le_p : z ≤ p := by
      have h1 : ⌈(X : ℝ) ^ ((1 : ℝ) / 36)⌉₊ ≤ ⌈(X : ℝ) ^ t₀⌉₊ :=
        Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le hX1.le ht₀)
      exact h1.trans hp_lo
    have hp_lt_Xt1 : (p : ℝ) < (X : ℝ) ^ t₁ := Nat.lt_ceil.mp hp_hi
    have hlogp_lt : Real.log (p : ℝ) < t₁ * Real.log (X : ℝ) := by
      calc Real.log (p : ℝ) < Real.log ((X : ℝ) ^ t₁) := Real.log_lt_log hp_pos hp_lt_Xt1
        _ = t₁ * Real.log (X : ℝ) := Real.log_rpow hXp t₁
    have hwt_nn : 0 ≤ 1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ) := by
      have h1 : (37 / 20 : ℝ) * Real.log (p : ℝ) ≤ (37 / 20 : ℝ) * (t₁ * Real.log (X : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogp_lt.le (by norm_num)
      have h2 : (37 / 20 : ℝ) * t₁ ≤ 1 := by linarith
      have h3 : (37 / 20 : ℝ) * Real.log (p : ℝ) ≤ Real.log (X : ℝ) := by nlinarith
      have h4 : (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ) ≤ 1 :=
        (div_le_one hlX).mpr h3
      linarith
    have hwt_le1 : 1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ) ≤ 1 := by
      have hlp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
      have : 0 ≤ (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ) := by positivity
      linarith
    set D_p : ℝ := (X : ℝ) / ((p : ℝ) * (Real.log (X : ℝ)) ^ 25)
    set R_p : ℕ := ⌊Real.sqrt D_p⌋₊
    have hDp_ge : (100 : ℝ) ≤ D_p := by
      dsimp [D_p]
      calc (100 : ℝ) ≤ (X : ℝ) ^ (1 - t₁) / (Real.log (X : ℝ)) ^ 25 := hDp_big
        _ = (X : ℝ) / ((X : ℝ) ^ t₁ * (Real.log (X : ℝ)) ^ 25) := by
            rw [Real.rpow_sub hXp, Real.rpow_one, div_div]
        _ ≤ (X : ℝ) / ((p : ℝ) * (Real.log (X : ℝ)) ^ 25) := by gcongr
    have hsqrt_ge : (10 : ℝ) ≤ Real.sqrt D_p := by
      rw [show (10 : ℝ) = Real.sqrt 100 by norm_num]
      exact Real.sqrt_le_sqrt hDp_ge
    have hRp_ge2 : 2 ≤ R_p := by
      have : (9 : ℝ) ≤ (R_p : ℝ) := by linarith [Nat.lt_floor_add_one (Real.sqrt D_p)]
      have : 9 ≤ R_p := by exact_mod_cast this
      omega
    have hRp_ub : (R_p : ℝ) ≤ Real.sqrt D_p := Nat.floor_le (Real.sqrt_nonneg D_p)
    have hRp_lb : Real.sqrt D_p / 2 ≤ (R_p : ℝ) := by linarith [Nat.lt_floor_add_one (Real.sqrt D_p)]
    have hRp_le_X : (R_p : ℝ) ≤ (X : ℝ) := by
      have hDp_le : D_p ≤ (X : ℝ) := by
        dsimp [D_p]
        refine div_le_self hXp.le ?_
        have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.one_lt.le
        have h2 : (1 : ℝ) ≤ (Real.log (X : ℝ)) ^ 25 := one_le_pow₀ (by linarith only [hlX_big])
        nlinarith only [h1, h2]
      calc (R_p : ℝ) ≤ Real.sqrt D_p := hRp_ub
        _ ≤ Real.sqrt (X : ℝ) := Real.sqrt_le_sqrt hDp_le
        _ ≤ (X : ℝ) := by rw [Real.sqrt_le_left hXp.le]; nlinarith only [hX1]
    -- Lower bound 2 * log R_p / log z >= 36 * (1 - t₁) - 1/20
    have h2logRp_lb : (1 - t₁) * Real.log (X : ℝ) - 25 * Real.log (Real.log (X : ℝ)) - 2 ≤ 2 * Real.log (R_p : ℝ) := by
      have h1 : Real.log (Real.sqrt D_p / 2) ≤ Real.log (R_p : ℝ) :=
        Real.log_le_log (by positivity) hRp_lb
      rw [Real.log_div (Real.sqrt_pos.mpr (by linarith only [hDp_ge])).ne' (by norm_num),
          Real.log_sqrt (by linarith only [hDp_ge])] at h1
      have hlogDp : Real.log D_p = Real.log (X : ℝ) - Real.log (p : ℝ) - 25 * Real.log (Real.log (X : ℝ)) := by
        dsimp [D_p]
        rw [Real.log_div hXp.ne' (by positivity), Real.log_mul hp_pos.ne' (pow_pos hlX 25).ne', Real.log_pow]
        ring
      have hlog2 : Real.log 2 ≤ 1 :=
        (Real.log_le_iff_le_exp (by norm_num)).mpr (le_trans (by norm_num) (Real.add_one_le_exp 1))
      linarith only [h1, hlogp_lt, hlogDp, hlog2]
    have hratio_lb : 36 * (1 - t₁) - 1 / 20 ≤ 2 * Real.log (R_p : ℝ) / Real.log (z : ℝ) := by
      rw [le_div_iff₀ hlogz_pos]
      have h36_nn : 0 ≤ 36 * (1 - t₁) - 1 / 20 := by linarith only [ht₁]
      have h1 : (36 * (1 - t₁) - 1 / 20) * Real.log (z : ℝ) ≤
          (36 * (1 - t₁) - 1 / 20) * ((1 / 36 : ℝ) * Real.log (X : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hlogz_ub h36_nn
      have h2 : (36 * (1 - t₁) - 1 / 20) * ((1 / 36 : ℝ) * Real.log (X : ℝ) + 1) ≤
          (1 - t₁) * Real.log (X : ℝ) - (1 / 1000 : ℝ) * Real.log (X : ℝ) + 36 := by
        nlinarith only [hlX, ht₁, ht₀, ht01]
      have hll_nn : 0 ≤ Real.log (Real.log (X : ℝ)) := Real.log_nonneg (by linarith only [hlX_big])
      linarith only [h1, h2, h2logRp_lb, hlog_rat, hll_nn]
    have hCrk_sm : C_rk / Real.log (z : ℝ) ≤ 1 / 50 := by
      rw [div_le_iff₀ hlogz_pos]
      have h1 : C_rk / (1 / 50 : ℝ) ≤ Real.log (z : ℝ) := hCrk_big.trans hlogz_lb
      linarith only [h1]
    set err := Real.exp (7 * EinUb c + C_rk / Real.log (z : ℝ) - c * Real.log (R_p : ℝ) / Real.log (z : ℝ))
    have herr_le : err ≤ err_r := by
      have hexp_le : err ≤ Real.exp (-gap_r) := by
        dsimp [err]
        apply Real.exp_le_exp.mpr
        have h3 : (c / 2) * (36 * (1 - t₁) - 1 / 20) ≤ c * Real.log (R_p : ℝ) / Real.log (z : ℝ) := by
          have := mul_le_mul_of_nonneg_left hratio_lb (by positivity : (0 : ℝ) ≤ c / 2)
          have heq : (c / 2) * (2 * Real.log (R_p : ℝ) / Real.log (z : ℝ)) =
              c * Real.log (R_p : ℝ) / Real.log (z : ℝ) := by ring
          linarith only [this, heq]
        linarith only [hEin_c, hCrk_sm, h3]
      exact hexp_le.trans hexp_gap
    have hsel_p := hAp X z p R_p hzP hz_le_p hpr hRp_ge2 (lt_of_le_of_lt herr_le herr_lt1)
    have hcomm : ((SSet sf X z).filter (fun m => p ∣ sf.F m)).card =
        (((Icc 1 X).filter (fun m => p ∣ sf.F m)).filter
          (fun m => ∀ q : ℕ, q.Prime → sf.P₀ < q → q < z → ¬ q ∣ sf.F m)).card := by
      unfold Erdos946Sieve1.SSet; rw [Finset.filter_comm]
    rw [hcomm]
    have hmain_ub : ((7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ z) / (1 - err) ≤
        F_r * (X : ℝ) * V7 sf.P₀ z * (7 / (p : ℝ)) := by
      have h1 : (1 - err)⁻¹ ≤ F_r :=
        (inv_le_inv₀ (by linarith only [herr_le, herr_lt1]) (by linarith only [herr_lt1])).mpr (by linarith only [herr_le]) |>.trans hF
      rw [div_eq_mul_inv]
      have hnn : 0 ≤ (7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ z := by positivity
      calc ((7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ z) * (1 - err)⁻¹
          ≤ ((7 / (p : ℝ)) * (X : ℝ) * V7 sf.P₀ z) * F_r := mul_le_mul_of_nonneg_left h1 hnn
        _ = F_r * (X : ℝ) * V7 sf.P₀ z * (7 / (p : ℝ)) := by ring
    have herr_Rp : C_err * (R_p : ℝ) ^ 2 * (Real.log (R_p : ℝ)) ^ 14 ≤
        C_err * (X : ℝ) / ((p : ℝ) * (Real.log (X : ℝ)) ^ 11) := by
      have hRp2 : (R_p : ℝ) ^ 2 ≤ D_p := by
        calc (R_p : ℝ) ^ 2 ≤ (Real.sqrt D_p) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hRp_ub 2
          _ = D_p := Real.sq_sqrt (by linarith only [hDp_ge])
      have hlogRp_le : Real.log (R_p : ℝ) ≤ Real.log (X : ℝ) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < R_p)) hRp_le_X
      calc C_err * (R_p : ℝ) ^ 2 * (Real.log (R_p : ℝ)) ^ 14
          ≤ C_err * D_p * (Real.log (X : ℝ)) ^ 14 := by
            have h1 : (Real.log (R_p : ℝ)) ^ 14 ≤ (Real.log (X : ℝ)) ^ 14 :=
              pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ R_p))) hlogRp_le 14
            have h2 := mul_le_mul hRp2 h1 (by positivity) (by linarith only [hDp_ge])
            have := mul_le_mul_of_nonneg_left h2 hCerr_p.le
            linarith only [this]
        _ = C_err * (X : ℝ) / ((p : ℝ) * (Real.log (X : ℝ)) ^ 11) := by
            dsimp [D_p]; have := hlX.ne'; have := hp_pos.ne'; field_simp
    have hcard_ub : ((((Icc 1 X).filter (fun m => p ∣ sf.F m)).filter
          (fun m => ∀ q : ℕ, q.Prime → sf.P₀ < q → q < z → ¬ q ∣ sf.F m)).card : ℝ) ≤
        F_r * (X : ℝ) * V7 sf.P₀ z * (7 / (p : ℝ)) + C_err * (X : ℝ) / ((p : ℝ) * (Real.log (X : ℝ)) ^ 11) :=
      hsel_p.trans (add_le_add hmain_ub herr_Rp)
    calc (1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ)) *
          ((((Icc 1 X).filter (fun m => p ∣ sf.F m)).filter
            (fun m => ∀ q : ℕ, q.Prime → sf.P₀ < q → q < z → ¬ q ∣ sf.F m)).card : ℝ)
        ≤ (1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ)) *
            (F_r * (X : ℝ) * V7 sf.P₀ z * (7 / (p : ℝ)) + C_err * (X : ℝ) / ((p : ℝ) * (Real.log (X : ℝ)) ^ 11)) :=
          mul_le_mul_of_nonneg_left hcard_ub hwt_nn
      _ = F_r * (X : ℝ) * V7 sf.P₀ z * ((1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ)) * (7 / (p : ℝ))) +
          (1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ)) * (C_err * (X : ℝ) / ((p : ℝ) * (Real.log (X : ℝ)) ^ 11)) := by
          ring
      _ ≤ F_r * (X : ℝ) * V7 sf.P₀ z * ((1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ)) * (7 / (p : ℝ))) +
          C_err * (X : ℝ) / ((p : ℝ) * (Real.log (X : ℝ)) ^ 11) := by
          have hnn : 0 ≤ C_err * (X : ℝ) / ((p : ℝ) * (Real.log (X : ℝ)) ^ 11) := by positivity
          nlinarith only [hwt_le1, hnn]
  -- Sum hSp_ub over the bin!
  have hsum_all := Finset.sum_le_sum hSp_ub
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum_all
  have hmain_sum :
      F_r * (X : ℝ) * V7 sf.P₀ z *
        (∑ p ∈ (Ico ⌈(X : ℝ) ^ t₀⌉₊ ⌈(X : ℝ) ^ t₁⌉₊).filter Nat.Prime,
          (1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ)) * (7 / (p : ℝ))) ≤
      (7 * F_r * (L_r - (37 / 20 : ℝ) * (t₁ - t₀)) + 1 / 2000) * (X : ℝ) * V7 sf.P₀ z := by
    have h1 := mul_le_mul_of_nonneg_left hBinX (by positivity : 0 ≤ F_r * (X : ℝ) * V7 sf.P₀ z)
    have h2 : F_r * (7 * (Real.log (t₁ / t₀) - (37 / 20 : ℝ) * (t₁ - t₀)) + C_bin / Real.log (X : ℝ)) ≤
        7 * F_r * (L_r - (37 / 20 : ℝ) * (t₁ - t₀)) + 1 / 2000 := by
      have hF_log : 7 * F_r * Real.log (t₁ / t₀) ≤ 7 * F_r * L_r := by nlinarith only [hF_pos, hlog_ratio]
      have hF_bin : F_r * (C_bin / Real.log (X : ℝ)) = F_r * C_bin / Real.log (X : ℝ) := by ring
      linarith only [hCbin_sm, hF_log, hF_bin]
    calc F_r * (X : ℝ) * V7 sf.P₀ z *
            (∑ p ∈ (Ico ⌈(X : ℝ) ^ t₀⌉₊ ⌈(X : ℝ) ^ t₁⌉₊).filter Nat.Prime,
              (1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ)) * (7 / (p : ℝ)))
        ≤ F_r * (X : ℝ) * V7 sf.P₀ z *
            (7 * (Real.log (t₁ / t₀) - (37 / 20 : ℝ) * (t₁ - t₀)) + C_bin / Real.log (X : ℝ)) := h1
      _ = (F_r * (7 * (Real.log (t₁ / t₀) - (37 / 20 : ℝ) * (t₁ - t₀)) + C_bin / Real.log (X : ℝ))) *
            ((X : ℝ) * V7 sf.P₀ z) := by ring
      _ ≤ (7 * F_r * (L_r - (37 / 20 : ℝ) * (t₁ - t₀)) + 1 / 2000) * ((X : ℝ) * V7 sf.P₀ z) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (7 * F_r * (L_r - (37 / 20 : ℝ) * (t₁ - t₀)) + 1 / 2000) * (X : ℝ) * V7 sf.P₀ z := by ring
  have herr_sum :
      ∑ p ∈ (Ico ⌈(X : ℝ) ^ t₀⌉₊ ⌈(X : ℝ) ^ t₁⌉₊).filter Nat.Prime,
        C_err * (X : ℝ) / ((p : ℝ) * (Real.log (X : ℝ)) ^ 11) ≤
      (1 / 2000 : ℝ) * (X : ℝ) * V7 sf.P₀ z := by
    have hsubX : (Ico ⌈(X : ℝ) ^ t₀⌉₊ ⌈(X : ℝ) ^ t₁⌉₊).filter Nat.Prime ⊆ (Ioo 0 X).filter Nat.Prime := by
      intro p hp
      simp only [mem_filter, mem_Ico, mem_Ioo] at hp ⊢
      refine ⟨⟨hp.2.pos, ?_⟩, hp.2⟩
      have h1 : (p : ℝ) < (X : ℝ) ^ t₁ := Nat.lt_ceil.mp hp.1.2
      have h2 : (X : ℝ) ^ t₁ ≤ (X : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1.le (by linarith only [ht₁])
      rw [Real.rpow_one] at h2
      exact_mod_cast lt_of_lt_of_le h1 h2
    have hsum_inv_p : ∑ p ∈ (Ico ⌈(X : ℝ) ^ t₀⌉₊ ⌈(X : ℝ) ^ t₁⌉₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
        2 * Real.log (X : ℝ) := by
      have hle1 : ∑ p ∈ (Ico ⌈(X : ℝ) ^ t₀⌉₊ ⌈(X : ℝ) ^ t₁⌉₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
          ∑ p ∈ (Ico ⌈(X : ℝ) ^ t₀⌉₊ ⌈(X : ℝ) ^ t₁⌉₊).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp_lo := (mem_Ico.mp (mem_filter.mp hp).1).1
        have hz_le_p : z ≤ p :=
          (Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le hX1.le ht₀)).trans hp_lo
        have hp3 : (3 : ℝ) ≤ (p : ℝ) := by have := sf.hP₀; exact_mod_cast (by omega : 3 ≤ p)
        have h1_le_logp : (1 : ℝ) ≤ Real.log (p : ℝ) := by
          rw [Real.le_log_iff_exp_le (by linarith only [hp3])]
          exact le_trans (by linarith [Real.exp_one_lt_d9]) hp3
        exact div_le_div_of_nonneg_right h1_le_logp (by linarith only [hp3])
      have hle2 : ∑ p ∈ (Ico ⌈(X : ℝ) ^ t₀⌉₊ ⌈(X : ℝ) ^ t₁⌉₊).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) ≤
          ∑ p ∈ (Ioo 0 X).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsubX fun p hp _ => ?_
        have hpr := (mem_filter.mp hp).2
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)) (Nat.cast_nonneg p)
      have hM1_X : ∑ p ∈ (Ioo 0 X).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log (X : ℝ) + C_m1 := by
        have h := hM1 X (by omega)
        simpa only [pow_one, Nat.cast_one, div_one, Nat.sub_self, pow_zero, mul_one] using h
      linarith only [hle1, hle2, hM1_X, hCm1_le]
    have hrew : ∑ p ∈ (Ico ⌈(X : ℝ) ^ t₀⌉₊ ⌈(X : ℝ) ^ t₁⌉₊).filter Nat.Prime,
          C_err * (X : ℝ) / ((p : ℝ) * (Real.log (X : ℝ)) ^ 11) =
        (C_err * (X : ℝ) / (Real.log (X : ℝ)) ^ 11) *
          ∑ p ∈ (Ico ⌈(X : ℝ) ^ t₀⌉₊ ⌈(X : ℝ) ^ t₁⌉₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
    rw [hrew]
    have hstep1 : (C_err * (X : ℝ) / (Real.log (X : ℝ)) ^ 11) *
          (∑ p ∈ (Ico ⌈(X : ℝ) ^ t₀⌉₊ ⌈(X : ℝ) ^ t₁⌉₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤
        2 * C_err * (X : ℝ) / (Real.log (X : ℝ)) ^ 10 := by
      calc (C_err * (X : ℝ) / (Real.log (X : ℝ)) ^ 11) *
              (∑ p ∈ (Ico ⌈(X : ℝ) ^ t₀⌉₊ ⌈(X : ℝ) ^ t₁⌉₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
          ≤ (C_err * (X : ℝ) / (Real.log (X : ℝ)) ^ 11) * (2 * Real.log (X : ℝ)) :=
            mul_le_mul_of_nonneg_left hsum_inv_p (by positivity)
        _ = 2 * C_err * (X : ℝ) / (Real.log (X : ℝ)) ^ 10 := by
            have := hlX.ne'; field_simp
    have hstep2 : 2 * C_err * (X : ℝ) / (Real.log (X : ℝ)) ^ 10 ≤
        (1 / 2000 : ℝ) * (X : ℝ) * (cV1 / (Real.log (X : ℝ)) ^ 7) := by
      have hpow_neg3 : (Real.log (X : ℝ)) ^ (-3 : ℝ) = ((Real.log (X : ℝ)) ^ 3)⁻¹ := by
        rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hlX.le, Real.rpow_natCast]
      rw [hpow_neg3] at hCerr_sm
      have heq_lhs : 2 * C_err * (X : ℝ) / (Real.log (X : ℝ)) ^ 10 =
          (2 * C_err * ((Real.log (X : ℝ)) ^ 3)⁻¹) * ((X : ℝ) / (Real.log (X : ℝ)) ^ 7) := by
        have := hlX.ne'; field_simp
      rw [heq_lhs]
      calc (2 * C_err * ((Real.log (X : ℝ)) ^ 3)⁻¹) * ((X : ℝ) / (Real.log (X : ℝ)) ^ 7)
          ≤ (cV1 / 2000) * ((X : ℝ) / (Real.log (X : ℝ)) ^ 7) :=
            mul_le_mul_of_nonneg_right hCerr_sm (by positivity)
        _ = (1 / 2000 : ℝ) * (X : ℝ) * (cV1 / (Real.log (X : ℝ)) ^ 7) := by ring
    exact hstep1.trans (hstep2.trans (mul_le_mul_of_nonneg_left hVz_lb (by positivity)))
  linarith only [hsum_all, hmain_sum, herr_sum]

lemma sum_Ico_prime_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (f : ℕ → ℝ) :
    ∑ p ∈ (Ico a c).filter Nat.Prime, f p =
      (∑ p ∈ (Ico a b).filter Nat.Prime, f p) + (∑ p ∈ (Ico b c).filter Nat.Prime, f p) := by
  have hdisj : Disjoint ((Ico a b).filter Nat.Prime) ((Ico b c).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (mem_Ico.mp (mem_filter.mp hp1).1).2
    have h2 := (mem_Ico.mp (mem_filter.mp hp2).1).1
    omega
  have hunion : (Ico a b).filter Nat.Prime ∪ (Ico b c).filter Nat.Prime = (Ico a c).filter Nat.Prime := by
    ext p; simp only [mem_union, mem_filter, mem_Ico]
    constructor
    · rintro (⟨⟨_, _⟩, hp⟩ | ⟨⟨_, _⟩, hp⟩) <;> exact ⟨⟨by omega, by omega⟩, hp⟩
    · rintro ⟨⟨_, _⟩, hp⟩
      by_cases hpb : p < b
      · exact Or.inl ⟨⟨by omega, hpb⟩, hp⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, hp⟩
  rw [← hunion, Finset.sum_union hdisj]

/-- Combining all 8 verified rational bins:
`∑_{z <= p < y} (1 - 37/20 * log p / log X) * S_p(z) <= 14.84 * X * V7 sf.P₀ z`! -/
lemma richert_eight_bins (sf : ShiftedForms) :
    ∀ᶠ X : ℕ in atTop,
      let z := ⌈(X : ℝ) ^ ((1 : ℝ) / 36)⌉₊
      let y := ⌈(X : ℝ) ^ ((20 : ℝ) / 37)⌉₊
      ∑ p ∈ (Ico z y).filter Nat.Prime,
        (1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ)) *
          (((SSet sf X z).filter (fun m => p ∣ sf.F m)).card : ℝ) ≤
      (1484 / 100 : ℝ) * (X : ℝ) * V7 sf.P₀ z := by
  have hb0 := richert_bin_bound sf (t₀ := 1 / 36) (t₁ := 9 / 50) (c := 13 / 10)
    (gap_r := 5847 / 1000) (err_r := 30 / 10000) (F_r := 10031 / 10000) (L_r := 18693 / 10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hb1 := richert_bin_bound sf (t₀ := 9 / 50) (t₁ := 13 / 50) (c := 11 / 10)
    (gap_r := 4103 / 1000) (err_r := 166 / 10000) (F_r := 10169 / 10000) (L_r := 3683 / 10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hb2 := richert_bin_bound sf (t₀ := 13 / 50) (t₁ := 33 / 100) (c := 9 / 10)
    (gap_r := 2745 / 1000) (err_r := 643 / 10000) (F_r := 10688 / 10000) (L_r := 2390 / 10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hb3 := richert_bin_bound sf (t₀ := 33 / 100) (t₁ := 39 / 100) (c := 7 / 10)
    (gap_r := 1736 / 1000) (err_r := 1763 / 10000) (F_r := 12141 / 10000) (L_r := 1676 / 10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hb4 := richert_bin_bound sf (t₀ := 39 / 100) (t₁ := 11 / 25) (c := 1 / 2)
    (gap_r := 1016 / 1000) (err_r := 3621 / 10000) (F_r := 15677 / 10000) (L_r := 1212 / 10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hb5 := richert_bin_bound sf (t₀ := 11 / 25) (t₁ := 12 / 25) (c := 7 / 20)
    (gap_r := 565 / 1000) (err_r := 5684 / 10000) (F_r := 23170 / 10000) (L_r := 876 / 10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hb6 := richert_bin_bound sf (t₀ := 12 / 25) (t₁ := 51 / 100) (c := 1 / 4)
    (gap_r := 312 / 1000) (err_r := 7320 / 10000) (F_r := 37314 / 10000) (L_r := 612 / 10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hb7 := richert_bin_bound sf (t₀ := 51 / 100) (t₁ := 20 / 37) (c := 3 / 20)
    (gap_r := 126 / 1000) (err_r := 8817 / 10000) (F_r := 84531 / 10000) (L_r := 587 / 10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  filter_upwards [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, eventually_ge_atTop 2]
    with X h0 h1 h2 h3 h4 h5 h6 h7 hX2
  intro z y
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hle : ∀ {a b : ℝ}, a ≤ b → ⌈(X : ℝ) ^ a⌉₊ ≤ ⌈(X : ℝ) ^ b⌉₊ := fun hab =>
    Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le hX1 hab)
  let g : ℕ → ℝ := fun p =>
    (1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ)) *
      (((SSet sf X z).filter (fun m => p ∣ sf.F m)).card : ℝ)
  have hsplit : ∑ p ∈ (Ico z y).filter Nat.Prime, g p =
      (∑ p ∈ (Ico ⌈(X : ℝ) ^ ((1 : ℝ) / 36)⌉₊ ⌈(X : ℝ) ^ ((9 : ℝ) / 50)⌉₊).filter Nat.Prime, g p) +
      (∑ p ∈ (Ico ⌈(X : ℝ) ^ ((9 : ℝ) / 50)⌉₊ ⌈(X : ℝ) ^ ((13 : ℝ) / 50)⌉₊).filter Nat.Prime, g p) +
      (∑ p ∈ (Ico ⌈(X : ℝ) ^ ((13 : ℝ) / 50)⌉₊ ⌈(X : ℝ) ^ ((33 : ℝ) / 100)⌉₊).filter Nat.Prime, g p) +
      (∑ p ∈ (Ico ⌈(X : ℝ) ^ ((33 : ℝ) / 100)⌉₊ ⌈(X : ℝ) ^ ((39 : ℝ) / 100)⌉₊).filter Nat.Prime, g p) +
      (∑ p ∈ (Ico ⌈(X : ℝ) ^ ((39 : ℝ) / 100)⌉₊ ⌈(X : ℝ) ^ ((11 : ℝ) / 25)⌉₊).filter Nat.Prime, g p) +
      (∑ p ∈ (Ico ⌈(X : ℝ) ^ ((11 : ℝ) / 25)⌉₊ ⌈(X : ℝ) ^ ((12 : ℝ) / 25)⌉₊).filter Nat.Prime, g p) +
      (∑ p ∈ (Ico ⌈(X : ℝ) ^ ((12 : ℝ) / 25)⌉₊ ⌈(X : ℝ) ^ ((51 : ℝ) / 100)⌉₊).filter Nat.Prime, g p) +
      (∑ p ∈ (Ico ⌈(X : ℝ) ^ ((51 : ℝ) / 100)⌉₊ ⌈(X : ℝ) ^ ((20 : ℝ) / 37)⌉₊).filter Nat.Prime, g p) := by
    rw [sum_Ico_prime_split (hle (by norm_num : (1 : ℝ) / 36 ≤ 51 / 100)) (hle (by norm_num : (51 : ℝ) / 100 ≤ 20 / 37))]
    rw [sum_Ico_prime_split (hle (by norm_num : (1 : ℝ) / 36 ≤ 12 / 25)) (hle (by norm_num : (12 : ℝ) / 25 ≤ 51 / 100))]
    rw [sum_Ico_prime_split (hle (by norm_num : (1 : ℝ) / 36 ≤ 11 / 25)) (hle (by norm_num : (11 : ℝ) / 25 ≤ 12 / 25))]
    rw [sum_Ico_prime_split (hle (by norm_num : (1 : ℝ) / 36 ≤ 39 / 100)) (hle (by norm_num : (39 : ℝ) / 100 ≤ 11 / 25))]
    rw [sum_Ico_prime_split (hle (by norm_num : (1 : ℝ) / 36 ≤ 33 / 100)) (hle (by norm_num : (33 : ℝ) / 100 ≤ 39 / 100))]
    rw [sum_Ico_prime_split (hle (by norm_num : (1 : ℝ) / 36 ≤ 13 / 50)) (hle (by norm_num : (13 : ℝ) / 50 ≤ 33 / 100))]
    rw [sum_Ico_prime_split (hle (by norm_num : (1 : ℝ) / 36 ≤ 9 / 50)) (hle (by norm_num : (9 : ℝ) / 50 ≤ 13 / 50))]
  have hXV_nn : 0 ≤ (X : ℝ) * V7 sf.P₀ z := mul_nonneg (Nat.cast_nonneg X) (V7_pos (w := z) sf.hP₀).le
  change ∑ p ∈ (Ico z y).filter Nat.Prime, g p ≤ _
  rw [hsplit]
  have hsum_le : ∑ p ∈ (Ico ⌈(X : ℝ) ^ ((1 : ℝ) / 36)⌉₊ ⌈(X : ℝ) ^ ((9 : ℝ) / 50)⌉₊).filter Nat.Prime, g p +
      ∑ p ∈ (Ico ⌈(X : ℝ) ^ ((9 : ℝ) / 50)⌉₊ ⌈(X : ℝ) ^ ((13 : ℝ) / 50)⌉₊).filter Nat.Prime, g p +
      ∑ p ∈ (Ico ⌈(X : ℝ) ^ ((13 : ℝ) / 50)⌉₊ ⌈(X : ℝ) ^ ((33 : ℝ) / 100)⌉₊).filter Nat.Prime, g p +
      ∑ p ∈ (Ico ⌈(X : ℝ) ^ ((33 : ℝ) / 100)⌉₊ ⌈(X : ℝ) ^ ((39 : ℝ) / 100)⌉₊).filter Nat.Prime, g p +
      ∑ p ∈ (Ico ⌈(X : ℝ) ^ ((39 : ℝ) / 100)⌉₊ ⌈(X : ℝ) ^ ((11 : ℝ) / 25)⌉₊).filter Nat.Prime, g p +
      ∑ p ∈ (Ico ⌈(X : ℝ) ^ ((11 : ℝ) / 25)⌉₊ ⌈(X : ℝ) ^ ((12 : ℝ) / 25)⌉₊).filter Nat.Prime, g p +
      ∑ p ∈ (Ico ⌈(X : ℝ) ^ ((12 : ℝ) / 25)⌉₊ ⌈(X : ℝ) ^ ((51 : ℝ) / 100)⌉₊).filter Nat.Prime, g p +
      ∑ p ∈ (Ico ⌈(X : ℝ) ^ ((51 : ℝ) / 100)⌉₊ ⌈(X : ℝ) ^ ((20 : ℝ) / 37)⌉₊).filter Nat.Prime, g p ≤
      ((7 * (10031 / 10000 : ℝ) * (18693 / 10000 - (37 / 20) * (9 / 50 - 1 / 36)) + 1 / 1000) +
       (7 * (10169 / 10000 : ℝ) * (3683 / 10000 - (37 / 20) * (13 / 50 - 9 / 50)) + 1 / 1000) +
       (7 * (10688 / 10000 : ℝ) * (2390 / 10000 - (37 / 20) * (33 / 100 - 13 / 50)) + 1 / 1000) +
       (7 * (12141 / 10000 : ℝ) * (1676 / 10000 - (37 / 20) * (39 / 100 - 33 / 100)) + 1 / 1000) +
       (7 * (15677 / 10000 : ℝ) * (1212 / 10000 - (37 / 20) * (11 / 25 - 39 / 100)) + 1 / 1000) +
       (7 * (23170 / 10000 : ℝ) * (876 / 10000 - (37 / 20) * (12 / 25 - 11 / 25)) + 1 / 1000) +
       (7 * (37314 / 10000 : ℝ) * (612 / 10000 - (37 / 20) * (51 / 100 - 12 / 25)) + 1 / 1000) +
       (7 * (84531 / 10000 : ℝ) * (587 / 10000 - (37 / 20) * (20 / 37 - 51 / 100)) + 1 / 1000)) *
      ((X : ℝ) * V7 sf.P₀ z) := by
    linarith [h0, h1, h2, h3, h4, h5, h6, h7]
  have hconst_le :
      ((7 * (10031 / 10000 : ℝ) * (18693 / 10000 - (37 / 20) * (9 / 50 - 1 / 36)) + 1 / 1000) +
       (7 * (10169 / 10000 : ℝ) * (3683 / 10000 - (37 / 20) * (13 / 50 - 9 / 50)) + 1 / 1000) +
       (7 * (10688 / 10000 : ℝ) * (2390 / 10000 - (37 / 20) * (33 / 100 - 13 / 50)) + 1 / 1000) +
       (7 * (12141 / 10000 : ℝ) * (1676 / 10000 - (37 / 20) * (39 / 100 - 33 / 100)) + 1 / 1000) +
       (7 * (15677 / 10000 : ℝ) * (1212 / 10000 - (37 / 20) * (11 / 25 - 39 / 100)) + 1 / 1000) +
       (7 * (23170 / 10000 : ℝ) * (876 / 10000 - (37 / 20) * (12 / 25 - 11 / 25)) + 1 / 1000) +
       (7 * (37314 / 10000 : ℝ) * (612 / 10000 - (37 / 20) * (51 / 100 - 12 / 25)) + 1 / 1000) +
       (7 * (84531 / 10000 : ℝ) * (587 / 10000 - (37 / 20) * (20 / 37 - 51 / 100)) + 1 / 1000)) ≤
      1484 / 100 := by norm_num
  calc _ ≤ _ := hsum_le
    _ ≤ (1484 / 100 : ℝ) * ((X : ℝ) * V7 sf.P₀ z) := mul_le_mul_of_nonneg_right hconst_le hXV_nn
    _ = (1484 / 100 : ℝ) * (X : ℝ) * V7 sf.P₀ z := by ring

/-! ### Part 5: Main rough almost-prime supply theorem (Hildebrand Lemma 2 supply) -/

set_option maxHeartbeats 800000 in
theorem rough_almost_prime_supply :
    ∀ s c : Fin 7 → ℕ, (∀ i, 0 < s i) →
      (∀ i j, i ≠ j → s i * c j ≠ s j * c i) →
      (∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬ p ∣ s i * t + c i) →
      ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ᶠ x : ℝ in atTop,
        ∃ V : Finset ℕ, x / (Real.log x) ^ 7 ≤ C * V.card ∧ ∀ n ∈ V, 0 < n ∧ (n : ℝ) ≤ x ∧
          let v := fun i => s i * n + c i
          (∀ i, 1 < v i ∧ ∀ p ∈ (v i).primeFactors, x ^ δ < (p : ℝ)) ∧
          (∑ i, (v i).primeFactors.card) ≤ 27 := by
  intro s c hs hdistinct hadm
  obtain ⟨_, sf, hs_eq, hc_eq⟩ := build_shifted_forms s c hs hdistinct hadm
  obtain ⟨cV1, _, hcV1p, _, hV_ord⟩ := (V7_asymptotics sf.P₀ sf.hP₀).1
  set K : ℕ := sf.M₀ + sf.n₀ + 1
  have hK_pos : 0 < K := by dsimp [K]; have := sf.hM₀_pos; omega
  set C_F : ℕ := (∑ i : Fin 7, (s i * K + c i)) + 2
  have hCF_ge2 : 2 ≤ C_F := by dsimp [C_F]; omega
  refine ⟨1000 * (K : ℝ) / cV1, (1 : ℝ) / 37, by positivity, by norm_num, ?_⟩
  -- Pull back asymptotic properties from X = ⌊x / K⌋₊ to x ∈ atTop!
  have hX_tend : Filter.Tendsto (fun x : ℝ => ⌊x / (K : ℝ)⌋₊) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro N
    refine ⟨(N : ℝ) * (K : ℝ), fun x hx => ?_⟩
    exact Nat.le_floor ((le_div_iff₀ (by positivity)).mpr hx)
  have hev_buch := hX_tend.eventually (buchstab_lower_bound sf)
  have hev_bins := hX_tend.eventually (richert_eight_bins sf)
  have hev_Xbig : ∀ᶠ X : ℕ in atTop,
      sf.P₀ < ⌈(X : ℝ) ^ ((1 : ℝ) / 36)⌉₊ ∧
      (37 / 20 : ℝ) * 7 * Real.log (C_F : ℝ) ≤ (1 / 20 : ℝ) * Real.log (X : ℝ) ∧
      1000 ≤ X := by
    have h1 := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 36)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop ((sf.P₀ : ℝ) + 2)
    have h2 := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (20 * ((37 / 20 : ℝ) * 7 * Real.log (C_F : ℝ)))
    filter_upwards [h1, h2, eventually_ge_atTop 1000] with X h1' h2' h3'
    dsimp only [Function.comp_apply] at h1' h2'
    refine ⟨?_, by linarith only [h2'], h3'⟩
    have : (sf.P₀ : ℝ) + 2 ≤ (⌈(X : ℝ) ^ ((1 : ℝ) / 36)⌉₊ : ℝ) := h1'.trans (Nat.le_ceil _)
    have : sf.P₀ + 2 ≤ ⌈(X : ℝ) ^ ((1 : ℝ) / 36)⌉₊ := by exact_mod_cast this
    omega
  have hev_z_gt_x : ∀ᶠ x : ℝ in atTop,
      x ^ ((1 : ℝ) / 37) < (x / (2 * (K : ℝ))) ^ ((1 : ℝ) / 36) ∧
      (2 * (K : ℝ) : ℝ) ≤ x := by
    have h1 : Filter.Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 36 - 1 / 37)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num)
    filter_upwards [h1.eventually_gt_atTop ((2 * (K : ℝ)) ^ ((1 : ℝ) / 36)),
      eventually_ge_atTop (max (2 * (K : ℝ)) 100)] with x hx1 hx2
    have hx_pos : 0 < x := by linarith [le_max_right (2 * (K : ℝ)) 100]
    have h2K_pos : (0 : ℝ) < 2 * (K : ℝ) := by positivity
    refine ⟨?_, le_trans (le_max_left _ _) hx2⟩
    rw [Real.div_rpow hx_pos.le h2K_pos.le, lt_div_iff₀ (Real.rpow_pos_of_pos h2K_pos _)]
    have hmul : x ^ ((1 : ℝ) / 37) * (2 * (K : ℝ)) ^ ((1 : ℝ) / 36) <
        x ^ ((1 : ℝ) / 37) * x ^ ((1 : ℝ) / 36 - 1 / 37) :=
      mul_lt_mul_of_pos_left hx1 (Real.rpow_pos_of_pos hx_pos _)
    rw [← Real.rpow_add hx_pos, show (1 : ℝ) / 37 + (1 / 36 - 1 / 37) = 1 / 36 by ring] at hmul
    exact hmul
  filter_upwards [hev_buch, hev_bins, hX_tend.eventually hev_Xbig, hev_z_gt_x]
    with x hbuch hbins ⟨hzP, hCF_log, hX1000⟩ ⟨hz_gt_x, hx_ge_2K⟩
  set X : ℕ := ⌊x / (K : ℝ)⌋₊
  set z : ℕ := ⌈(X : ℝ) ^ ((1 : ℝ) / 36)⌉₊
  set y : ℕ := ⌈(X : ℝ) ^ ((20 : ℝ) / 37)⌉₊
  have hx_pos : 0 < x := by linarith [show (0 : ℝ) < 2 * (K : ℝ) by positivity]
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) < X := by exact_mod_cast (by omega : 1 < X)
  have hlX : 0 < Real.log (X : ℝ) := Real.log_pos hX1
  have hX_lb : x / (2 * (K : ℝ)) ≤ (X : ℝ) := by
    have h1 : x / (K : ℝ) - 1 ≤ (X : ℝ) := by linarith [Nat.lt_floor_add_one (x / (K : ℝ))]
    have h2 : (1 : ℝ) ≤ x / (2 * (K : ℝ)) := by
      rw [one_le_div (by positivity)]; exact hx_ge_2K
    have h3 : x / (K : ℝ) = 2 * (x / (2 * (K : ℝ))) := by ring
    linarith
  have hX_le_x : (X : ℝ) ≤ x := by
    have h1 : (X : ℝ) ≤ x / (K : ℝ) := Nat.floor_le (by positivity)
    have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK_pos
    exact h1.trans (div_le_self hx_pos.le hK1)
  have hz_gt_xd : x ^ ((1 : ℝ) / 37) < (z : ℝ) :=
    hz_gt_x.trans_le ((Real.rpow_le_rpow (by positivity) hX_lb (by norm_num)).trans (Nat.le_ceil _))
  -- Define Richert weight W m for m ∈ SSet sf X z
  let W : ℕ → ℝ := fun m =>
    1 - (100 / 1495 : ℝ) *
      ∑ p ∈ (Ico z y).filter (fun p => p.Prime ∧ p ∣ sf.F m),
        (1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ))
  -- Double counting identity for ∑ m ∈ SSet sf X z, W m!
  have hW_sum :
      ∑ m ∈ SSet sf X z, W m =
        ((SSet sf X z).card : ℝ) -
        (100 / 1495 : ℝ) *
          ∑ p ∈ (Ico z y).filter Nat.Prime,
            (1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ)) *
              (((SSet sf X z).filter (fun m => p ∣ sf.F m)).card : ℝ) := by
    dsimp [W]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
    congr 2
    have hinner : ∀ m ∈ SSet sf X z,
        ∑ p ∈ (Ico z y).filter (fun p => p.Prime ∧ p ∣ sf.F m),
          (1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ)) =
        ∑ p ∈ (Ico z y).filter Nat.Prime,
          if p ∣ sf.F m then (1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ)) else 0 := by
      intro m _
      rw [← Finset.sum_filter]
      congr 1; ext p; simp only [mem_filter, and_assoc]
    rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hW_lb : (2 / 1000 : ℝ) * (X : ℝ) * V7 sf.P₀ z ≤ ∑ m ∈ SSet sf X z, W m := by
    have hVpos_z := V7_pos (w := z) sf.hP₀
    have hXV_nn : 0 ≤ (X : ℝ) * V7 sf.P₀ z := by positivity
    rw [hW_sum]
    have hcoeff : (2 / 1000 : ℝ) ≤ 995 / 1000 - (100 / 1495) * (1484 / 100) := by norm_num
    nlinarith [hbuch, hbins, hcoeff, hXV_nn]
  -- Every m ∈ SSet sf X z has W m <= 1!
  have hW_le1 : ∀ m, W m ≤ 1 := by
    intro m
    dsimp [W]
    have hsum_nn : 0 ≤ ∑ p ∈ (Ico z y).filter (fun p => p.Prime ∧ p ∣ sf.F m),
        (1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ)) := by
      refine Finset.sum_nonneg fun p hp => ?_
      have hp_hi := (mem_Ico.mp (mem_filter.mp hp).1).2
      have hpr := (mem_filter.mp hp).2.1
      have hp_lt : (p : ℝ) < (X : ℝ) ^ ((20 : ℝ) / 37) := Nat.lt_ceil.mp hp_hi
      have hlogp_lt : Real.log (p : ℝ) < (20 / 37 : ℝ) * Real.log (X : ℝ) := by
        calc Real.log (p : ℝ) < Real.log ((X : ℝ) ^ ((20 : ℝ) / 37)) :=
              Real.log_lt_log (by exact_mod_cast hpr.pos) hp_lt
          _ = (20 / 37 : ℝ) * Real.log (X : ℝ) := Real.log_rpow hXp _
      have h3 : (37 / 20 : ℝ) * Real.log (p : ℝ) ≤ Real.log (X : ℝ) := by linarith
      have h4 : (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ) ≤ 1 := (div_le_one hlX).mpr h3
      linarith
    nlinarith
  set Good := (SSet sf X z).filter (fun m => 0 < W m)
  have hGood_lb : (2 / 1000 : ℝ) * (X : ℝ) * V7 sf.P₀ z ≤ (Good.card : ℝ) := by
    have hsplit : ∑ m ∈ SSet sf X z, W m =
        (∑ m ∈ Good, W m) + (∑ m ∈ (SSet sf X z).filter (fun m => ¬ 0 < W m), W m) :=
      (Finset.sum_filter_add_sum_filter_not (SSet sf X z) (fun m => 0 < W m) W).symm
    have hneg : ∑ m ∈ (SSet sf X z).filter (fun m => ¬ 0 < W m), W m ≤ 0 :=
      Finset.sum_nonpos fun m hm => by linarith [(mem_filter.mp hm).2]
    have hpos_ub : ∑ m ∈ Good, W m ≤ (Good.card : ℝ) := by
      calc ∑ m ∈ Good, W m ≤ ∑ _m ∈ Good, (1 : ℝ) := Finset.sum_le_sum fun m _ => hW_le1 m
        _ = (Good.card : ℝ) := by simp
    linarith [hW_lb, hsplit, hneg, hpos_ub]
  -- Define V = Good.image (fun m => sf.M₀ * m + sf.n₀)!
  let phi : ℕ → ℕ := fun m => sf.M₀ * m + sf.n₀
  have hphi_inj : Function.Injective phi := fun m₁ m₂ h => by
    dsimp [phi] at h
    exact Nat.eq_of_mul_eq_mul_left sf.hM₀_pos (Nat.add_right_cancel h)
  refine ⟨Good.image phi, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hphi_inj]
    have hVz_lb : cV1 / (Real.log x) ^ 7 ≤ V7 sf.P₀ z := by
      have h1 := (hV_ord z hzP).1
      have hz_le_x : (z : ℝ) ≤ x := by
        have h1' : (X : ℝ) ^ ((1 : ℝ) / 36) ≤ (X : ℝ) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le hX1.le (by norm_num)
        have h2' : (X : ℝ) ^ ((1 : ℝ) / 2) + 1 ≤ (X : ℝ) := by
          have hsq : (X : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (X : ℝ) := (Real.sqrt_eq_rpow (X : ℝ)).symm
          rw [hsq]
          have h3 : (4 : ℝ) ≤ Real.sqrt (X : ℝ) := by
            rw [show (4 : ℝ) = Real.sqrt 16 by norm_num]
            exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 16 ≤ X))
          have h4 := Real.sq_sqrt hXp.le
          nlinarith
        linarith [Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 36) by positivity)]
      have hlogz_le_x : Real.log (z : ℝ) ≤ Real.log x :=
        Real.log_le_log (by exact_mod_cast (by have := sf.hP₀; omega : 0 < z)) hz_le_x
      have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by have := sf.hP₀; omega : 1 < z))
      have hpow : (Real.log (z : ℝ)) ^ 7 ≤ (Real.log x) ^ 7 := pow_le_pow_left₀ hlogz_pos.le hlogz_le_x 7
      exact (div_le_div_of_nonneg_left hcV1p.le (pow_pos hlogz_pos 7) hpow).trans h1
    have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith only [hX1, hX_le_x])
    have h1 : (2 / 1000 : ℝ) * (x / (2 * (K : ℝ))) * (cV1 / (Real.log x) ^ 7) ≤ (Good.card : ℝ) := by
      have hA : (2 / 1000 : ℝ) * (x / (2 * (K : ℝ))) ≤ (2 / 1000 : ℝ) * (X : ℝ) := by linarith only [hX_lb]
      have hmul := mul_le_mul hA hVz_lb (by positivity) (by positivity)
      exact hmul.trans hGood_lb
    have heq : (1000 * (K : ℝ) / cV1) * ((2 / 1000 : ℝ) * (x / (2 * (K : ℝ))) * (cV1 / (Real.log x) ^ 7)) =
        x / (Real.log x) ^ 7 := by
      have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast hK_pos.ne'
      have hc0 : cV1 ≠ 0 := hcV1p.ne'
      have hlx0 : Real.log x ≠ 0 := hlogx_pos.ne'
      field_simp
    have hmul2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 1000 * (K : ℝ) / cV1)
    linarith only [heq, hmul2]
  · intro n hn
    obtain ⟨m, hmG, rfl⟩ := mem_image.mp hn
    have hmS := (mem_filter.mp hmG).1
    have hWm_pos := (mem_filter.mp hmG).2
    have hm_Icc := (mem_filter.mp hmS).1
    have hm_rough := (mem_filter.mp hmS).2
    have hm1 : 1 ≤ m := (mem_Icc.mp hm_Icc).1
    have hmX : m ≤ X := (mem_Icc.mp hm_Icc).2
    have hn_pos : 0 < phi m := by dsimp [phi]; have := sf.hM₀_pos; nlinarith
    have hn_le_x : (phi m : ℝ) ≤ x := by
      have h1 : phi m ≤ K * X := by
        dsimp [phi, K]
        have : sf.n₀ ≤ sf.n₀ * m := Nat.le_mul_of_pos_right sf.n₀ (by omega)
        nlinarith
      have h2 : (K : ℝ) * (X : ℝ) ≤ x := by
        have := Nat.floor_le (show (0 : ℝ) ≤ x / (K : ℝ) by positivity)
        have h3 := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ K)
        have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast hK_pos.ne'
        rwa [mul_div_cancel₀ _ hK0] at h3
      exact (by exact_mod_cast h1 : (phi m : ℝ) ≤ (K : ℝ) * (X : ℝ)).trans h2
    have hv_eq : ∀ i : Fin 7, s i * phi m + c i = sf.L i m := fun i => by
      rw [sf.hL_def, hs_eq, hc_eq]
    refine ⟨hn_pos, hn_le_x, ?_, ?_⟩
    · intro i
      dsimp only
      rw [hv_eq i]
      refine ⟨sf.hL_gt1 i m hm1, fun p hp => ?_⟩
      have hpr := Nat.prime_of_mem_primeFactors hp
      have hpL := Nat.dvd_of_mem_primeFactors hp
      have hpF : p ∣ sf.F m := by
        rw [sf.hF_def]
        exact hpL.trans (Finset.dvd_prod_of_mem (fun j => sf.L j m) (mem_univ i))
      have hpP : sf.P₀ < p := by
        by_contra hle; push Not at hle
        exact sf.hsmall p hpr hle m hpF
      have hp_ge_z : z ≤ p := by
        by_contra hlt; push Not at hlt
        exact hm_rough p hpr hpP hlt hpF
      exact hz_gt_xd.trans_le (by exact_mod_cast hp_ge_z)
    · -- Prove ∑ i : Fin 7, (s i * phi m + c i).primeFactors.card ≤ 27!
      dsimp only
      have hsum_eq_F : ∑ i : Fin 7, (s i * phi m + c i).primeFactors.card = (sf.F m).primeFactors.card := by
        have h1 : ∀ i : Fin 7, (s i * phi m + c i).primeFactors = (sf.L i m).primeFactors := fun i => by
          rw [hv_eq i]
        simp_rw [h1]
        have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin 7)) : Set (Fin 7))
            (fun i => (sf.L i m).primeFactors) := by
          intro i _ j _ hij
          change Disjoint (sf.L i m).primeFactors (sf.L j m).primeFactors
          rw [Finset.disjoint_left]
          intro p hpi hpj
          have hpr := Nat.prime_of_mem_primeFactors hpi
          have hdi := Nat.dvd_of_mem_primeFactors hpi
          have hdj := Nat.dvd_of_mem_primeFactors hpj
          have hpF : p ∣ sf.F m := by
            rw [sf.hF_def]
            exact hdi.trans (Finset.dvd_prod_of_mem (fun k => sf.L k m) (mem_univ i))
          have hpP : sf.P₀ < p := by
            by_contra hle; push Not at hle
            exact sf.hsmall p hpr hle m hpF
          exact sf.hcop_forms p hpr hpP m i j hij ⟨hdi, hdj⟩
        have hunion : (Finset.univ : Finset (Fin 7)).biUnion (fun i => (sf.L i m).primeFactors) =
            (sf.F m).primeFactors := by
          ext p
          simp only [mem_biUnion, mem_univ, true_and, Nat.mem_primeFactors]
          constructor
          · rintro ⟨i, hpr, hdi, _⟩
            refine ⟨hpr, ?_, (sf.hF_pos m hm1).ne'⟩
            rw [sf.hF_def]
            exact hdi.trans (Finset.dvd_prod_of_mem (fun k => sf.L k m) (mem_univ i))
          · rintro ⟨hpr, hdF, _⟩
            rw [sf.hF_def] at hdF
            obtain ⟨i, _, hdi⟩ := (hpr.prime.dvd_finsetProd_iff _).mp hdF
            exact ⟨i, hpr, hdi, (by have := sf.hL_gt1 i m hm1; omega)⟩
        rw [← hunion, Finset.card_biUnion hdisj]
      rw [hsum_eq_F]
      set Sall := (sf.F m).primeFactors
      have hSall_sum_lt :
          ∑ p ∈ Sall, (1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ)) < 1495 / 100 := by
        have hlt_good :
            ∑ p ∈ (Ico z y).filter (fun p => p.Prime ∧ p ∣ sf.F m),
              (1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ)) < 1495 / 100 := by
          dsimp [W] at hWm_pos
          linarith only [hWm_pos]
        have hsub_part : (Ico z y).filter (fun p => p.Prime ∧ p ∣ sf.F m) = Sall.filter (fun p => p < y) := by
          ext p; simp only [Sall, mem_filter, mem_Ico, Nat.mem_primeFactors]
          constructor
          · rintro ⟨⟨_, hpy⟩, hpr, hdvd⟩
            exact ⟨⟨hpr, hdvd, (sf.hF_pos m hm1).ne'⟩, hpy⟩
          · rintro ⟨⟨hpr, hdvd, _⟩, hpy⟩
            have hpP : sf.P₀ < p := by
              by_contra hle; push Not at hle; exact sf.hsmall p hpr hle m hdvd
            have hp_ge_z : z ≤ p := by
              by_contra hlt; push Not at hlt; exact hm_rough p hpr hpP hlt hdvd
            exact ⟨⟨hp_ge_z, hpy⟩, hpr, hdvd⟩
        have hsplit := (Finset.sum_filter_add_sum_filter_not Sall (fun p => p < y)
          (fun p => 1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ))).symm
        have hge_y_nonpos :
            ∑ p ∈ Sall.filter (fun p => ¬ p < y),
              (1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ)) ≤ 0 := by
          refine Finset.sum_nonpos fun p hp => ?_
          have hp_ge_y : y ≤ p := by have := (mem_filter.mp hp).2; omega
          have h1 : (X : ℝ) ^ ((20 : ℝ) / 37) ≤ (p : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hp_ge_y)
          have h2 : (20 / 37 : ℝ) * Real.log (X : ℝ) ≤ Real.log (p : ℝ) := by
            calc (20 / 37 : ℝ) * Real.log (X : ℝ) = Real.log ((X : ℝ) ^ ((20 : ℝ) / 37)) :=
                  (Real.log_rpow hXp _).symm
              _ ≤ Real.log (p : ℝ) := Real.log_le_log (Real.rpow_pos_of_pos hXp _) h1
          have h3 : 1 ≤ (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ) := by
            rw [one_le_div hlX]; linarith only [h2]
          linarith only [h3]
        rw [hsub_part] at hlt_good
        linarith only [hlt_good, hsplit, hge_y_nonpos]
      have hsum_logp_ub :
          ∑ p ∈ Sall, Real.log (p : ℝ) ≤ 7 * Real.log (X : ℝ) + 7 * Real.log (C_F : ℝ) := by
        have hprod_dvd : ∏ p ∈ Sall, p ∣ sf.F m := Nat.prod_primeFactors_dvd (sf.F m)
        have hprod_le_F : ∏ p ∈ Sall, p ≤ sf.F m := Nat.le_of_dvd (sf.hF_pos m hm1) hprod_dvd
        have hF_le : sf.F m ≤ (C_F * X) ^ 7 := by
          rw [sf.hF_def]
          calc ∏ i : Fin 7, sf.L i m
              ≤ ∏ _i : Fin 7, (C_F * X) := by
                refine Finset.prod_le_prod' fun i _ => ?_
                rw [← hv_eq i]
                have h1 : phi m ≤ K * X := by
                  dsimp [phi, K]
                  have : sf.n₀ ≤ sf.n₀ * m := Nat.le_mul_of_pos_right sf.n₀ (by omega)
                  nlinarith only [this, hmX]
                have h2 : s i * K + c i ≤ C_F := by
                  have hmem : s i * K + c i ≤ ∑ j : Fin 7, (s j * K + c j) :=
                    Finset.single_le_sum (f := fun j : Fin 7 => s j * K + c j) (fun _ _ => Nat.zero_le _) (mem_univ i)
                  dsimp [C_F]; omega
                have hX1' : 1 ≤ X := by omega
                nlinarith only [h1, h2, Nat.le_mul_of_pos_right (c i) (by omega : 0 < X), hX1']
            _ = (C_F * X) ^ 7 := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        have hprod_pos : (0 : ℝ) < ∏ p ∈ Sall, (p : ℝ) :=
          Finset.prod_pos fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
        have hlog_eq : ∑ p ∈ Sall, Real.log (p : ℝ) = Real.log (∏ p ∈ Sall, (p : ℝ)) := by
          rw [Real.log_prod fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero]
        rw [hlog_eq]
        calc Real.log (∏ p ∈ Sall, (p : ℝ))
            ≤ Real.log (((C_F * X) ^ 7 : ℕ) : ℝ) := by
              apply Real.log_le_log hprod_pos
              rw [← Nat.cast_prod]
              exact_mod_cast hprod_le_F.trans hF_le
          _ = 7 * Real.log (X : ℝ) + 7 * Real.log (C_F : ℝ) := by
              push_cast
              rw [Real.log_pow, Real.log_mul (by positivity) hXp.ne']
              ring
      have hsum_rew :
          ∑ p ∈ Sall, (1 - (37 / 20 : ℝ) * Real.log (p : ℝ) / Real.log (X : ℝ)) =
            (Sall.card : ℝ) - (37 / 20 : ℝ) * (∑ p ∈ Sall, Real.log (p : ℝ)) / Real.log (X : ℝ) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.sum_div, ← Finset.mul_sum]
      have hterm_ub2 :
          (37 / 20 : ℝ) * (∑ p ∈ Sall, Real.log (p : ℝ)) / Real.log (X : ℝ) ≤ 7 * (37 / 20 : ℝ) + 1 / 20 := by
        rw [div_le_iff₀ hlX]
        nlinarith only [hsum_logp_ub, hCF_log]
      have hcard_lt28 : (Sall.card : ℝ) < 28 := by
        rw [hsum_rew] at hSall_sum_lt
        linarith only [hSall_sum_lt, hterm_ub2]
      have hcard_lt28N : Sall.card < 28 := by exact_mod_cast hcard_lt28
      omega

end Erdos946Sieve2
end

section
/-! Remove the additional prescribed valuations from the sieve. The second input
constructs a single CRT progression on which the divided forms are admissible.
The remaining analytic input is the fixed-coefficient seven-dimensional
lower-bound sieve in Hildebrand, Pacific J. Math. 129 (1987), Lemma 2. -/

namespace OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1
open Finset Filter Real
open scoped Classical

/-- Seven-dimensional lower-bound sieve for seven nonproportional affine
forms with no fixed prime divisor, in the squarefree 27-factor range. -/
def H1 : Prop := ∀ s c : Fin 7 → ℕ, (∀ i, 0 < s i) →
    (∀ i j, i ≠ j → s i*c j ≠ s j*c i) →
    (∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬p ∣ s i*t+c i) →
    ∀ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ∃ U : Finset ℕ, x / (log x)^7 ≤ C * U.card ∧ ∀ n ∈ U, 0 < n ∧ (n:ℝ) ≤ x ∧
        let v := fun i => s i*n+c i
        (∀ i, 1 < v i ∧ Squarefree (v i) ∧ ∀ p ∈ (v i).primeFactors, B < p) ∧
        (∑ i, (v i).primeFactors.card) ≤ 27

/-- The Chinese remainder progression and the admissibility of the divided forms. -/
def H2 : Prop := ∀ a q e : Fin 7 → ℕ, StrictMono a → (∀ i, 0 < a i) →
    Function.Injective q → (∀ i, (q i).Prime) → (∀ i j, a i < q j) →
    ∃ h M : ℕ, ∃ s c : Fin 7 → ℕ, 0<M ∧ (∀ i, 0<s i) ∧
      (∀ i t, q i^e i * (s i*t+c i) = a i*(h+M*t)+1) ∧
      (∀ i j, i≠j → s i*c j ≠ s j*c i) ∧
      ∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬p∣s i*t+c i

theorem main : H1 → H2 → OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1.H1 := by
  classical
  intro sieve forms a q e mono ap qi qp aq B
  obtain ⟨h,M,s,c,mp,sp,formula,cross,localGood⟩ := forms a q e mono ap qi qp aq
  obtain ⟨C,Cp,many⟩ := sieve s c sp cross localGood B
  let K := h+M
  have kp : 0<K := by dsimp [K]; omega
  have K1 : (1:ℝ)≤K := by exact_mod_cast kp
  refine ⟨(K:ℝ)*C,by positivity,?_⟩
  have kt : Tendsto (fun x : ℝ => x/(K:ℝ)) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  filter_upwards [kt.eventually many,kt.eventually (eventually_gt_atTop (1:ℝ))] with x many large
  obtain ⟨U,rate,rows⟩ := many
  let f (t : ℕ) := h+M*t
  have inj : Function.Injective f := by
    intro t u eq
    exact Nat.eq_of_mul_eq_mul_left mp (Nat.add_left_cancel eq)
  refine ⟨U.image f,?_,?_⟩
  · rw [card_image_of_injective _ inj]
    have xp : 0<x := by have := (lt_div_iff₀ (by positivity : (0:ℝ)<K)).mp large; linarith
    have logpos := Real.log_pos large
    have logle : log (x/K)≤log x := Real.log_le_log (by positivity) (div_le_self xp.le K1)
    calc
      _ ≤ x/(log (x/K))^7 := div_le_div_of_nonneg_left xp.le (by positivity)
        (pow_le_pow_left₀ logpos.le logle _)
      _ = (K:ℝ)*(x/K/(log (x/K))^7) := by field_simp
      _ ≤ (K:ℝ)*(C*U.card) := by gcongr
      _ = _ := by ring
  · intro n hn
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hn
    obtain ⟨tp,tx,parts,total⟩ := rows t ht
    have bp (i) : 0<q i^e i := pow_pos (qp i).pos _
    have val (i) : (a i*f t+1)/(q i^e i)=s i*t+c i := by
      change (a i*(h+M*t)+1)/(q i^e i)=_
      rw [←formula i t,Nat.mul_div_cancel_left _ (bp i)]
    have dp (i) : q i^e i ∣ a i*f t+1 := ⟨_,(formula i t).symm⟩
    have limit : f t≤K*t := by
      dsimp [f,K]
      nlinarith only [Nat.mul_le_mul_left h (show 1≤t from tp)]
    have ft : 0 < f t := by dsimp [f]; positivity
    refine ⟨ft,?_,?_,?_⟩
    · calc
        _ ≤ (K:ℝ)*t := by exact_mod_cast limit
        _ ≤ x := by rw [mul_comm]; exact (le_div_iff₀ (by positivity)).mp tx
    · intro i
      exact ⟨dp i,by simpa only [val] using parts i⟩
    · simpa only [val] using total

end OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1
end

section
/-! Heath-Brown's sieve in prescribed prime-power progressions. -/
namespace OMA.HeathCRT946
open Finset

private theorem affine_zero {h k m : ℕ} (mp : 0 < m) (cop : k.Coprime m) :
    ∃ t : ℕ, m ∣ k*t+h := by
  let _ : NeZero m := ⟨mp.ne'⟩
  refine ⟨(-(k:ZMod m)⁻¹ * (h:ZMod m)).val, (ZMod.natCast_eq_zero_iff _ _).mp ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val]
  rw [neg_mul, mul_neg, ←mul_assoc,ZMod.coe_mul_inv_eq_one _ cop]
  ring

/-- Divide the seven linear forms by prescribed, mutually coprime prime powers
on a single common arithmetic progression. The resulting forms are pairwise
nonproportional and have no fixed prime divisor in their product. -/
theorem forms (a q e : Fin 7 → ℕ) (mono : StrictMono a) (ap : ∀ i, 0<a i)
    (qi : Function.Injective q) (qp : ∀ i, (q i).Prime) (aq : ∀ i j, a i<q j) :
    ∃ h M : ℕ, ∃ s c : Fin 7 → ℕ, 0<M ∧ (∀ i, 0<s i) ∧
      (∀ i t, q i^e i * (s i*t+c i) = a i*(h+M*t)+1) ∧
      (∀ i j, i≠j → s i*c j ≠ s j*c i) ∧
      ∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬p∣s i*t+c i := by
  classical
  let b (i : Fin 7) := q i ^ e i
  have bp (i) : 0<b i := pow_pos (qp i).pos _
  have cop (i j) : (a i).Coprime (b j) := by
    apply Nat.Coprime.pow_right
    exact ((qp j).coprime_iff_not_dvd.mpr (fun dv =>
      (aq i j).not_ge (Nat.le_of_dvd (ap i) dv))).symm
  have pair (i j) (ne:i≠j) : (b i).Coprime (b j) := by
    exact (((Nat.coprime_primes (qp i) (qp j)).mpr (fun eq => ne (qi eq))).pow_left _).pow_right _
  choose res resprop using (fun i => affine_zero (h:=1) (bp i) (cop i i))
  let h := Nat.chineseRemainderOfFinset res b univ (fun i _ => (bp i).ne')
    (fun i _ j _ ne => pair i j ne)
  have dv (i) : b i∣a i*h.val+1 := by
    have u := ((h.property i (mem_univ _)).mul_left (a i)).add_right 1
    exact (Nat.modEq_zero_iff_dvd.mp (u.trans (Nat.modEq_zero_iff_dvd.mpr (resprop i))))
  let M := ∏ i, b i
  let rem (i : Fin 7) := ∏ j∈univ.erase i,b j
  have prod (i) : b i*rem i=M := mul_prod_erase _ _ (mem_univ _)
  have mp : 0<M := prod_pos fun i _ => bp i
  let s (i : Fin 7) := a i*rem i
  let c (i : Fin 7) := (a i*h.val+1)/b i
  have sp (i) : 0<s i := Nat.mul_pos (ap i) (prod_pos fun j _ => bp j)
  have sc (i) : b i*s i=a i*M := by
    change b i*(a i*rem i)=a i*M
    rw [←prod i]; ring
  have cc (i) : b i*c i=a i*h.val+1 := Nat.mul_div_cancel' (dv i)
  have form (i t) : b i*(s i*t+c i)=a i*(h.val+M*t)+1 := by
    rw [Nat.mul_add,←Nat.mul_assoc,sc,cc]; ring
  refine ⟨h.val,M,s,c,mp,sp,form,?_,?_⟩
  · intro i j ne eq
    have he : (b i*s i)*(b j*c j)=(b j*s j)*(b i*c i) := by
      calc
        _ = (b i*b j)*(s i*c j) := by ring
        _ = (b i*b j)*(s j*c i) := by rw [eq]
        _ = _ := by ring
    rw [sc,sc,cc,cc] at he
    have hmul : a i*M=a j*M := by nlinarith only [he]
    exact ne (mono.injective (Nat.eq_of_mul_eq_mul_right mp hmul))
  · intro p pp
    by_cases ∃ j, p∣b j
    · obtain ⟨j,pj⟩ := ‹∃ j, p∣b j›
      have eqp : p=q j := (Nat.prime_dvd_prime_iff_eq pp (qp j)).mp (pp.dvd_of_dvd_pow pj)
      have others (i) (ne:i≠j) (t) : ¬p∣s i*t+c i := by
        intro divides
        have pi : p∣a i*(h.val+M*t)+1 := form i t ▸ dvd_mul_of_dvd_right divides _
        have pj' : p∣a j*(h.val+M*t)+1 := form j t ▸ dvd_mul_of_dvd_left pj _
        have ei : (a i:ZMod p)*(h.val+M*t)+1 = 0 := by
          exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mpr pi
        have ej : (a j:ZMod p)*(h.val+M*t)+1 = 0 := by
          exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mpr pj'
        have eq : (a i : ZMod p) = a j := by
          linear_combination (a i:ZMod p)*ej-(a j:ZMod p)*ei
        have small (k) : a k < p := eqp ▸ aq k j
        have eql := (ZMod.natCast_eq_natCast_iff' _ _ _).mp eq
        rw [Nat.mod_eq_of_lt (small i),Nat.mod_eq_of_lt (small j)] at eql
        exact ne (mono.injective eql)
      have slope : ¬p∣s j := by
        have ar : p.Coprime (a j) := pp.coprime_iff_not_dvd.mpr (fun dvd =>
          (aq j j).not_ge (eqp ▸ Nat.le_of_dvd (ap j) dvd))
        have pr : p.Coprime (rem j) := by
          apply Nat.Coprime.prod_right
          intro k hk
          apply Nat.Coprime.pow_right
          rw [eqp]
          apply (Nat.coprime_primes (qp j) (qp k)).mpr
          exact fun e => (ne_of_mem_erase hk) (qi e).symm
        exact (pp.coprime_iff_not_dvd).mp (ar.mul_right pr)
      by_cases hit : p∣c j
      · refine ⟨1,fun i => ?_⟩
        by_cases ij:i=j
        · subst i
          simpa only [Nat.mul_one] using (fun v : p∣s j+c j => slope ((Nat.dvd_add_iff_left hit).mpr v))
        · exact others _ ij _
      · refine ⟨0,fun i => ?_⟩
        by_cases ij:i=j
        · simpa only [ij,Nat.mul_zero,Nat.zero_add] using hit
        · exact others _ ij _
    · rename_i none
      have pm : p.Coprime M := Nat.Coprime.prod_right fun i _ =>
        pp.coprime_iff_not_dvd.mpr (fun dv => none ⟨i,dv⟩)
      obtain ⟨t,tgood⟩ := affine_zero (h:=h.val) pp.pos pm.symm
      refine ⟨t,fun i bad => ?_⟩
      have pt : p∣a i*(h.val+M*t) := dvd_mul_of_dvd_right (Nat.add_comm _ _ ▸ tgood) _
      have left : p∣a i*(h.val+M*t)+1 := form i t ▸ dvd_mul_of_dvd_right bad _
      exact pp.not_dvd_one ((Nat.dvd_add_iff_right pt).mpr left)

end OMA.HeathCRT946
end

section
/-!
Separate the rough almost-prime supply from the loss caused by squares of
large primes. This follows the two inputs distinguished by Hildebrand
after Lemma 2 in The divisor function at consecutive integers.

Source: https://msp.org/pjm/1987/129-2/pjm-v129-n2-p06-s.pdf
Credit: @justusklocke-cloud
-/

open Filter Finset Real
open scoped Classical BigOperators

namespace OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1_H1_R1

/-- The rough almost-prime count before imposing squarefreeness. -/
def H1 : Prop :=
  ∀ s c : Fin 7 → ℕ, (∀ i, 0 < s i) →
    (∀ i j, i ≠ j → s i * c j ≠ s j * c i) →
    (∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬ p ∣ s i * t + c i) →
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ᶠ x : ℝ in atTop,
      ∃ V : Finset ℕ, x / (log x)^7 ≤ C * V.card ∧ ∀ n ∈ V, 0 < n ∧ (n : ℝ) ≤ x ∧
        let v := fun i => s i * n + c i
        (∀ i, 1 < v i ∧ ∀ p ∈ (v i).primeFactors, x ^ δ < (p : ℝ)) ∧
        (∑ i, (v i).primeFactors.card) ≤ 27

/-- A single linear form has negligibly many values with a large square factor. -/
def H2 : Prop :=
  ∀ a b : ℕ, 0 < a → ∀ δ K : ℝ, 0 < δ → 0 < K → ∀ᶠ x : ℝ in atTop,
    K * (((Icc 1 ⌊x⌋₊).filter fun n =>
      ∃ p ∈ (a * n + b).primeFactors, x ^ δ < (p : ℝ) ∧ p ^ 2 ∣ a * n + b).card : ℝ)
      ≤ x / (log x)^7

theorem main : H1 → H2 → OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1.H1 := by
  classical
  intro supply loss s c hs hdistinct hadm B
  obtain ⟨C, δ, hC, hδ, hmany⟩ := supply s c hs hdistinct hadm
  refine ⟨2 * C, by positivity, ?_⟩
  have hE : ∀ᶠ x : ℝ in atTop, ∀ i : Fin 7,
      (14 * C) * (((Icc 1 ⌊x⌋₊).filter fun n =>
        ∃ p ∈ (s i * n + c i).primeFactors, x ^ δ < (p : ℝ) ∧
          p ^ 2 ∣ s i * n + c i).card : ℝ) ≤ x / (log x)^7 :=
    eventually_all.mpr fun i => loss (s i) (c i) (hs i) δ (14 * C) hδ (by positivity)
  have hlarge := (tendsto_rpow_atTop hδ).eventually_ge_atTop (B : ℝ)
  filter_upwards [hmany, hE, hlarge] with x hmany hE hlarge
  obtain ⟨V, hVsize, hV⟩ := hmany
  let E (i : Fin 7) := (Icc 1 ⌊x⌋₊).filter fun n =>
    ∃ p ∈ (s i * n + c i).primeFactors, x ^ δ < (p : ℝ) ∧
      p ^ 2 ∣ s i * n + c i
  let U := V.filter (fun n => ∀ i : Fin 7, Squarefree (s i * n + c i))
  let D := V.filter (fun n => ¬ ∀ i : Fin 7, Squarefree (s i * n + c i))
  have hsub : D ⊆ univ.biUnion E := by
    intro n hn
    obtain ⟨hnV, hnot⟩ := mem_filter.mp hn
    obtain ⟨hnpos, hnx, hvalues, _⟩ := hV n hnV
    push Not at hnot
    obtain ⟨i, hi⟩ := hnot
    rw [Nat.squarefree_iff_prime_squarefree] at hi
    push Not at hi
    obtain ⟨p, hp, hsq⟩ := hi
    have hdvd : p ∣ s i * n + c i := (dvd_mul_right p p).trans hsq
    have hmem : p ∈ (s i * n + c i).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hdvd, (ne_of_gt ((hvalues i).1.trans' Nat.zero_lt_one))⟩
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr
      ⟨mem_Icc.mpr ⟨hnpos, Nat.le_floor hnx⟩,
        p, hmem, (hvalues i).2 p hmem, by simpa only [pow_two] using hsq⟩⟩
  have hsum : D.card ≤ ∑ i, (E i).card := (card_le_card hsub).trans card_biUnion_le
  have hbudget : (14 * C) * (D.card : ℝ) ≤ 7 * (x / (log x)^7) := by
    calc
      _ ≤ (14 * C) * (∑ i, ((E i).card : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast hsum
      _ = ∑ i, (14 * C) * ((E i).card : ℝ) := by rw [mul_sum]
      _ ≤ ∑ _i : Fin 7, x / (log x)^7 := sum_le_sum fun i _ => hE i
      _ = _ := by simp [nsmul_eq_mul]
  have hpartition : U.card + D.card = V.card := card_filter_add_card_filter_not _
  have hpartitionR : (V.card : ℝ) = (U.card : ℝ) + (D.card : ℝ) := by exact_mod_cast hpartition.symm
  refine ⟨U, ?_, ?_⟩
  · rw [hpartitionR, mul_add] at hVsize
    nlinarith only [hVsize, hbudget]
  · intro n hn
    obtain ⟨hnV, hsquare⟩ := mem_filter.mp hn
    obtain ⟨hnpos, hnx, hvalues, hcap⟩ := hV n hnV
    refine ⟨hnpos, hnx, fun i => ⟨(hvalues i).1, hsquare i, ?_⟩, hcap⟩
    intro p hp
    exact_mod_cast hlarge.trans_lt ((hvalues i).2 p hp)

end OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1_H1_R1
end

section
/-! Counting divisibility by large prime squares in affine forms. -/

open scoped BigOperators
open Filter

namespace Erdos946SquareFactorCount

/-- Two hits of divisibility by the same coprime modulus differ by a multiple of it. -/
lemma modulus_dvd_sub {a b q m n : ℕ} (hc : a.Coprime q) (hmn : m ≤ n)
    (hm : q ∣ a * m + b) (hn : q ∣ a * n + b) : q ∣ n - m := by
  have heq : (a * m + b) + a * (n - m) = a * n + b := by
    rw [Nat.add_right_comm, ← Nat.mul_add, Nat.add_sub_of_le hmn]
  have hsum : q ∣ (a * m + b) + a * (n - m) := by rwa [heq]
  exact hc.symm.dvd_of_dvd_mul_left ((Nat.dvd_add_iff_right hm).mpr hsum)

/-- A fixed coprime modulus has at most `N / q + 1` hits in `[1, N]`. -/
theorem card_dvd_affine_le {a b q N : ℕ} (hq : 0 < q) (hc : a.Coprime q) :
    ((Finset.Icc 1 N).filter (fun n => q ∣ a * n + b)).card ≤ N / q + 1 := by
  let S := (Finset.Icc 1 N).filter (fun n => q ∣ a * n + b)
  change S.card ≤ N / q + 1
  rw [← Finset.card_range (N / q + 1)]
  have injective_on_hits (m n : ℕ) (hm : m ∈ S) (hn : n ∈ S) (hmn : m ≤ n)
      (he : m / q = n / q) : m = n := by
    have hd := modulus_dvd_sub hc hmn (Finset.mem_filter.mp hm).2 (Finset.mem_filter.mp hn).2
    have hmdecomp := Nat.mod_add_div m q
    have hndecomp := Nat.mod_add_div n q
    rw [he] at hmdecomp
    have hmod := Nat.mod_lt n hq
    have hlt : n - m < q := by omega
    by_contra hne
    have hpos : 0 < n - m := by omega
    exact (not_le_of_gt hlt) (Nat.le_of_dvd hpos hd)
  apply Finset.card_le_card_of_injOn (fun n => n / q)
  · intro n hn
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2)
  · intro m hm n hn he
    rcases le_total m n with hmn | hnm
    · exact injective_on_hits m n hm hn hmn he
    · exact (injective_on_hits n m hn hm hnm he.symm).symm

/-- For a prime greater than the positive slope, there are at most `N / p² + 1` hits. -/
theorem card_prime_square_dvd_affine_le {a b p N : ℕ} (ha : 0 < a) (hp : p.Prime) (hap : a < p) :
    ((Finset.Icc 1 N).filter (fun n => p ^ 2 ∣ a * n + b)).card ≤ N / p ^ 2 + 1 := by
  have hpa : ¬p ∣ a := fun h => hap.not_ge (Nat.le_of_dvd ha h)
  exact card_dvd_affine_le (pow_pos hp.pos _) (hp.coprime_pow_of_not_dvd hpa)

/-- Union bound for a finite set of forbidden prime squares. -/
theorem card_bad_for_primes_le {a b N : ℕ} (ha : 0 < a) {P : Finset ℕ}
    (hp : ∀ p ∈ P, p.Prime) (hap : ∀ p ∈ P, a < p) :
    ((Finset.Icc 1 N).filter (fun n => ∃ p ∈ P, p ^ 2 ∣ a * n + b)).card ≤
      ∑ p ∈ P, (N / p ^ 2 + 1) := by
  classical
  let S (p : ℕ) := (Finset.Icc 1 N).filter (fun n => p ^ 2 ∣ a * n + b)
  have heq : (Finset.Icc 1 N).filter (fun n => ∃ p ∈ P, p ^ 2 ∣ a * n + b) = P.biUnion S := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_biUnion, S]
    tauto
  rw [heq]
  exact Finset.card_biUnion_le.trans
    (Finset.sum_le_sum fun p hpP => card_prime_square_dvd_affine_le ha (hp p hpP) (hap p hpP))

private lemma inverse_square_tail_le (B T : ℕ) (hB : 0 < B) :
    (∑ p ∈ Finset.Ioc B T, 1 / (p : ℝ) ^ 2) ≤ 1 / (B : ℝ) := by
  let shift : ℕ ↪ ℕ := ⟨fun k => B + k + 1, by
    intro x y h
    change B + x + 1 = B + y + 1 at h
    omega⟩
  have hIoc : (Finset.range (T - B)).map shift = Finset.Ioc B T := by
    ext p
    simp only [Finset.mem_map, Finset.mem_range, Finset.mem_Ioc]
    change (∃ k : ℕ, k < T - B ∧ B + k + 1 = p) ↔ B < p ∧ p ≤ T
    exact ⟨by rintro ⟨k, hk, rfl⟩; omega, fun hp => ⟨p - B - 1, by omega, by omega⟩⟩
  rw [← hIoc, Finset.sum_map]
  change (∑ k ∈ Finset.range (T - B), 1 / ((B + k + 1 : ℕ) : ℝ) ^ 2) ≤ _
  let f (k : ℕ) : ℝ := 1 / ((B + k : ℕ) : ℝ)
  calc
    _ ≤ ∑ k ∈ Finset.range (T - B), (f k - f (k + 1)) := by
      refine Finset.sum_le_sum fun k _ => ?_
      let c : ℝ := ((B + k : ℕ) : ℝ)
      have hc : 0 < c := by dsimp [c]; exact_mod_cast (show 0 < B + k by omega)
      have hshift : ((B + k + 1 : ℕ) : ℝ) = c + 1 := by simp only [Nat.cast_add, Nat.cast_one, c]
      rw [hshift]
      have hf : f (k + 1) = 1 / (c + 1) := by dsimp [f]; rw [← Nat.add_assoc, hshift]
      rw [hf]
      change 1 / (c + 1) ^ 2 ≤ 1 / c - 1 / (c + 1)
      calc
        _ ≤ 1 / (c * (c + 1)) := by
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith
        _ = _ := by
          field_simp
          ring
    _ = f 0 - f (T - B) := Finset.sum_range_sub' f _
    _ ≤ 1 / (B : ℝ) := by simpa [f] using sub_le_self (f 0) (show 0 ≤ f (T - B) by dsimp [f]; positivity)

/-- Indices with a prime square divisor of `a * n + b` whose prime exceeds `B`. -/
def largePrimeSquareRows (a b B N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n =>
    ∃ p ∈ (Finset.Ioc B (Nat.sqrt (a * N + b))).filter Nat.Prime, p ^ 2 ∣ a * n + b

theorem mem_largePrimeSquareRows {a b B N n : ℕ} (ha : 0 < a) :
    n ∈ largePrimeSquareRows a b B N ↔
      n ∈ Finset.Icc 1 N ∧ ∃ p, p.Prime ∧ B < p ∧ p ^ 2 ∣ a * n + b := by
  rw [largePrimeSquareRows, Finset.mem_filter]
  refine and_congr_right fun hn => ⟨?_, ?_⟩
  · rintro ⟨p, hp, hd⟩
    obtain ⟨hpi, hp⟩ := Finset.mem_filter.mp hp
    exact ⟨p, hp, (Finset.mem_Ioc.mp hpi).1, hd⟩
  · rintro ⟨p, hp, hBp, hd⟩
    have hpos : 0 < a * n + b := by
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      positivity
    have hupper : a * n + b ≤ a * N + b := by gcongr; exact (Finset.mem_Icc.mp hn).2
    have hcutoff : p ≤ Nat.sqrt (a * N + b) :=
      Nat.le_sqrt'.mpr ((Nat.le_of_dvd hpos hd).trans hupper)
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hBp, hcutoff⟩, hp⟩, hd⟩

/-- The total large-prime square loss is bounded by `N / B + sqrt (a * N + b)`. -/
theorem card_largePrimeSquareRows_le {a b B N : ℕ} (ha : 0 < a) (haB : a ≤ B) :
    ((largePrimeSquareRows a b B N).card : ℝ) ≤ N / (B : ℝ) + Nat.sqrt (a * N + b) := by
  let T := Nat.sqrt (a * N + b)
  let P := (Finset.Ioc B T).filter Nat.Prime
  have hP : P ⊆ Finset.Ioc B T := Finset.filter_subset _ _
  have hcount : (largePrimeSquareRows a b B N).card ≤ ∑ p ∈ P, (N / p ^ 2 + 1) :=
    card_bad_for_primes_le ha (fun _ hp => (Finset.mem_filter.mp hp).2)
      (fun _ hp => haB.trans_lt (Finset.mem_Ioc.mp (hP hp)).1)
  have hsum : (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ≤ 1 / (B : ℝ) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hP (by intros; positivity)).trans
      (inverse_square_tail_le B T (ha.trans_le haB))
  have hcard : P.card ≤ T := by
    calc
      _ ≤ (Finset.Ioc B T).card := Finset.card_le_card hP
      _ ≤ T := by simp
  change ((largePrimeSquareRows a b B N).card : ℝ) ≤ N / (B : ℝ) + T
  calc
    _ ≤ ((∑ p ∈ P, (N / p ^ 2 + 1) : ℕ) : ℝ) := by exact_mod_cast hcount
    _ ≤ ∑ p ∈ P, ((N : ℝ) * (1 / (p : ℝ) ^ 2) + 1) := by
      push_cast
      refine Finset.sum_le_sum fun p _ => ?_
      have h := Nat.cast_div_le (α := ℝ) (m := N) (n := p ^ 2)
      push_cast at h
      simpa only [mul_one_div] using add_le_add h (le_refl (1 : ℝ))
    _ = (N : ℝ) * (∑ p ∈ P, 1 / (p : ℝ) ^ 2) + P.card := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp
    _ ≤ (N : ℝ) * (1 / (B : ℝ)) + T :=
      add_le_add (mul_le_mul_of_nonneg_left hsum (by positivity)) (by exact_mod_cast hcard)
    _ = _ := by rw [mul_one_div]

private lemma eventually_pow_log_le {r C : ℝ} (hr : 0 < r) (hC : 0 < C) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ (7 : ℕ) ≤ C * x ^ r := by
  have ho : (fun x : ℝ => Real.log x ^ (7 : ℕ)) =o[atTop] (fun x => x ^ r) := by
    simpa only [Real.rpow_natCast] using isLittleO_log_rpow_rpow_atTop (↑(7 : ℕ)) hr
  filter_upwards [(Asymptotics.isLittleO_iff.mp ho) hC, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 ≤ x := zero_le_one.trans hx1.le
  simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Real.log_nonneg hx1.le) _),
    abs_of_nonneg (Real.rpow_nonneg hx0 _)] using hx

/-- For fixed coefficients, subsampling to exclude large square divisors loses
`o(x / (log x)^7)` values. -/
theorem square_loss (a b : ℕ) (ha : 0 < a) (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K) :
    ∀ᶠ x : ℝ in atTop,
      K * (((Finset.Icc 1 ⌊x⌋₊).filter fun n =>
        ∃ p ∈ (a * n + b).primeFactors, x ^ δ < (p : ℝ) ∧ p ^ 2 ∣ a * n + b).card : ℝ) ≤
      x / (Real.log x)^7 := by
  let A : ℝ := Real.sqrt ((a : ℝ) + b)
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hA : 0 < A := by dsimp [A]; positivity
  have hlarge := (tendsto_rpow_atTop hδ).eventually_ge_atTop (max 2 (a : ℝ))
  have hlogδ := eventually_pow_log_le hδ (show 0 < 1 / (4 * K) by positivity)
  have hloghalf := eventually_pow_log_le (show (0 : ℝ) < 1 / 2 by norm_num)
    (show 0 < 1 / (2 * K * A) by positivity)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hlarge, hlogδ, hloghalf] with x hx1 hlarge hlogδ hloghalf
  let N := ⌊x⌋₊
  let B := ⌊x ^ δ⌋₊
  let V := (Finset.Icc 1 N).filter fun n =>
    ∃ p ∈ (a * n + b).primeFactors, x ^ δ < (p : ℝ) ∧ p ^ 2 ∣ a * n + b
  have hx : 0 < x := zero_lt_one.trans hx1
  have hxδ : 0 < x ^ δ := Real.rpow_pos_of_pos hx _
  have hN : (N : ℝ) ≤ x := Nat.floor_le hx.le
  have haB : a ≤ B := Nat.le_floor ((le_max_right _ _).trans hlarge)
  have hBhalf : x ^ δ / 2 ≤ (B : ℝ) := by
    have hxδ2 := (le_max_left (2 : ℝ) (a : ℝ)).trans hlarge
    have hceil : x ^ δ < (B : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hB : 0 < (B : ℝ) := (div_pos hxδ (by norm_num)).trans_le hBhalf
  have hV : V ⊆ largePrimeSquareRows a b B N := by
    intro n hn
    obtain ⟨hn, p, hp, hpx, hd⟩ := Finset.mem_filter.mp hn
    have hBp : (B : ℝ) < p := (Nat.floor_le hxδ.le).trans_lt hpx
    exact (mem_largePrimeSquareRows ha).mpr
      ⟨hn, p, Nat.prime_of_mem_primeFactors hp, by exact_mod_cast hBp, hd⟩
  have hcard : (V.card : ℝ) ≤ N / (B : ℝ) + Nat.sqrt (a * N + b) :=
    (show (V.card : ℝ) ≤ (largePrimeSquareRows a b B N).card by
      exact_mod_cast Finset.card_le_card hV).trans (card_largePrimeSquareRows_le ha haB)
  have hquot : (N : ℝ) / (B : ℝ) ≤ 2 * x / (x ^ δ) := by
    calc
      _ ≤ x / (B : ℝ) := div_le_div_of_nonneg_right hN hB.le
      _ ≤ x / (x ^ δ / 2) := div_le_div_of_nonneg_left hx.le (by positivity) hBhalf
      _ = _ := by field_simp [hxδ.ne']
  have hsqrt : (Nat.sqrt (a * N + b) : ℝ) ≤ A * Real.sqrt x := by
    calc
      _ ≤ Real.sqrt ((a * N + b : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
      _ ≤ Real.sqrt (((a : ℝ) + b) * x) := by
        apply Real.sqrt_le_sqrt
        push_cast
        nlinarith only [mul_le_mul_of_nonneg_left hN haR.le,
          mul_le_mul_of_nonneg_left hx1.le (Nat.cast_nonneg b)]
      _ = _ := Real.sqrt_mul (by positivity) x
  have hlogpos : 0 < Real.log x ^ (7 : ℕ) := pow_pos (Real.log_pos hx1) _
  have htermδ : K * (2 * x / x ^ δ) * Real.log x ^ (7 : ℕ) ≤ x / 2 := by
    calc
      _ ≤ (K * (2 * x / x ^ δ)) * (1 / (4 * K) * x ^ δ) :=
        mul_le_mul_of_nonneg_left hlogδ (by positivity)
      _ = _ := by
        field_simp [hK.ne', hxδ.ne']
        ring
  have htermsqrt : K * (A * Real.sqrt x) * Real.log x ^ (7 : ℕ) ≤ x / 2 := by
    rw [← Real.sqrt_eq_rpow] at hloghalf
    calc
      _ ≤ (K * (A * Real.sqrt x)) * (1 / (2 * K * A) * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hloghalf (by positivity)
      _ = (K * A * (1 / (2 * K * A))) * (Real.sqrt x * Real.sqrt x) := by ring
      _ = _ := by
        rw [Real.mul_self_sqrt hx.le]
        field_simp [hK.ne', hA.ne']
  change K * (V.card : ℝ) ≤ x / Real.log x ^ (7 : ℕ)
  apply (le_div_iff₀ hlogpos).mpr
  calc
    _ ≤ K * (2 * x / (x ^ δ) + A * Real.sqrt x) * Real.log x ^ (7 : ℕ) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (hcard.trans (add_le_add hquot hsqrt)) hK.le) hlogpos.le
    _ ≤ x := by
      rw [mul_add, add_mul]
      exact (add_le_add htermδ htermsqrt).trans_eq (by ring)

end Erdos946SquareFactorCount
end

theorem OMA.solution : OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1.H1 :=
  OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1.main
    (OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1_H1_R1.main
      Erdos946Sieve2.rough_almost_prime_supply
      Erdos946SquareFactorCount.square_loss)
    OMA.HeathCRT946.forms
