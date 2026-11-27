import OMAReductions.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1_H1_R1
import Mathlib

/-! Finite Abel summation identity for Chebyshev theta against `1 / (t^2 * log t)`. -/

section RobinThetaAbelIdentity
open Real Finset MeasureTheory

private noncomputable def kernelK (t : ℝ) : ℝ :=
  (2 * log t + 1) / (t ^ 3 * (log t) ^ 2)

private noncomputable def antiderivW (t : ℝ) : ℝ :=
  -1 / (t ^ 2 * log t)

private lemma hasDerivAt_antiderivW {t : ℝ} (ht : 1 < t) :
    HasDerivAt antiderivW (kernelK t) t := by
  have ht0 : 0 < t := by linarith
  have hlog : 0 < log t := Real.log_pos ht
  have hd_pow : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t ^ (2 - 1)) t := hasDerivAt_pow 2 t
  have hd_log : HasDerivAt log t⁻¹ t := Real.hasDerivAt_log ht0.ne'
  have hd_prod : HasDerivAt (fun u : ℝ => u ^ 2 * log u)
      ((2 * t ^ (2 - 1)) * log t + t ^ 2 * t⁻¹) t := hd_pow.mul hd_log
  have hprod_ne : t ^ 2 * log t ≠ 0 := mul_ne_zero (pow_ne_zero 2 ht0.ne') hlog.ne'
  have hd_div := (hasDerivAt_const t (-1 : ℝ)).div hd_prod hprod_ne
  refine hd_div.congr_deriv ?_
  unfold kernelK
  have ht_ne : t ≠ 0 := ht0.ne'
  have hl_ne : log t ≠ 0 := hlog.ne'
  field_simp [ht_ne, hl_ne]
  ring

private lemma continuousOn_kernelK {u v : ℝ} (hu : 1 < u) :
    ContinuousOn kernelK (Set.Icc u v) := by
  have hlog_cont : ContinuousOn log (Set.Icc u v) :=
    Real.continuousOn_log.mono fun x (hx : x ∈ Set.Icc u v) =>
      (lt_of_lt_of_le (by linarith : (0 : ℝ) < u) hx.1).ne'
  unfold kernelK
  refine ContinuousOn.div ((continuousOn_const.mul hlog_cont).add continuousOn_const)
    ((continuousOn_id.pow 3).mul (hlog_cont.pow 2)) ?_
  intro x hx
  have hx1 : 1 < x := lt_of_lt_of_le hu hx.1
  have hx0 : 0 < x := by linarith
  have hlog : 0 < log x := Real.log_pos hx1
  exact mul_ne_zero (pow_ne_zero 3 hx0.ne') (pow_ne_zero 2 hlog.ne')

private lemma integral_kernelK_Ioc {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    (∫ t in Set.Ioc u v, kernelK t) = 1 / (u ^ 2 * log u) - 1 / (v ^ 2 * log v) := by
  rw [← intervalIntegral.integral_of_le huv]
  have huicc : Set.uIcc u v = Set.Icc u v := Set.uIcc_of_le huv
  have hcont : ContinuousOn kernelK (Set.uIcc u v) := by
    rw [huicc]; exact continuousOn_kernelK hu
  have hderiv : ∀ x ∈ Set.uIcc u v, HasDerivAt antiderivW (kernelK x) x := by
    rw [huicc]
    intro x hx
    exact hasDerivAt_antiderivW (lt_of_lt_of_le hu hx.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  unfold antiderivW
  ring

private lemma setIntegral_finset_sum_real {S : Finset ℕ} {A : Set ℝ} {f : ℕ → ℝ → ℝ}
    (hf : ∀ p ∈ S, IntegrableOn (f p) A) :
    (∫ t in A, ∑ p ∈ S, f p t) = ∑ p ∈ S, ∫ t in A, f p t := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have ha_int : IntegrableOn (f a) A := hf a (mem_insert_self a S)
    have hS_int : ∀ p ∈ S, IntegrableOn (f p) A := fun p hp => hf p (mem_insert_of_mem hp)
    have hsum_int : IntegrableOn (fun t => ∑ p ∈ S, f p t) A := by
      clear ha_int hf ha ih
      induction S using Finset.induction_on with
      | empty => simp
      | insert b T hb ihT =>
        have hb_int := hS_int b (mem_insert_self b T)
        have hT_int := ihT (fun p hp => hS_int p (mem_insert_of_mem hp))
        have hfn : (fun t => ∑ p ∈ insert b T, f p t) = fun t => f b t + ∑ p ∈ T, f p t := by
          ext t; exact sum_insert hb
        rw [hfn]
        exact hb_int.add hT_int
    have hfn_a : (fun t => ∑ p ∈ insert a S, f p t) = fun t => f a t + ∑ p ∈ S, f p t := by
      ext t; exact sum_insert ha
    rw [hfn_a, sum_insert ha, integral_add ha_int hsum_int, ih hS_int]

theorem OMA.solution : OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1_H1_R1.H3 := by
  classical
  intro s b hs hsb
  have hs0 : 0 ≤ s := by linarith
  have hb0 : 0 ≤ b := by linarith
  let P := (Icc 0 ⌊b⌋₊).filter Nat.Prime
  have htheta_eq : ∀ t ∈ Set.Ioc s b,
      kernelK t * Chebyshev.theta t =
        ∑ p ∈ P, Set.indicator (Set.Ici (p : ℝ)) (fun u => kernelK u * log p) t := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have htb : t ≤ b := ht.2
    have hfl_le : ⌊t⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono htb
    have hsub : (Icc 0 ⌊t⌋₊).filter Nat.Prime = P.filter (fun p : ℕ => (p : ℝ) ≤ t) := by
      ext p
      simp only [P, mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨hp0, hpt⟩, hpr⟩
        exact ⟨⟨⟨hp0, hpt.trans hfl_le⟩, hpr⟩, (Nat.le_floor_iff ht0).mp hpt⟩
      · rintro ⟨⟨⟨hp0, _⟩, hpr⟩, hpt⟩
        exact ⟨⟨hp0, (Nat.le_floor_iff ht0).mpr hpt⟩, hpr⟩
    rw [Chebyshev.theta_eq_sum_Icc, hsub, mul_sum, sum_filter]
    refine sum_congr rfl fun p _ => ?_
    by_cases hpt : (p : ℝ) ≤ t
    · simp [Set.indicator_of_mem, hpt]
    · simp [Set.indicator_of_notMem, hpt]
  have hint_K : IntegrableOn kernelK (Set.Ioc s b) :=
    (continuousOn_kernelK hs).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hint_term : ∀ p ∈ P,
      IntegrableOn (Set.indicator (Set.Ici (p : ℝ)) (fun u => kernelK u * log p)) (Set.Ioc s b) := by
    intro p _
    exact (hint_K.mul_const (log p)).indicator measurableSet_Ici
  have hint_eq : (∫ t in Set.Ioc s b, kernelK t * Chebyshev.theta t) =
      ∑ p ∈ P, ∫ t in Set.Ioc s b,
        Set.indicator (Set.Ici (p : ℝ)) (fun u => kernelK u * log p) t := by
    rw [setIntegral_congr_fun measurableSet_Ioc htheta_eq, setIntegral_finset_sum_real hint_term]
  have hpart : P = (Icc 0 ⌊s⌋₊).filter Nat.Prime ∪ (Ioc ⌊s⌋₊ ⌊b⌋₊).filter Nat.Prime := by
    have hsb_fl : ⌊s⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hsb
    ext p
    simp only [P, mem_union, mem_filter, mem_Icc, mem_Ioc]
    by_cases hp : p.Prime
    · simp only [hp, and_true]; omega
    · simp [hp]
  have hdisj : Disjoint ((Icc 0 ⌊s⌋₊).filter Nat.Prime) ((Ioc ⌊s⌋₊ ⌊b⌋₊).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [mem_filter, mem_Icc, mem_Ioc] at hp1 hp2
    omega
  have hsum_low : (∑ p ∈ (Icc 0 ⌊s⌋₊).filter Nat.Prime,
      ∫ t in Set.Ioc s b, Set.indicator (Set.Ici (p : ℝ)) (fun u => kernelK u * log p) t) =
      Chebyshev.theta s / (s ^ 2 * log s) -
        (∑ p ∈ (Icc 0 ⌊s⌋₊).filter Nat.Prime, log (p : ℝ)) / (b ^ 2 * log b) := by
    have hterm : ∀ p ∈ (Icc 0 ⌊s⌋₊).filter Nat.Prime,
        (∫ t in Set.Ioc s b, Set.indicator (Set.Ici (p : ℝ)) (fun u => kernelK u * log p) t) =
          log (p : ℝ) / (s ^ 2 * log s) - log (p : ℝ) / (b ^ 2 * log b) := by
      intro p hp
      simp only [mem_filter, mem_Icc] at hp
      have hps : (p : ℝ) ≤ s := (Nat.le_floor_iff hs0).mp hp.1.2
      have hinter : Set.Ioc s b ∩ Set.Ici (p : ℝ) = Set.Ioc s b :=
        Set.inter_eq_left.mpr fun t ht => hps.trans ht.1.le
      rw [setIntegral_indicator measurableSet_Ici, hinter, integral_mul_const,
        integral_kernelK_Ioc hs hsb]
      ring
    rw [sum_congr rfl hterm, sum_sub_distrib, ← sum_div, ← sum_div, ← Chebyshev.theta_eq_sum_Icc]
  have hsum_high : (∑ p ∈ (Ioc ⌊s⌋₊ ⌊b⌋₊).filter Nat.Prime,
      ∫ t in Set.Ioc s b, Set.indicator (Set.Ici (p : ℝ)) (fun u => kernelK u * log p) t) =
      (∑ p ∈ (Ioc ⌊s⌋₊ ⌊b⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ ^ 2) -
        (∑ p ∈ (Ioc ⌊s⌋₊ ⌊b⌋₊).filter Nat.Prime, log (p : ℝ)) / (b ^ 2 * log b) := by
    have hterm : ∀ p ∈ (Ioc ⌊s⌋₊ ⌊b⌋₊).filter Nat.Prime,
        (∫ t in Set.Ioc s b, Set.indicator (Set.Ici (p : ℝ)) (fun u => kernelK u * log p) t) =
          (p : ℝ)⁻¹ ^ 2 - log (p : ℝ) / (b ^ 2 * log b) := by
      intro p hp
      simp only [mem_filter, mem_Ioc] at hp
      have hsp : s < (p : ℝ) := Nat.lt_of_floor_lt hp.1.1
      have hpb : (p : ℝ) ≤ b := (Nat.le_floor_iff hb0).mp hp.1.2
      have hp1 : 1 < (p : ℝ) := hs.trans hsp
      have hp0 : (0 : ℝ) < p := by linarith
      have hlogp : 0 < log (p : ℝ) := Real.log_pos hp1
      have hinter : Set.Ioc s b ∩ Set.Ici (p : ℝ) = Set.Icc (p : ℝ) b := by
        ext t; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
        exact ⟨fun ⟨⟨_, htb⟩, hpt⟩ => ⟨hpt, htb⟩, fun ⟨hpt, htb⟩ => ⟨⟨hsp.trans_le hpt, htb⟩, hpt⟩⟩
      rw [setIntegral_indicator measurableSet_Ici, hinter, MeasureTheory.integral_Icc_eq_integral_Ioc,
        integral_mul_const, integral_kernelK_Ioc hp1 hpb]
      have hsimp : (1 / ((p : ℝ) ^ 2 * log (p : ℝ))) * log (p : ℝ) = (p : ℝ)⁻¹ ^ 2 := by
        field_simp [hp0.ne', hlogp.ne']
      rw [sub_mul, hsimp, one_div_mul_eq_div]
    rw [sum_congr rfl hterm, sum_sub_distrib, ← sum_div]
  have hth_b : Chebyshev.theta b =
      (∑ p ∈ (Icc 0 ⌊s⌋₊).filter Nat.Prime, log (p : ℝ)) +
      (∑ p ∈ (Ioc ⌊s⌋₊ ⌊b⌋₊).filter Nat.Prime, log (p : ℝ)) := by
    have h1 : Chebyshev.theta b = ∑ p ∈ P, log (p : ℝ) := Chebyshev.theta_eq_sum_Icc b
    rw [h1, hpart, sum_union hdisj]
  change Chebyshev.theta s / (s ^ 2 * log s) +
      (∑ p ∈ (Ioc ⌊s⌋₊ ⌊b⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ ^ 2) =
    Chebyshev.theta b / (b ^ 2 * log b) + (∫ t in Set.Ioc s b, kernelK t * Chebyshev.theta t)
  rw [hint_eq, hpart, sum_union hdisj, hsum_low, hsum_high, hth_b, add_div]
  ring

end RobinThetaAbelIdentity
