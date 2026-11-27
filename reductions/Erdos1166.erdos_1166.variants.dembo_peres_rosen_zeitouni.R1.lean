import FormalConjectures.ErdosProblems.«1166»
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi

/-!
# Dyadic tail bounds for the planar random-walk maximum

The hypotheses are the summable upper and lower deviation bounds on dyadic
times. Borel–Cantelli gives convergence there, then monotonicity of the
maximum interpolates between consecutive dyadic times. Pushing forward
to the space of increment sequences makes the hypotheses apply to the law
of the walk on any sample space. The upper-tail bound
is the estimate of Dembo–Peres–Rosen–Zeitouni (2001), equation (5.12).
The sharp lower tail is obtained from independent blocks using (5.7).
-/

namespace OMA.R_Erdos1166_erdos_1166_variants_dembo_peres_rosen_zeitouni_R1

open Erdos1165 Erdos1166 MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Real Topology ENNReal

private theorem max_mono {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) :
    Monotone (fun n => maxLocalTime X n ω) := by
  intro m n h
  change (Finset.range (m + 1)).sup (fun k => localTime X m ω (position X k ω)) ≤
    maxLocalTime X n ω
  apply Finset.sup_le
  intro k _
  calc
    localTime X m ω (position X k ω) ≤ localTime X n ω (position X k ω) := by
      apply Finset.card_le_card
      exact Finset.filter_subset_filter _ (Finset.range_mono (Nat.succ_le_succ h))
    _ ≤ maxLocalTime X n ω := localTime_le_maxLocalTime _ _ _ _

private theorem dyadic_interpolate {T : ℕ → ℕ} (hm : Monotone T) {c : ℝ}
    (h : Tendsto (fun k : ℕ => (T (2 ^ k) : ℝ) / (Real.log ((2 ^ k : ℕ) : ℝ)) ^ 2)
      atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (T n : ℝ) / (Real.log n) ^ 2) atTop (𝓝 c) := by
  let j := Nat.log 2
  let d (n : ℕ) := (Real.log (n : ℝ)) ^ 2
  let a (k : ℕ) := (T (2 ^ k) : ℝ) / d (2 ^ k)
  let r (k : ℕ) := (k : ℝ) / ((k : ℝ) + 1)
  let lo (n : ℕ) := (T (2 ^ j n) : ℝ) / d (2 ^ (j n + 1))
  let hi (n : ℕ) := (T (2 ^ (j n + 1)) : ℝ) / d (2 ^ j n)
  have hj : Tendsto j atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (2 ^ b : ℕ)] with n hn
    exact Nat.le_log_of_pow_le (by decide) hn
  have hj' : Tendsto (fun n => j n + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [tendsto_atTop.mp hj k] with n hn
    exact hn.trans (Nat.le_succ _)
  have hr : Tendsto r atTop (𝓝 1) := tendsto_natCast_div_add_atTop (1 : ℝ)
  have hri : Tendsto (fun k => (r k)⁻¹) atTop (𝓝 1) := by
    simpa using hr.inv₀ one_ne_zero
  have hl : Tendsto (fun n => a (j n) * r (j n) ^ 2) atTop (𝓝 c) := by
    simpa [a, d] using (h.comp hj).mul ((hr.comp hj).pow 2)
  have hh : Tendsto (fun n => a (j n + 1) * ((r (j n))⁻¹) ^ 2) atTop (𝓝 c) := by
    simpa [a, d] using (h.comp hj').mul ((hri.comp hj).pow 2)
  have hlog (k : ℕ) : Real.log ((2 ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
    simp [Real.log_pow]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hj_pos : ∀ᶠ n in atTop, 0 < j n :=
    (tendsto_atTop.mp hj 1).mono (fun _ h => h)
  have hlo : Tendsto lo atTop (𝓝 c) := by
    apply hl.congr'
    filter_upwards [hj_pos] with n hn
    have hj0 : (0 : ℝ) < (j n : ℝ) := by exact_mod_cast hn
    simp only [lo, a, d, hlog, r, Nat.cast_add, Nat.cast_one]
    field_simp
  have hhi : Tendsto hi atTop (𝓝 c) := by
    apply hh.congr'
    filter_upwards [hj_pos] with n hn
    have hj0 : (0 : ℝ) < (j n : ℝ) := by exact_mod_cast hn
    simp only [hi, a, d, hlog, r, Nat.cast_add, Nat.cast_one]
    field_simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hn1 : 1 < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hlo : 2 ^ j n ≤ n := Nat.pow_log_le_self _ (by omega)
    have hhi : n < 2 ^ (j n + 1) := Nat.lt_pow_succ_log_self (by decide) n
    change lo n ≤ (T n : ℝ) / d n
    calc
      lo n ≤ (T n : ℝ) / d (2 ^ (j n + 1)) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hm hlo) (sq_nonneg _)
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left (by positivity) (pow_pos (Real.log_pos hn1) 2)
        exact pow_le_pow_left₀ (Real.log_pos hn1).le
          (Real.log_le_log hn0 (by exact_mod_cast hhi.le)) 2
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hj1 : 1 ≤ j n := Nat.le_log_of_pow_le (by decide)
      (by simpa using hn : 2 ^ 1 ≤ n)
    have hj2 : 1 < (2 ^ j n : ℕ) :=
      (by decide : 1 < 2 ^ 1).trans_le (Nat.pow_le_pow_right (by decide) hj1)
    have hj0 : 0 < ((2 ^ j n : ℕ) : ℝ) := by positivity
    have hlo : 2 ^ j n ≤ n := Nat.pow_log_le_self _ (by omega)
    have hhi : n < 2 ^ (j n + 1) := Nat.lt_pow_succ_log_self (by decide) n
    change (T n : ℝ) / d n ≤ hi n
    calc
      _ ≤ (T (2 ^ (j n + 1)) : ℝ) / d n :=
        div_le_div_of_nonneg_right (by exact_mod_cast hm hhi.le) (sq_nonneg _)
      _ ≤ _ := by
        have hp : 0 < Real.log ((2 ^ j n : ℕ) : ℝ) :=
          Real.log_pos (by exact_mod_cast hj2)
        apply div_le_div_of_nonneg_left (by positivity) (pow_pos hp 2)
        exact pow_le_pow_left₀ hp.le (Real.log_le_log hj0 (by exact_mod_cast hlo)) 2

/-- Summable upper deviations on the dyadic sequence. -/
def H1 : Prop :=
  ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}, IsSimpleRandomWalkSteps X →
    ∀ ε : ℝ, 0 < ε →
      (∑' k : ℕ, ℙ {ω | 1 / π + ε <
        (maxLocalTime X (2 ^ k) ω : ℝ) / (Real.log ((2 ^ k : ℕ) : ℝ)) ^ 2}) ≠ ∞

/-- Summable lower deviations on the dyadic sequence. -/
def H2 : Prop :=
  ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}, IsSimpleRandomWalkSteps X →
    ∀ ε : ℝ, 0 < ε →
      (∑' k : ℕ, ℙ {ω | (maxLocalTime X (2 ^ k) ω : ℝ) /
        (Real.log ((2 ^ k : ℕ) : ℝ)) ^ 2 < 1 / π - ε}) ≠ ∞

theorem limit_of_tails (h₁ : H1) (h₂ : H2)
    {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) :
    ∀ᵐ ω, Tendsto (fun n : ℕ => (maxLocalTime X n ω : ℝ) / (Real.log n) ^ 2)
      atTop (𝓝 (1 / π)) := by
  let R (k : ℕ) (ω : Ω) := (maxLocalTime X (2 ^ k) ω : ℝ) /
    (Real.log ((2 ^ k : ℕ) : ℝ)) ^ 2
  let δ (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hδ (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
  have hUpper (j : ℕ) : ∀ᵐ ω, ∀ᶠ k in atTop, R k ω ≤ 1 / π + δ j := by
    simpa only [R, Set.mem_ofPred_eq, not_lt] using ae_eventually_notMem (h₁ hX (δ j) (hδ j))
  have hLower (j : ℕ) : ∀ᵐ ω, ∀ᶠ k in atTop, 1 / π - δ j ≤ R k ω := by
    simpa only [R, Set.mem_ofPred_eq, not_lt] using ae_eventually_notMem (h₂ hX (δ j) (hδ j))
  filter_upwards [ae_all_iff.mpr hUpper, ae_all_iff.mpr hLower] with ω hUp hLow
  apply dyadic_interpolate (max_mono X ω)
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hsmall : ∀ᶠ j in atTop, δ j < ε := hlim (gt_mem_nhds hε)
  obtain ⟨j, hj⟩ := hsmall.exists
  filter_upwards [hUp j, hLow j] with k hk₁ hk₂
  rw [Real.dist_eq, abs_lt]
  change -ε < R k ω - 1 / π ∧ R k ω - 1 / π < ε
  exact ⟨by linarith, by linarith⟩

theorem main : H1 → H2 → type_of% @Erdos1166.erdos_1166.variants.dembo_peres_rosen_zeitouni := by
  intro h₁ h₂ Ω _ _ X hX
  let Path := ℕ → ℤ × ℤ
  let p (ω : Ω) : Path := fun k => X k ω
  have hp : Measurable p := measurable_pi_iff.2 hX.measurable
  let ν : Measure Path := Measure.map p (ℙ : Measure Ω)
  let : MeasureSpace Path := ⟨ν⟩
  have : IsProbabilityMeasure (ℙ : Measure Path) := Measure.isProbabilityMeasure_map hp.aemeasurable
  let Y (k : ℕ) (z : Path) := z k
  have hYm (k : ℕ) : Measurable (Y k) := measurable_pi_apply k
  have hmap (k : ℕ) : Measure.map (Y k) ν = Measure.map (X k) (ℙ : Measure Ω) :=
    Measure.map_map (hYm k) hp
  have hY : IsSimpleRandomWalkSteps Y := by
    refine ⟨hYm, ?_, fun k => ?_⟩
    · change iIndepFun Y ν
      rw [iIndepFun_iff_map_fun_eq_infinitePi_map hYm]
      change Measure.map id ν = Measure.infinitePi (fun k => Measure.map (Y k) ν)
      simp only [Measure.map_id, hmap]
      exact hX.indep.map_fun_eq_infinitePi_map hX.measurable
    · change Measure.map (Y k) ν = _
      rw [hmap]
      exact hX.isUniform k
  exact ae_of_ae_map (μ := (ℙ : Measure Ω)) hp.aemeasurable (limit_of_tails h₁ h₂ hY)

end OMA.R_Erdos1166_erdos_1166_variants_dembo_peres_rosen_zeitouni_R1
