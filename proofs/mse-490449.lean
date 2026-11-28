import OMAStatements.S_mse_490449

/-!
# Characterization of strong convergence of finite measures

Proves `OMA.S_mse_490449.main` by indicator testing and uniform step-function approximation.
-/

open MeasureTheory Filter

theorem OMA.solution : type_of% @OMA.S_mse_490449.main := by
  intro Ω _ μ μ₀ hμ hμ₀
  refine ⟨fun hA f hf ⟨C, hC⟩ => Metric.tendsto_atTop.mpr fun ε hε => ?_, fun hI A hA => ?_⟩
  · set M := (μ₀ Set.univ).toReal + 1
    have hM : 0 < M := by positivity
    set δ := ε / (3 * M)
    have hδ : 0 < δ := by positivity
    set B := max C 1
    obtain ⟨K, hK⟩ := exists_nat_gt (2 * B / δ)
    let a : ℕ → ℝ := fun k => -B + k * δ
    let S : ℕ → Set Ω := fun k => f ⁻¹' Set.Ico (a k) (a (k + 1))
    have hSm : ∀ k, MeasurableSet (S k) := fun k => measurableSet_Ico.preimage hf
    let g : Ω → ℝ := fun x => ∑ k ∈ Finset.range K, (S k).indicator (fun _ => a k) x
    have hfg : ∀ x, |f x - g x| ≤ δ := by
      intro x
      have hx : |f x| ≤ B := (hC x).trans (le_max_left _ _)
      have hq : 0 ≤ (f x + B) / δ := div_nonneg (by linarith [(abs_le.mp hx).1]) hδ.le
      set j := ⌊(f x + B) / δ⌋₊
      have hj1 : (j : ℝ) * δ ≤ f x + B := (le_div_iff₀ hδ).mp (Nat.floor_le hq)
      have hj2 : f x + B < ((j : ℝ) + 1) * δ := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one _)
      have hjK : j < K := by
        have h1 : (j : ℝ) < (K : ℝ) := (Nat.floor_le hq).trans_lt
          ((div_lt_iff₀ hδ).mpr (by linarith [(abs_le.mp hx).2, (div_lt_iff₀ hδ).mp hK]))
        exact_mod_cast h1
      have hxj : x ∈ S j := ⟨by dsimp [S, a]; linarith, by dsimp [S, a]; push_cast; linarith⟩
      have hgx : g x = a j := by
        dsimp only [g]
        rw [Finset.sum_eq_single j]
        · exact Set.indicator_of_mem hxj _
        · intro k _ hk
          apply Set.indicator_of_notMem
          intro hxk
          rcases lt_or_gt_of_ne hk with h | h
          · have : ((k + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast h
            nlinarith [hxk.2, hxj.1]
          · have : ((j + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast h
            nlinarith [hxj.2, hxk.1]
        · exact fun h => absurd (Finset.mem_range.mpr hjK) h
      rw [hgx, abs_le]; dsimp [a]; constructor <;> linarith
    have hint : ∀ (ν : Measure Ω) [IsFiniteMeasure ν],
        ∫ x, g x ∂ν = ∑ k ∈ Finset.range K, (ν (S k)).toReal * a k := fun ν _ => by
      rw [integral_finsetSum _ fun k _ => (integrable_const _).indicator (hSm k)]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [integral_indicator_const, hSm k, Measure.real]
    have herr : ∀ (ν : Measure Ω) [IsFiniteMeasure ν],
        |∫ x, f x ∂ν - ∫ x, g x ∂ν| ≤ δ * (ν Set.univ).toReal := fun ν _ => by
      rw [← integral_sub
        (Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs]; exact (hC x).trans (le_max_left _ _)))
        (integrable_finsetSum _ fun k _ => (integrable_const _).indicator (hSm k)),
        ← Real.norm_eq_abs]
      exact norm_integral_le_of_norm_le_const (ae_of_all _ fun x => by
        simpa [Real.norm_eq_abs] using hfg x)
    have hgt : Tendsto (fun n => ∫ x, g x ∂(μ n)) atTop (nhds (∫ x, g x ∂μ₀)) := by
      simp_rw [hint]
      exact tendsto_finsetSum _ fun k _ => (hA _ (hSm k)).mul_const _
    have hev := ((hA Set.univ MeasurableSet.univ).eventually
      (gt_mem_nhds (by linarith : (μ₀ Set.univ).toReal < M))).and
      (Metric.tendsto_atTop.mp hgt (ε / 3) (by positivity) |> fun ⟨N, hN⟩ =>
        eventually_atTop.mpr ⟨N, hN⟩)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨hMn, hgn⟩ := hN n hn
    have h1 := (herr (μ n)).trans (mul_le_mul_of_nonneg_left hMn.le hδ.le)
    have h2 := (herr μ₀).trans
      (mul_le_mul_of_nonneg_left (by linarith : (μ₀ Set.univ).toReal ≤ M) hδ.le)
    have h3 : δ * M = ε / 3 := by dsimp [δ]; field_simp
    rw [Real.dist_eq, abs_lt] at hgn ⊢
    rw [abs_le] at h1 h2
    constructor <;> linarith
  · simpa [integral_indicator_const, hA, Measure.real] using
      hI (A.indicator fun _ => (1 : ℝ)) (measurable_const.indicator hA)
        ⟨1, fun x => by by_cases hx : x ∈ A <;> simp [hx]⟩
