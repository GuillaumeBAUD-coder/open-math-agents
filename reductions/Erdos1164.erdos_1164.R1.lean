import FormalConjectures.ErdosProblems.«1164»

-- Reduction Erdos1164.erdos_1164.R1 of Erdős Problem 1164
-- Credit: @koolkao
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The two halves of log R_n ≍ √(log n), each in probability. main combines them at ε/2 by a union
-- bound, after moving the walk to the canonical path space ℕ → ℤ × ℤ (the hypotheses are stated
-- for Ω : Type). The probabilities agree because the covering radius at time n depends only on the
-- first n steps, whose joint law is the same on both spaces.

open MeasureTheory Filter
open scoped ProbabilityTheory Real ENNReal

namespace OMA.R_Erdos1164_erdos_1164_R1

open Erdos1165 Erdos1164

-- H1 (lower half: the disc of radius e^{c √(log n)} is covered). Révész (1990) and Kesten; see
-- Dembo, Peres, Rosen and Zeitouni, Ann. of Math. 160 (2004), Section 1.3: the probability that the
-- disc of radius r is covered by time e^{t (log r)^2} has liminf at least e^{-b/t}, so it tends to 1
-- as t → ∞. Elementary proof: the walk makes at least δ log n returns to the origin with probability
-- at least 1 - ε/2, and each excursion from the origin hits a given x with |x| ≤ r before returning
-- with probability at least c₀ / log r. A union bound over the (2r + 1)^2 sites finishes the proof.
def H1 : Prop :=
  ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ},
    IsSimpleRandomWalkSteps X → ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      1 - ε ≤ (ℙ {ω | c * Real.sqrt (Real.log n) ≤ Real.log (coveringRadius X n ω)}).toReal

-- H2 (upper half: some site within radius e^{C √(log n)} is missed). Révész (1990) and Kesten; DPRZ04,
-- Section 1.3: the probability that the disc of radius r is covered by time e^{t (log r)^2} has limsup
-- at most e^{-a/t}, which tends to 0 as t → 0. DPRZ04, Theorem 1.4, gives the exact limit e^{-4/t}.
def H2 : Prop :=
  ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ},
    IsSimpleRandomWalkSteps X → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      1 - ε ≤ (ℙ {ω | Real.log (coveringRadius X n ω) ≤ C * Real.sqrt (Real.log n)}).toReal

lemma coveringRadius_congr {Ω Ω' : Type*} {X : ℕ → Ω → ℤ × ℤ} {Y : ℕ → Ω' → ℤ × ℤ} {ω : Ω}
    {ω' : Ω'} {n : ℕ} (h : ∀ i < n, X i ω = Y i ω') :
    coveringRadius X n ω = coveringRadius Y n ω' := by
  have hp : ∀ k ≤ n, position X k ω = position Y k ω' := fun k hk ↦
    Finset.sum_congr rfl fun i hi ↦ h i (by rw [Finset.mem_range] at hi; omega)
  unfold coveringRadius Covers
  congr 1
  ext r
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hc x hx
    obtain ⟨k, hk, hpos⟩ := hc x hx
    exact ⟨k, hk, (hp k hk).symm.trans hpos⟩
  · intro hc x hx
    obtain ⟨k, hk, hpos⟩ := hc x hx
    exact ⟨k, hk, (hp k hk).trans hpos⟩

lemma measurable_coveringRadius {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : ∀ k, Measurable (X k)) (n : ℕ) : Measurable fun ω ↦ coveringRadius X n ω := by
  let g : (Fin n → ℤ × ℤ) → ℕ := fun z ↦
    coveringRadius (fun i (z : Fin n → ℤ × ℤ) ↦ if h : i < n then z ⟨i, h⟩ else 0) n z
  have hg : Measurable g := measurable_of_countable g
  have hF : Measurable fun ω (i : Fin n) ↦ X i ω := measurable_pi_iff.mpr fun i ↦ hX i
  have e : (fun ω ↦ coveringRadius X n ω) = g ∘ fun ω (i : Fin n) ↦ X i ω := by
    funext ω
    exact coveringRadius_congr fun i hi ↦ by simp [hi]
  rw [e]
  exact hg.comp hF

lemma meas_event {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : ∀ k, Measurable (X k)) (n : ℕ) (P : ℕ → Prop) :
    MeasurableSet {ω | P (coveringRadius X n ω)} :=
  measurable_coveringRadius hX n (Set.to_countable {k : ℕ | P k}).measurableSet

theorem main : H1 → H2 → type_of% @Erdos1164.erdos_1164 := by
  intro h1 h2 Ω _ _ X hX ε hε
  have hF : Measurable (fun ω i ↦ X i ω) := measurable_pi_iff.mpr hX.measurable
  letI : MeasureSpace (ℕ → ℤ × ℤ) := ⟨Measure.map (fun ω i ↦ X i ω) ℙ⟩
  haveI : IsProbabilityMeasure (ℙ : Measure (ℕ → ℤ × ℤ)) := by
    constructor
    change Measure.map (fun ω i ↦ X i ω) ℙ Set.univ = 1
    rw [Measure.map_apply hF MeasurableSet.univ]
    simp
  have hX' : IsSimpleRandomWalkSteps (fun i (ω' : ℕ → ℤ × ℤ) ↦ ω' i) := by
    refine ⟨fun k ↦ measurable_pi_apply k, ?_, ?_⟩
    · rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
      intro S sets hs
      have key := hX.indep.measure_inter_preimage_eq_mul S hs
      have hm : ∀ T : Set (ℕ → ℤ × ℤ), MeasurableSet T →
          (ℙ : Measure (ℕ → ℤ × ℤ)) T = ℙ ((fun ω i ↦ X i ω) ⁻¹' T) := fun T hT ↦
        Measure.map_apply hF hT
      rw [hm _ (Finset.measurableSet_biInter S fun i hi ↦ measurable_pi_apply i (hs i hi))]
      rw [Finset.prod_congr rfl fun i hi ↦ hm _ (measurable_pi_apply i (hs i hi))]
      simp only [Set.preimage_iInter₂]
      exact key
    · intro k
      exact (Measure.map_map (measurable_pi_apply k) hF).trans (hX.isUniform k)
  have hmc : ∀ k, Measurable (fun (ω' : ℕ → ℤ × ℤ) ↦ ω' k) := fun k ↦ measurable_pi_apply k
  -- probabilities of covering-radius events agree on the two spaces
  have htr : ∀ (n : ℕ) (P : ℕ → Prop), ℙ {ω | P (coveringRadius X n ω)} =
      (ℙ : Measure (ℕ → ℤ × ℤ)) {ω' | P (coveringRadius (fun i (ω' : ℕ → ℤ × ℤ) ↦ ω' i) n ω')} := by
    intro n P
    change _ = Measure.map (fun ω i ↦ X i ω) ℙ _
    rw [Measure.map_apply hF (meas_event hmc n P)]
    rfl
  obtain ⟨c, hc, hlow⟩ := h1 hX' (ε / 2) (by positivity)
  obtain ⟨C, hup⟩ := h2 hX' (ε / 2) (by positivity)
  refine ⟨c, C, hc, ?_⟩
  filter_upwards [hlow, hup] with n hl hu
  set Y := fun i (ω' : ℕ → ℤ × ℤ) ↦ ω' i
  set A := {ω' : ℕ → ℤ × ℤ | c * Real.sqrt (Real.log n) ≤ Real.log (coveringRadius Y n ω')}
  set B := {ω' : ℕ → ℤ × ℤ | Real.log (coveringRadius Y n ω') ≤ C * Real.sqrt (Real.log n)}
  have hA : MeasurableSet A :=
    meas_event hmc n (fun k ↦ c * Real.sqrt (Real.log n) ≤ Real.log (k : ℝ))
  have hB : MeasurableSet B :=
    meas_event hmc n (fun k ↦ Real.log (k : ℝ) ≤ C * Real.sqrt (Real.log n))
  have e : ℙ {ω | c * Real.sqrt (Real.log n) ≤ Real.log (coveringRadius X n ω) ∧
      Real.log (coveringRadius X n ω) ≤ C * Real.sqrt (Real.log n)} =
      (ℙ : Measure (ℕ → ℤ × ℤ)) (A ∩ B) :=
    htr n (fun k ↦ c * Real.sqrt (Real.log n) ≤ Real.log (k : ℝ) ∧
      Real.log (k : ℝ) ≤ C * Real.sqrt (Real.log n))
  rw [e]
  have hAc : ((ℙ : Measure (ℕ → ℤ × ℤ)) Aᶜ).toReal ≤ ε / 2 := by
    rw [prob_compl_eq_one_sub hA, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
    linarith
  have hBc : ((ℙ : Measure (ℕ → ℤ × ℤ)) Bᶜ).toReal ≤ ε / 2 := by
    rw [prob_compl_eq_one_sub hB, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
    linarith
  have hu' : (ℙ : Measure (ℕ → ℤ × ℤ)) (A ∩ B)ᶜ ≤ ℙ Aᶜ + ℙ Bᶜ := by
    rw [Set.compl_inter]; exact measure_union_le _ _
  have hu'' : ((ℙ : Measure (ℕ → ℤ × ℤ)) (A ∩ B)ᶜ).toReal ≤
      ((ℙ : Measure (ℕ → ℤ × ℤ)) Aᶜ).toReal + ((ℙ : Measure (ℕ → ℤ × ℤ)) Bᶜ).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hu'
  rw [prob_compl_eq_one_sub (hA.inter hB), ENNReal.toReal_sub_of_le prob_le_one
    ENNReal.one_ne_top, ENNReal.toReal_one] at hu''
  linarith

end OMA.R_Erdos1164_erdos_1164_R1
