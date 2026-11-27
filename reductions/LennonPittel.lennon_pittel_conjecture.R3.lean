import FormalConjectures.Paper.LennonPittelStableMatchings

-- Port of Bo Cowgill's lower-tail criterion, used under Apache-2.0.
-- https://github.com/bocowgill/lennon-pittel/tree/cf950d059659
-- His proof gives both the upper bound on the mean and a lower scale for
-- the random count, with constants allowed to depend on the probability loss.

open Filter MeasureTheory StableMarriage
open scoped Topology ENNReal

namespace OMA.R_LennonPittel_lennon_pittel_conjecture_R3

def H1 : Prop := ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
  expectedNumStableMatchings n ≤ C * ((n : ℝ) * Real.log n)

def H2 : Prop := ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
  ENNReal.ofReal (1 - δ) ≤ (uniformProfile n).toMeasure
    {p | c * ((n : ℝ) * Real.log n) ≤ (numStableMatchings p : ℝ)}

theorem main : H1 → H2 → type_of% @LennonPittel.lennon_pittel_conjecture := by
  intro ⟨C, hmean⟩ hlower ε _ _ hε
  have hsmall : Tendsto (fun n ↦ |ε n| * C) atTop (𝓝 0) := by
    simpa using hε.abs.mul_const C
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    have hat : a ≠ ⊤ := ha.ne_top
    have haR : a.toReal < 1 := by
      simpa only [ENNReal.toReal_one] using ENNReal.toReal_strict_mono (by simp) ha
    let δ : ℝ := (1 - a.toReal) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    obtain ⟨c, hc, hlarge⟩ := hlower δ hδ
    have haδ : a < ENNReal.ofReal (1 - δ) := by
      rw [← ENNReal.ofReal_toReal hat]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg |>.2 (by
        dsimp [δ]
        linarith)
    filter_upwards [(tendsto_order.mp hsmall).2 c hc, hlarge,
      hmean, eventually_ge_atTop (1 : ℕ)]
      with n hs hl hm hn
    have hnorm : 0 ≤ (n : ℝ) * Real.log n :=
      mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hn))
    have hthreshold : ε n * expectedNumStableMatchings n ≤ c * ((n : ℝ) * Real.log n) :=
      calc
        _ ≤ |ε n| * expectedNumStableMatchings n :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (integral_nonneg fun _ ↦ Nat.cast_nonneg _)
        _ ≤ |ε n| * (C * ((n : ℝ) * Real.log n)) :=
          mul_le_mul_of_nonneg_left hm (abs_nonneg _)
        _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hs.le hnorm
    exact haδ.trans_le (hl.trans (measure_mono fun p hp => hthreshold.trans hp))
  · intro a ha
    exact Eventually.of_forall fun n ↦
      (prob_le_one (μ := (uniformProfile n).toMeasure)).trans_lt ha

end OMA.R_LennonPittel_lennon_pittel_conjecture_R3
