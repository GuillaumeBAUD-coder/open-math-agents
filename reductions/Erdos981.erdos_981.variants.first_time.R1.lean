import FormalConjectures.ErdosProblems.«981»

/-!
# Truncation reduction for the first-passage variant of Erdős Problem 981

Credit: @DarkWingMcQuack.
-/

namespace OMA.R_Erdos981_erdos_981_variants_first_time_R1

open Filter Real
open scoped Topology

/-- For each positive cutoff, the normalized sum of truncated first-passage times converges
to a positive limit. This is the finite-dimensional part of Tang and Zhang's argument. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ B : ℕ, 0 < B →
    ∃ c > (0 : ℝ), Tendsto (fun x : ℝ ↦
      (↑(∑ p : Nat.primesBelow ⌈x⌉₊, min B (Erdos981.f' ε p)) : ℝ) * log x / x)
      atTop (𝓝 c)

/-- As the cutoff grows, the discarded contribution is eventually arbitrarily small.
This is the uniform tail estimate in Tang and Zhang's argument. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∃ B : ℕ, 0 < B ∧ ∀ᶠ x : ℝ in atTop,
    dist
      ((↑(∑ p : Nat.primesBelow ⌈x⌉₊, Erdos981.f' ε p) : ℝ) * log x / x)
      ((↑(∑ p : Nat.primesBelow ⌈x⌉₊, min B (Erdos981.f' ε p)) : ℝ) * log x / x) < δ

theorem main : H1 → H2 → type_of% @Erdos981.erdos_981.variants.first_time := by
  intro hTruncated hTail ε hε
  let average (x : ℝ) : ℝ :=
    (↑(∑ p : Nat.primesBelow ⌈x⌉₊, Erdos981.f' ε p) : ℝ) * log x / x
  let truncated (B : ℕ) (x : ℝ) : ℝ :=
    (↑(∑ p : Nat.primesBelow ⌈x⌉₊, min B (Erdos981.f' ε p)) : ℝ) * log x / x
  have hCauchy : CauchySeq average := by
    refine Metric.cauchySeq_iff.mpr ?_
    intro δ hδ
    have hThird : 0 < δ / 3 := by positivity
    obtain ⟨B, hB, hError⟩ := hTail ε hε (δ / 3) hThird
    obtain ⟨cutoff, hError⟩ := eventually_atTop.mp hError
    obtain ⟨c, _, hc⟩ := hTruncated ε hε B hB
    have hTruncatedCauchy : CauchySeq (truncated B) := hc.cauchySeq
    obtain ⟨start, hDistance⟩ := Metric.cauchySeq_iff.mp hTruncatedCauchy (δ / 3) hThird
    refine ⟨max cutoff start, fun x hx y hy ↦ ?_⟩
    have hxError : dist (average x) (truncated B x) < δ / 3 :=
      hError x ((le_max_left _ _).trans hx)
    have hyError : dist (truncated B y) (average y) < δ / 3 := by
      rw [dist_comm]
      exact hError y ((le_max_left _ _).trans hy)
    have hxy := hDistance x ((le_max_right _ _).trans hx) y ((le_max_right _ _).trans hy)
    calc
      dist (average x) (average y) ≤
          dist (average x) (truncated B x) + dist (truncated B x) (average y) :=
        dist_triangle _ _ _
      _ ≤ dist (average x) (truncated B x) + (dist (truncated B x) (truncated B y) +
          dist (truncated B y) (average y)) := add_le_add le_rfl (dist_triangle _ _ _)
      _ < δ := by linarith
  obtain ⟨limit, hLimit⟩ := cauchySeq_tendsto_of_complete hCauchy
  obtain ⟨lower, hLowerPos, hLower⟩ := hTruncated ε hε 1 Nat.zero_lt_one
  have hBelow : ∀ᶠ x in atTop, truncated 1 x ≤ average x := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hSum :
        (↑(∑ p : Nat.primesBelow ⌈x⌉₊, min 1 (Erdos981.f' ε p)) : ℝ) ≤
          (↑(∑ p : Nat.primesBelow ⌈x⌉₊, Erdos981.f' ε p) : ℝ) :=
      Nat.cast_le.mpr (Finset.sum_le_sum fun _ _ ↦ min_le_right _ _)
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hSum (log_nonneg hx)) (zero_le_one.trans hx)
  exact ⟨limit, hLowerPos.trans_le (le_of_tendsto_of_tendsto hLower hLimit hBelow), hLimit⟩

end OMA.R_Erdos981_erdos_981_variants_first_time_R1
