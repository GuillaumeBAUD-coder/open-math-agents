import OMAReductions.R_Green91_green_91_R1

/-! Diagonal selection of a single deficit from fixed tolerances on the
even and odd graph sizes. No rate of convergence in either input is needed. -/

namespace OMA.R_Green91_green_91_R1_H1_R1

open Filter Asymptotics
open scoped Topology

/-- The fixed-tolerance probability estimate on even graph sizes. -/
def H1 : Prop :=
  ∀ j : ℕ, ∀ᶠ m : ℕ in atTop,
    let n := 2 * m
    ENNReal.ofReal (1 - ((j : ℝ) + 1)⁻¹) ≤ Green91.prob n fun G ↦
      ∃ s : Finset (Fin n), s.card = n / 2 ∧
        (n : ℝ) - (n : ℝ) * ((j : ℝ) + 1)⁻¹ ≤ Green91.numFriendly G s

/-- The fixed-tolerance probability estimate on odd graph sizes. -/
def H2 : Prop :=
  ∀ j : ℕ, ∀ᶠ m : ℕ in atTop,
    let n := 2 * m + 1
    ENNReal.ofReal (1 - ((j : ℝ) + 1)⁻¹) ≤ Green91.prob n fun G ↦
      ∃ s : Finset (Fin n), s.card = n / 2 ∧
        (n : ℝ) - (n : ℝ) * ((j : ℝ) + 1)⁻¹ ≤ Green91.numFriendly G s

theorem main : H1 → H2 → OMA.R_Green91_green_91_R1.H1 := by
  classical
  intro heven hodd
  let tolerance (j : ℕ) : ℝ := ((j : ℝ) + 1)⁻¹
  let good (n j : ℕ) : Prop :=
    ENNReal.ofReal (1 - tolerance j) ≤ Green91.prob n fun G ↦
      ∃ s : Finset (Fin n), s.card = n / 2 ∧
        (n : ℝ) - (n : ℝ) * tolerance j ≤ Green91.numFriendly G s
  have hgood (j : ℕ) : ∀ᶠ n in atTop, good n j := by
    obtain ⟨E, hE⟩ := eventually_atTop.mp (heven j)
    obtain ⟨O, hO⟩ := eventually_atTop.mp (hodd j)
    apply eventually_atTop.mpr
    refine ⟨2 * max E O, ?_⟩
    intro n hn
    have hmax : max E O ≤ n / 2 := by omega
    have he := (le_max_left E O).trans hmax
    have ho := (le_max_right E O).trans hmax
    by_cases hz : n % 2 = 0
    · have hn' : n = 2 * (n / 2) := by omega
      exact Eq.mpr (congrArg (fun k ↦ good k j) hn') (hE (n / 2) he)
    · have hn' : n = 2 * (n / 2) + 1 := by omega
      exact Eq.mpr (congrArg (fun k ↦ good k j) hn') (hO (n / 2) ho)
  let candidates (n : ℕ) := (Finset.range (n + 1)).filter (good n)
  have hnonempty (n : ℕ) : (candidates n).Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos _), ?_⟩⟩
    simp [good, tolerance]
  let index (n : ℕ) := (candidates n).max' (hnonempty n)
  have hvalid (n : ℕ) : good n (index n) :=
    (Finset.mem_filter.mp (Finset.max'_mem (candidates n) (hnonempty n))).2
  have hindex (j : ℕ) : ∀ᶠ n in atTop, j ≤ index n := by
    filter_upwards [hgood j, eventually_ge_atTop j] with n hnj hle
    exact Finset.le_max' (candidates n) j
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hle), hnj⟩)
  have htop : Tendsto (fun n ↦ (index n : ℝ) + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro a
    obtain ⟨j, hj⟩ := exists_nat_ge a
    filter_upwards [hindex j] with n hn
    exact hj.trans (by exact_mod_cast (hn.trans (Nat.le_succ (index n))))
  have hzero : Tendsto (fun n ↦ tolerance (index n)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp htop
  refine ⟨fun n ↦ (n : ℝ) * tolerance (index n), ?_, ?_⟩
  · apply isLittleO_iff.mpr
    intro c hc
    filter_upwards [(tendsto_order.mp hzero).2 c hc] with n hcn
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have ht : 0 ≤ tolerance (index n) := by dsimp [tolerance]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hn ht),
      Real.norm_eq_abs, abs_of_nonneg hn, mul_comm c]
    exact mul_le_mul_of_nonneg_left hcn.le hn
  · have hreal : Tendsto (fun n ↦ (1 : ℝ) - tolerance (index n)) atTop (𝓝 1) := by
      have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      simpa using hone.sub hzero
    have hlow : Tendsto (fun n ↦ ENNReal.ofReal (1 - tolerance (index n))) atTop (𝓝 1) := by
      simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · exact Eventually.of_forall hvalid
    · exact Eventually.of_forall fun _ ↦ MeasureTheory.prob_le_one

end OMA.R_Green91_green_91_R1_H1_R1
