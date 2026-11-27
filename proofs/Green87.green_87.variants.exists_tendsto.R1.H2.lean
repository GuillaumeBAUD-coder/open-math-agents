import OMAReductions.R_Green87_green_87_variants_exists_tendsto_R1

/-! The terms are trapped between two corrected running means. The upper
mean decreases, the lower mean increases, and their difference tends to zero. -/

open Finset Filter Topology

theorem OMA.solution : OMA.R_Green87_green_87_variants_exists_tendsto_R1.H2 := by
  intro a C hC herr
  let S (n : ℕ) := ∑ j ∈ range (n+1), a j
  let upper (n : ℕ) := (S n + C) / (n+1 : ℝ)
  let lower (n : ℕ) := (S n - C) / (n+1 : ℝ)
  have step (n : ℕ) : S (n+1) = S n + a (n+1) := sum_range_succ _ _
  have bounds (n : ℕ) : S n - C ≤ (n+1 : ℝ) * a (n+1) ∧
      (n+1 : ℝ) * a (n+1) ≤ S n + C := by
    have h := abs_le.mp (herr (n+1))
    change -C ≤ ((n+1 : ℕ) : ℝ) * a (n+1) - S n ∧ _ at h
    push_cast at h
    constructor <;> linarith
  have decreasing : Antitone upper := by
    apply antitone_nat_of_succ_le
    intro n
    dsimp only [upper]
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity), step]
    nlinarith [(bounds n).2]
  have increasing : Monotone lower := by
    apply monotone_nat_of_le_succ
    intro n
    dsimp only [lower]
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity), step]
    nlinarith [(bounds n).1]
  have below (n : ℕ) : lower n ≤ upper n :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hb : BddBelow (Set.range upper) :=
    ⟨lower 0, fun _ ⟨n, hn⟩ => hn ▸ (increasing (Nat.zero_le n)).trans (below n)⟩
  have hu := tendsto_atTop_ciInf decreasing hb
  have hgap : Tendsto (fun n : ℕ => (2*C) * (1 / (n+1 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2*C)
  have hl : Tendsto lower atTop (𝓝 (⨅ i, upper i)) := by
    convert! hu.sub hgap using 1
    · funext n
      dsimp [lower, upper]
      ring
    · simp
  refine ⟨_, (tendsto_add_atTop_iff_nat 1).mp (hl.squeeze hu ?_ ?_)⟩
  · intro n
    exact (div_le_iff₀ (by positivity)).mpr (by linarith [(bounds n).1])
  · intro n
    exact (le_div_iff₀ (by positivity)).mpr (by linarith [(bounds n).2])
