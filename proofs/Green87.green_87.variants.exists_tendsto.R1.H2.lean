import OMAReductions.R_Green87_green_87_variants_exists_tendsto_R1

/-! # A running-mean convergence criterion -/
-- Credit: @steveDOTdigital
namespace OMA.RunningMeans
open Finset Filter
open scoped Topology

theorem converge (a : ℕ → ℝ) (C : ℝ) (hnon : 0 ≤ C)
    (h : ∀ n : ℕ, |(n : ℝ) * a n - ∑ j ∈ range n, a j| ≤ C) :
    ∃ L : ℝ, Tendsto a atTop (𝓝 L) := by
  let S (n : ℕ) := ∑ j ∈ range n, a j
  let low (n : ℕ) := (S (n+1)-C)/((n:ℝ)+1)
  let high (n : ℕ) := (S (n+1)+C)/((n:ℝ)+1)
  have rec' (n : ℕ) : S (n+1) = S n + a n := sum_range_succ _ _
  have err (n : ℕ) : -C ≤ ((n:ℝ)+1)*a (n+1)-S (n+1) ∧
      ((n:ℝ)+1)*a (n+1)-S (n+1) ≤ C := by
    simpa [S] using abs_le.mp (h (n+1))
  have between (n : ℕ) : low n ≤ a (n+1) ∧ a (n+1) ≤ high n := by
    obtain ⟨l,u⟩ := err n
    constructor
    · apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
      linarith
    · apply (le_div_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
      linarith
  have lower : Monotone low := by
    apply monotone_nat_of_le_succ
    intro n
    simp only [low,Nat.cast_add_one]
    rw [rec' (n+1), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [(err n).1]
  have upper : Antitone high := by
    apply antitone_nat_of_succ_le
    intro n
    simp only [high,Nat.cast_add_one]
    rw [rec' (n+1), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [(err n).2]
  have bounded : BddAbove (Set.range low) := by
    refine ⟨high 0,?_⟩
    rintro _ ⟨n,rfl⟩
    exact ((between n).1.trans (between n).2).trans (upper (Nat.zero_le _))
  have lim := tendsto_atTop_ciSup lower bounded
  have gap : Tendsto (fun n : ℕ => (2*C)*(1/((n:ℝ)+1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2*C))
  have hi : Tendsto high atTop (𝓝 (⨆ n, low n)) := by
    have h' := lim.add gap
    rw [add_zero] at h'
    apply h'.congr
    intro n
    change (S (n+1)-C)/((n:ℝ)+1)+(2*C)*(1/((n:ℝ)+1)) = (S (n+1)+C)/((n:ℝ)+1)
    ring
  refine ⟨⨆ n, low n,(tendsto_add_atTop_iff_nat 1).mp ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le lim hi (fun n => (between n).1) (fun n => (between n).2)
end OMA.RunningMeans

theorem OMA.solution : OMA.R_Green87_green_87_variants_exists_tendsto_R1.H2 := OMA.RunningMeans.converge
