import OMAReductions.R_PartitionParity_bellaiche_green_soundararajan_odd_R1

/-! Once log log X ≥ 1, dividing the nonnegative number sqrt X by it does not increase it. -/

theorem OMA.solution : OMA.R_PartitionParity_bellaiche_green_soundararajan_odd_R1.H2 := by
  have t2 : Filter.Tendsto (fun X : ℝ => Real.log (Real.log X)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [t2.eventually_ge_atTop 1] with X h2
  have hs : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  rw [one_mul, Real.norm_of_nonneg (div_nonneg hs (by linarith)), Real.norm_of_nonneg hs]
  exact div_le_self hs h2
