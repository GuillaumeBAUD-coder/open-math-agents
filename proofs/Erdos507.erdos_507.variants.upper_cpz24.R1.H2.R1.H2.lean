import OMAReductions.R_Erdos507_erdos_507_variants_upper_cpz24_R1_H2_R1

open Filter Topology

theorem OMA.solution : OMA.R_Erdos507_erdos_507_variants_upper_cpz24_R1_H2_R1.H2 := by
  intro W mono small
  have step : ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, W n ((n : ℝ) ^ (2 / ((k : ℝ) + 1))) := by
    intro k
    have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨C, hC⟩ := small _ hε
    have grow : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / ((k : ℝ) + 1))) atTop atTop :=
      (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
    have ev := hC.and ((grow.eventually_ge_atTop C).and (eventually_ge_atTop 1))
    obtain ⟨N, hN⟩ := eventually_atTop.mp ev
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨hW, hCle, hn1⟩ := hN n hn
    apply mono n _ hW
    have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnn : 0 ≤ (n : ℝ) ^ (1 / ((k : ℝ) + 1)) := Real.rpow_nonneg hpos.le _
    have split : (n : ℝ) ^ (2 / ((k : ℝ) + 1)) =
        (n : ℝ) ^ (1 / ((k : ℝ) + 1)) * (n : ℝ) ^ (1 / ((k : ℝ) + 1)) := by
      rw [← Real.rpow_add hpos]
      congr 1
      ring
    rw [split]
    exact mul_le_mul_of_nonneg_right hCle hnn
  choose N hN using step
  let P : ℕ → ℕ → Prop := fun n k => ∀ j ≤ k, N j ≤ n
  let κ : ℕ → ℕ := fun n => Nat.findGreatest (P n) n
  refine ⟨fun n => 2 / ((κ n : ℝ) + 1), ?_, ?_⟩
  · have hκ : Tendsto κ atTop atTop := by
      rw [tendsto_atTop]
      intro K
      rw [eventually_atTop]
      refine ⟨K + ∑ j ∈ Finset.range (K + 1), N j, fun n hn => ?_⟩
      apply Nat.le_findGreatest (by omega)
      intro j hj
      have := Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (show j < K + 1 by omega))
      omega
    have hreal : Tendsto (fun n => (κ n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hκ)
    have := hreal.inv_tendsto_atTop.const_mul 2
    simpa [div_eq_mul_inv] using this
  · rw [eventually_atTop]
    refine ⟨N 0, fun n hn => ?_⟩
    have spec : P n (κ n) := by
      apply Nat.findGreatest_spec (m := 0) (Nat.zero_le n)
      intro j hj
      have : j = 0 := by omega
      subst this
      exact hn
    exact hN (κ n) n (spec (κ n) le_rfl)
