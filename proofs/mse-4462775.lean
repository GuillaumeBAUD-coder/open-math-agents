import OMAStatements.S_mse_4462775
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OMA.P_mse_4462775

private theorem prove_main :
    ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (T : X →ₗ[𝕜] Y) (hT : Function.Surjective T)
    (hcompact : ∃ D : Set Y, IsCompact D ∧ T '' Metric.ball (0 : X) 1 ⊆ D),
    FiniteDimensional 𝕜 Y := by
  intro 𝕜 X Y _ _ _ _ _ _ _ T hT ⟨D, hD_compact, hD_sub⟩
  obtain ⟨C, hC⟩ := hD_compact.isBounded.subset_closedBall (0 : Y)
  set M : ℝ := max C 0
  have hM_nonneg : 0 ≤ M := le_max_right C 0
  have hD_norm : ∀ y ∈ D, ‖y‖ ≤ M := by
    intro y hy
    have hmem : y ∈ Metric.closedBall (0 : Y) C := hC hy
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact le_trans hmem (le_max_left C 0)
  have hT_bound : ∀ x : X, ‖T x‖ ≤ (2 * M) * ‖x‖ := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    · have hnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      set r : ℝ := 2 * ‖x‖
      have hr_pos : 0 < r := by positivity
      set c : 𝕜 := (RCLike.ofReal r⁻¹ : 𝕜)
      have hc_norm : ‖c‖ = r⁻¹ := by
        dsimp only [c]
        rw [RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hr_pos)]
      have hcx_ball : c • x ∈ Metric.ball (0 : X) 1 := by
        rw [Metric.mem_ball, dist_zero_right, norm_smul, hc_norm]
        have hhalf : r⁻¹ * ‖x‖ = 1 / 2 := by
          dsimp only [r]
          field_simp
        linarith
      have hTcx_mem : T (c • x) ∈ D := hD_sub ⟨c • x, hcx_ball, rfl⟩
      have hTcx_le : ‖T (c • x)‖ ≤ M := hD_norm _ hTcx_mem
      rw [map_smul, norm_smul, hc_norm] at hTcx_le
      have hmul : r * (r⁻¹ * ‖T x‖) ≤ r * M := mul_le_mul_of_nonneg_left hTcx_le hr_pos.le
      have hcancel : r * (r⁻¹ * ‖T x‖) = ‖T x‖ := by field_simp
      rw [hcancel] at hmul
      dsimp only [r] at hmul
      linarith
  let T' : X →L[𝕜] Y := T.mkContinuous (2 * M) hT_bound
  have hT'_surj : Function.Surjective T' := hT
  have hopen : IsOpenMap T' := T'.isOpenMap hT'_surj
  have hU_open : IsOpen (T' '' Metric.ball (0 : X) 1) := hopen _ Metric.isOpen_ball
  have h0_mem : (0 : Y) ∈ T' '' Metric.ball (0 : X) 1 :=
    ⟨0, Metric.mem_ball_self zero_lt_one, map_zero T'⟩
  have hU_nhds : T' '' Metric.ball (0 : X) 1 ∈ nhds (0 : Y) := hU_open.mem_nhds h0_mem
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hU_nhds
  have hball_sub_D : Metric.closedBall (0 : Y) r ⊆ D := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hr_sub hy
    exact hD_sub ⟨x, hx, rfl⟩
  have hball_compact : IsCompact (Metric.closedBall (0 : Y) r) :=
    hD_compact.of_isClosed_subset Metric.isClosed_closedBall hball_sub_D
  exact FiniteDimensional.of_isCompact_closedBall₀ 𝕜 hr_pos hball_compact

end OMA.P_mse_4462775

theorem OMA.solution : type_of% @OMA.S_mse_4462775.main :=
  OMA.P_mse_4462775.prove_main
