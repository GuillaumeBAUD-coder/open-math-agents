import OMAReductions.R_Erdos413_erdos_413_parts_ii_R1

/-!
Proof of `OMA.R_Erdos413_erdos_413_parts_ii_R1.H2`.

Take `ε = 1 / C`. Then `ε * C * log k = log k ≤ k - 1` for every `k ≥ 2`, by `log x ≤ x - 1`.
-/

theorem OMA.solution : OMA.R_Erdos413_erdos_413_parts_ii_R1.H2 := by
  intro C hC
  refine ⟨1 / C, one_div_pos.mpr hC, fun k hk => ?_⟩
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlog := Real.log_le_sub_one_of_pos hkpos
  have hεC : 1 / C * C = 1 := one_div_mul_cancel hC.ne'
  rw [hεC, one_mul]
  exact hlog
