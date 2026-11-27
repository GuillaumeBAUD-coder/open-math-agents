import OMAReductions.R_Erdos3_erdos_3_variants_green_tao_R1

-- Step Erdos3.erdos_3.variants.green_tao.R1.H2: hypothesis H2 of reduction Erdos3.erdos_3.variants.green_tao.R1
-- Credit: @loremcdmx
-- H2 := ∀ C B : ℝ, 0 < C → 0 < B → ∃ c K : ℝ, 0 < c ∧ 0 < K ∧     ∀ᶠ p : ℕ in atTop, ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 10 ∧       C * ε + C * Real.exp (ε ^ (-B)) / p ≤ (K * Real.log p ^ (-c)) ^ 4

open Filter Topology

namespace OMA.Aux

lemma eps_facts (B L : ℝ) (hB : 0 < B) (hL1 : 1 ≤ L / 2) (hL2 : 10 ^ B ≤ L / 2) :
    0 < (L / 2) ^ (-(1 / B)) ∧ (L / 2) ^ (-(1 / B)) ≤ 1 / 10 ∧
    ((L / 2) ^ (-(1 / B))) ^ (-B) = L / 2 ∧
    (L / 2) ^ (-(1 / B)) ≤ 2 ^ (1 / B) * L ^ (-(1 / B)) := by
  have hLpos : 0 < L / 2 := by linarith
  have hLp : 0 < L := by linarith
  refine ⟨Real.rpow_pos_of_pos hLpos _, ?_, ?_, ?_⟩
  · have h10 : (0:ℝ) < 10 ^ B := Real.rpow_pos_of_pos (by norm_num) _
    calc (L / 2) ^ (-(1 / B)) ≤ (10 ^ B) ^ (-(1 / B)) :=
          Real.rpow_le_rpow_of_nonpos h10 hL2 (by
            have : 0 < 1 / B := by positivity
            linarith)
      _ = 1 / 10 := by
          rw [← Real.rpow_mul (by norm_num)]
          have : B * (-(1 / B)) = -1 := by field_simp
          rw [this, Real.rpow_neg_one]
          try norm_num
  · rw [← Real.rpow_mul hLpos.le]
    have : -(1 / B) * -B = 1 := by field_simp
    rw [this, Real.rpow_one]
  · rw [Real.div_rpow hLp.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    rw [div_inv_eq_mul, mul_comm]

end OMA.Aux

open OMA.Aux in
theorem OMA.solution : OMA.R_Erdos3_erdos_3_variants_green_tao_R1.H2 := by
  intro C B hC hB
  have hK0 : 0 < C * 2 ^ (1 / B) + C := by
    have : (0:ℝ) < 2 ^ (1 / B) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  refine ⟨1 / (4 * B), (C * 2 ^ (1 / B) + C) ^ ((1 : ℝ) / 4), by positivity,
    Real.rpow_pos_of_pos hK0 _, ?_⟩
  have hlog : Tendsto (fun p : ℕ => Real.log p) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hexp := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / B) (1 / 2)
    (by norm_num)).comp hlog
  have h1 := hlog.eventually_ge_atTop (2 * max 1 (10 ^ B))
  have h2 := hexp.eventually (ge_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [h1, h2, eventually_gt_atTop 0] with p hp1 hp2 hp0
  set L := Real.log p with hLdef
  have hm1 : 1 ≤ max 1 (10 ^ B : ℝ) := le_max_left _ _
  have hm2 : (10 ^ B : ℝ) ≤ max 1 (10 ^ B) := le_max_right _ _
  obtain ⟨hε0, hε1, hεB, hεL⟩ := eps_facts B L hB (by linarith) (by linarith)
  have hLp : 0 < L := by linarith
  refine ⟨(L / 2) ^ (-(1 / B)), hε0, hε1, ?_⟩
  have hpR : (0:ℝ) < p := by exact_mod_cast hp0
  have hpexp : (p : ℝ) = Real.exp L := (Real.exp_log hpR).symm
  have hexpdiv : Real.exp (L / 2) / p = Real.exp (-(L / 2)) := by
    rw [hpexp, ← Real.exp_sub]; congr 1; ring
  have hLB : 0 < L ^ (-(1 / B)) := Real.rpow_pos_of_pos hLp _
  have hexpb : Real.exp (-(L / 2)) ≤ L ^ (-(1 / B)) := by
    simp only [Function.comp] at hp2
    have e1 : L ^ (-(1 / B)) = (L ^ (1 / B))⁻¹ := Real.rpow_neg hLp.le _
    have hp3 : 0 < L ^ (1 / B) := Real.rpow_pos_of_pos hLp _
    rw [e1, le_inv_comm₀ (Real.exp_pos _) hp3, ← Real.exp_neg, neg_neg]
    have : L ^ (1 / B) * Real.exp (-(1 / 2) * L) ≤ 1 := hp2
    have e2 : Real.exp (-(1 / 2) * L) = Real.exp (-(L / 2)) := by congr 1; ring
    rw [e2] at this
    have h5 := mul_le_mul_of_nonneg_right this (Real.exp_pos (L / 2)).le
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, one_mul] at h5
    exact h5
  have hK4 : ((C * 2 ^ (1 / B) + C) ^ ((1 : ℝ) / 4) * L ^ (-(1 / (4 * B)))) ^ 4
      = (C * 2 ^ (1 / B) + C) * L ^ (-(1 / B)) := by
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hK0.le,
      ← Real.rpow_mul hLp.le]
    have a : ((1:ℝ) / 4) * ((4:ℕ):ℝ) = 1 := by norm_num
    have b : -(1 / (4 * B)) * ((4:ℕ):ℝ) = -(1 / B) := by push_cast; field_simp
    rw [a, b, Real.rpow_one]
  rw [hK4, hεB, mul_div_assoc, hexpdiv]
  have := mul_le_mul_of_nonneg_left hεL hC.le
  have h3 := mul_le_mul_of_nonneg_left hexpb hC.le
  nlinarith
