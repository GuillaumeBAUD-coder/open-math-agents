import OMAReductions.R_Erdos1180_erdos_1180_variants_optimal_R1

-- Every denominator in the whole interval works once twice its endpoint is below p.
-- Compared with Linmiao Xu's fraction-stage argument in linrock/math-proofs
-- at ba96303b34a95ac458958c1eb0bbdee54733484a (Apache-2.0), here the
-- numerators are all one and no prime selection is needed.
-- Credit: @marcusbuffett

open Filter Finset Real

theorem OMA.solution : OMA.R_Erdos1180_erdos_1180_variants_optimal_R1.H1 := by
  intro ε he he1
  have hg := ((tendsto_rpow_atTop (show 0 < ε / 4 by linarith)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 2
  obtain ⟨N, hN⟩ := eventually_atTop.1 hg
  refine ⟨max 5 N, ?_⟩
  intro p hpN hp
  letI : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by omega
  have hp5R : (5 : ℝ) ≤ p := by exact_mod_cast hp5
  have hp0 : (0 : ℝ) < p := by linarith
  have ht : 2 ≤ (p : ℝ) ^ (ε / 4) := hN p (by omega)
  let T := ⌊(p : ℝ) ^ (ε / 2)⌋₊
  have hsq : (p : ℝ) ^ (ε / 4) * (p : ℝ) ^ (ε / 4) = (p : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hp0]; congr 1; ring
  have hT : (p : ℝ) ^ (ε / 4) < T := by
    have hf : (p : ℝ) ^ (ε / 2) < (T : ℝ) + 1 := Nat.lt_floor_add_one _
    nlinarith [sq_nonneg ((p : ℝ) ^ (ε / 4) - 2)]
  have hs : (p : ℝ) ^ (ε / 2) ≤ Real.sqrt p := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hs2 : Real.sqrt p * Real.sqrt p = (p : ℝ) := Real.mul_self_sqrt hp0.le
  have hspos : 2 < Real.sqrt p := Real.lt_sqrt_of_sq_lt (by linarith)
  have hbound : 2 * T < p := by
    have hfloor : (T : ℝ) ≤ (p : ℝ) ^ (ε / 2) := Nat.floor_le (by positivity)
    have hR : 2 * (T : ℝ) < p := by nlinarith [mul_pos (sub_pos.mpr hspos) (Real.sqrt_pos.2 hp0)]
    exact_mod_cast hR
  let D := Icc 1 T
  let V := D.image (fun n : ℕ ↦ (n : ZMod p)⁻¹)
  refine ⟨V, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hx
    obtain ⟨hn1, hnT⟩ := mem_Icc.mp hn
    have hc := hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega : 0 < n) (by omega : n < p))
    exact mem_image.mpr ⟨n, mem_filter.mpr ⟨hn, hc.symm⟩, rfl⟩
  · have hi : Set.InjOn (fun n : ℕ ↦ (n : ZMod p)⁻¹) D := by
      intro m hm n hn h
      have hmT := (mem_Icc.mp hm).2
      have hnT := (mem_Icc.mp hn).2
      have hc : (m : ZMod p) = n := inv_injective h
      have hv := congrArg ZMod.val hc
      rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
    simpa [V, card_image_of_injOn hi, D, Nat.card_Icc] using hT
  · intro x hx y hy hs
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hx
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hy
    obtain ⟨hm1, hmT⟩ := mem_Icc.mp hm
    obtain ⟨hn1, hnT⟩ := mem_Icc.mp hn
    have hi := congrArg (fun z : ZMod p ↦ z⁻¹) (eq_neg_of_add_eq_zero_left hs)
    have hc : (m : ZMod p) = - (n : ZMod p) := by simpa using hi
    have hz : ((m + n : ℕ) : ZMod p) = 0 := by push_cast; rw [hc]; simp
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv
    omega

