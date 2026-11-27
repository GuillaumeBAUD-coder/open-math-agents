import FormalConjectures.ErdosProblems.«697»

-- Problem: Erdős Problem 697 — delta lt
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/697.lean:52 (declaration Erdos697.erdos_697.variants.delta_lt)
-- Credit: @cordellxyz (the owner of the agent is credited as the solver)
--
-- Every admissible divisor is d = k * m + 1 with 1 ≤ k ≤ ⌊exp (m ^ α)⌋. A union bound over the
-- multiples of these d gives δ ≤ ∑ 1 / (k * m + 1), which is strictly below
-- (1 / m) * harmonic ⌊exp (m ^ α)⌋ ≤ (1 + m ^ α) / m.

open Filter Set Real
open scoped Topology

namespace OMA.Erdos697DeltaLt

/-- There are at most `b / c + 1` multiples of `c` below `b`. -/
lemma card_multiples_le (b c : ℕ) (hc : 0 < c) :
    ((Finset.range b).filter (fun n => c ∣ n)).card ≤ b / c + 1 := by
  calc ((Finset.range b).filter (fun n => c ∣ n)).card
      ≤ ((Finset.range (b / c + 1)).image (fun j => c * j)).card := by
        apply Finset.card_le_card
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_range] at hn
        obtain ⟨hnb, j, rfl⟩ := hn
        simp only [Finset.mem_image, Finset.mem_range]
        refine ⟨j, ?_, rfl⟩
        have : j ≤ b / c := (Nat.le_div_iff_mul_le hc).mpr (by nlinarith)
        omega
    _ ≤ b / c + 1 := Finset.card_image_le.trans (by simp)

end OMA.Erdos697DeltaLt

open OMA.Erdos697DeltaLt in
theorem OMA.solution : type_of% @Erdos697.erdos_697.variants.delta_lt := by
  intro m α hm
  set B := Real.exp ((m : ℝ) ^ α) with hB
  set K := ⌊B⌋₊ with hK
  set D := (Finset.Icc 1 K).filter (fun k => ((k * m + 1 : ℕ) : ℝ) < B) with hD
  set S := {n : ℕ | ∃ d, d ≡ 1 [MOD m] ∧ (d : ℝ) ∈ Set.Ioo 1 (exp ((m : ℝ) ^ α)) ∧ d ∣ n}
    with hS
  have hδ : S.HasDensity (Erdos697.δ m α) := (Erdos697.density_exists m α).choose_spec
  set σ : ℝ := ∑ k ∈ D, 1 / ((k * m + 1 : ℕ) : ℝ) with hσ
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  -- Every element of `S` is a multiple of some `k * m + 1` with `k ∈ D`.
  have hcover : ∀ n ∈ S, ∃ k ∈ D, (k * m + 1) ∣ n := by
    rintro n ⟨d, hmod, ⟨h1, h2⟩, hdn⟩
    have hd1 : 1 < d := by exact_mod_cast h1
    obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hd1.le).mp hmod.symm
    have hdk : d = k * m + 1 := by rw [mul_comm, ← hk, Nat.sub_add_cancel hd1.le]
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; omega
      · exact h
    have hkd : k ≤ d := by rw [hdk]; nlinarith
    have hdB : ((k * m + 1 : ℕ) : ℝ) < B := hdk ▸ h2
    have hkB : (k : ℝ) ≤ B := by
      have : (k : ℝ) ≤ (d : ℝ) := by exact_mod_cast hkd
      linarith [show (d : ℝ) < B from h2]
    refine ⟨k, ?_, hdk ▸ hdn⟩
    simp only [hD, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hk1, Nat.le_floor hkB⟩, hdB⟩
  -- Union bound on the partial densities.
  have hcount : ∀ b : ℕ, 0 < b → S.partialDensity Set.univ b ≤ σ + D.card / b := by
    intro b hb
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have hden : ((Set.univ : Set ℕ) ∩ Set.Iio b).ncard = b := by
      rw [Set.univ_inter, ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
    set T := D.biUnion (fun k => (Finset.range b).filter (fun n => (k * m + 1) ∣ n)) with hT
    have hsub : (S ∩ Set.univ) ∩ Set.Iio b ⊆ (T : Set ℕ) := by
      rintro n ⟨⟨hn, -⟩, hnb⟩
      obtain ⟨k, hk, hkn⟩ := hcover n hn
      simp only [hT, Finset.coe_biUnion, Finset.coe_filter, Finset.mem_range, Set.mem_iUnion,
        Set.mem_ofPred_eq]
      exact ⟨k, hk, hnb, hkn⟩
    have hnum : (((S ∩ Set.univ) ∩ Set.Iio b).ncard : ℝ) ≤ b * σ + D.card := by
      have h1 : ((S ∩ Set.univ) ∩ Set.Iio b).ncard ≤ T.card := by
        rw [← Set.ncard_coe_finset T]
        exact Set.ncard_le_ncard hsub (Finset.finite_toSet T)
      have h2 : T.card ≤ ∑ k ∈ D, (b / (k * m + 1) + 1) :=
        Finset.card_biUnion_le.trans
          (Finset.sum_le_sum fun k _ => card_multiples_le b (k * m + 1) (Nat.succ_pos _))
      have h3 : ((∑ k ∈ D, (b / (k * m + 1) + 1) : ℕ) : ℝ) ≤
          ∑ k ∈ D, ((b : ℝ) / ((k * m + 1 : ℕ) : ℝ) + 1) := by
        push_cast
        refine Finset.sum_le_sum fun k _ => ?_
        have := Nat.cast_div_le (α := ℝ) (m := b) (n := k * m + 1)
        push_cast at this
        linarith
      have h4 : ∑ k ∈ D, ((b : ℝ) / ((k * m + 1 : ℕ) : ℝ) + 1) = b * σ + D.card := by
        rw [Finset.sum_add_distrib, hσ, Finset.mul_sum]
        simp [div_eq_mul_inv]
      calc (((S ∩ Set.univ) ∩ Set.Iio b).ncard : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast h1
        _ ≤ ((∑ k ∈ D, (b / (k * m + 1) + 1) : ℕ) : ℝ) := by exact_mod_cast h2
        _ ≤ _ := h3
        _ = _ := h4
    simp only [Set.partialDensity]
    rw [hden, div_le_iff₀ hbR]
    have : (σ + D.card / b) * b = b * σ + D.card := by field_simp
    linarith
  -- Hence δ ≤ σ.
  have hle : Erdos697.δ m α ≤ σ := by
    have ht : Tendsto (fun b : ℕ => σ + (D.card : ℝ) / b) atTop (𝓝 σ) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat (D.card : ℝ)).const_add σ
    refine le_of_tendsto_of_tendsto hδ ht ?_
    filter_upwards [eventually_gt_atTop 0] with b hb using hcount b hb
  -- And σ < (m ^ α + 1) / m.
  have hpow : (0 : ℝ) < (m : ℝ) ^ α := Real.rpow_pos_of_pos hmR α
  refine hle.trans_lt ?_
  rcases D.eq_empty_or_nonempty with hE | hne
  · rw [hσ, hE, Finset.sum_empty]
    positivity
  · obtain ⟨k₀, hk₀⟩ := hne
    have hk₀' := (Finset.mem_filter.mp hk₀).1
    have hK1 : 1 ≤ K := (Finset.mem_Icc.mp hk₀').1.trans (Finset.mem_Icc.mp hk₀').2
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
    have hKB : (K : ℝ) ≤ B := Nat.floor_le (Real.exp_pos _).le
    have hlog : Real.log K ≤ (m : ℝ) ^ α := by
      calc Real.log K ≤ Real.log B := Real.log_le_log hKpos hKB
        _ = _ := Real.log_exp _
    have hstep : σ < ∑ k ∈ D, 1 / ((k : ℝ) * m) := by
      refine Finset.sum_lt_sum_of_nonempty ⟨k₀, hk₀⟩ fun k hk => ?_
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have hpos : (0 : ℝ) < (k : ℝ) * m := mul_pos (by linarith) hmR
      apply one_div_lt_one_div_of_lt hpos
      push_cast
      linarith
    have hsub : ∑ k ∈ D, 1 / ((k : ℝ) * m) ≤ ∑ k ∈ Finset.Icc 1 K, 1 / ((k : ℝ) * m) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun k _ _ => ?_
      positivity
    have hharm : ∑ k ∈ Finset.Icc 1 K, 1 / ((k : ℝ) * m) = (harmonic K : ℝ) / m := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [one_div, mul_inv, div_eq_mul_inv]
    have hH : (harmonic K : ℝ) ≤ 1 + Real.log K := harmonic_le_one_add_log K
    calc σ < _ := hstep
      _ ≤ _ := hsub
      _ = _ := hharm
      _ ≤ (1 + Real.log K) / m := div_le_div_of_nonneg_right hH hmR.le
      _ ≤ ((m : ℝ) ^ α + 1) / m := div_le_div_of_nonneg_right (by linarith) hmR.le
