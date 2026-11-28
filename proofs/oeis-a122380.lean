import OMAStatements.S_oeis_a122380
import Mathlib

namespace OMA.A122380Proof

open OMA.S_oeis_a122380 Filter Topology


lemma exists_fact (N : ℕ) : ∃ y : ℕ, N ^ 2 < y.factorial :=
  ⟨N ^ 2 + 1, lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.self_le_factorial _)⟩

noncomputable def Y (N : ℕ) : ℕ := Nat.find (exists_fact N)

lemma Y_spec (N : ℕ) : N ^ 2 < (Y N).factorial := Nat.find_spec (exists_fact N)

lemma Y_pos {N : ℕ} (hN : 1 ≤ N) : 1 ≤ Y N := by
  by_contra h
  have h0 : Y N = 0 := by omega
  have := Y_spec N
  rw [h0] at this
  simp at this
  nlinarith

lemma Y_min {N : ℕ} (hN : 1 ≤ N) : (Y N - 1).factorial ≤ N ^ 2 := by
  have := Nat.find_min (exists_fact N) (m := Y N - 1) (by have := Y_pos hN; show Y N - 1 < Y N; omega)
  exact not_lt.mp this

lemma Y_tendsto : Tendsto Y atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  refine ⟨M.factorial, fun N hN => ?_⟩
  by_contra h
  have h1 := Nat.factorial_le (show Y N ≤ M by omega)
  have h2 := Y_spec N
  have : N ≤ N ^ 2 := by nlinarith
  omega

lemma bad_subset (N : ℕ) :
    (Finset.Icc 1 N).filter (fun k => ¬ k ^ 2 < (P k).factorial) ⊆
      Nat.smoothNumbersUpTo N (Y N) := by
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_Icc] at hk
  obtain ⟨⟨hk1, hkN⟩, hbad⟩ := hk
  rw [Nat.mem_smoothNumbersUpTo]
  refine ⟨hkN, ?_⟩
  rw [Nat.mem_smoothNumbers']
  intro p hp hpk
  by_contra hlt
  push Not at hlt
  have hpP : p ≤ P k := by
    unfold P
    exact Finset.le_sup (f := id) (Nat.mem_primeFactors.mpr ⟨hp, hpk, by omega⟩)
  have h1 := Nat.factorial_le (hlt.trans hpP)
  have h2 := Y_spec N
  have h3 : k ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hkN 2
  omega

lemma bad_card_le (N : ℕ) :
    ((Finset.Icc 1 N).filter (fun k => ¬ k ^ 2 < (P k).factorial)).card ≤
      2 ^ (Y N) * N.sqrt := by
  refine (Finset.card_le_card (bad_subset N)).trans ((Nat.smoothNumbersUpTo_card_le _ _).trans ?_)
  gcongr
  · norm_num
  · unfold Nat.primesBelow
    exact (Finset.card_filter_le _ _).trans (by simp)

lemma bad_ratio_le {N : ℕ} (hN : 1 ≤ N) :
    (((Finset.Icc 1 N).filter (fun k => ¬ k ^ 2 < (P k).factorial)).card : ℝ) / N ≤
      Real.sqrt (Real.sqrt (1 * (16:ℝ) ^ (Y N) / ((Y N - 1).factorial : ℝ))) := by
  set B := ((Finset.Icc 1 N).filter (fun k => ¬ k ^ 2 < (P k).factorial)).card
  set y := Y N
  set s := N.sqrt
  have hB : (B : ℝ) ≤ 2 ^ y * s := by exact_mod_cast bad_card_le N
  have hs : ((s : ℝ)) ^ 2 ≤ N := by exact_mod_cast Nat.sqrt_le' N
  have hF : (((y - 1).factorial : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast Y_min hN
  have hFpos : (0 : ℝ) < ((y - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : 0 ≤ (B : ℝ) / N := by positivity
  rw [Real.le_sqrt hx (Real.sqrt_nonneg _), Real.le_sqrt (by positivity) (by positivity)]
  rw [← pow_mul, div_pow, one_mul, div_le_div_iff₀ (by positivity) hFpos]
  have h1 : (B : ℝ) ^ (2 * 2) ≤ (2 ^ y * s) ^ 4 := by
    norm_num
    exact pow_le_pow_left₀ (by positivity) hB 4
  have h2 : ((2:ℝ) ^ y * s) ^ 4 = 16 ^ y * ((s:ℝ) ^ 2) ^ 2 := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm y 4, pow_mul]; norm_num
  have h3 : ((s:ℝ) ^ 2) ^ 2 ≤ (N:ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hs 2
  calc (B : ℝ) ^ (2 * 2) * ((y - 1).factorial : ℝ)
      ≤ (16 ^ y * (N:ℝ) ^ 2) * (N : ℝ) ^ 2 := by
        apply mul_le_mul _ hF hFpos.le (by positivity)
        rw [h2] at h1
        exact h1.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
    _ = 16 ^ y * (N:ℝ) ^ (2 * 2) := by ring

theorem main_proof :
    Tendsto (fun N : ℕ =>
        (((Finset.Icc 1 N).filter (fun k => k ^ 2 < (P k).factorial)).card : ℝ) / N)
      atTop (𝓝 1) := by
  have hg : Tendsto (fun N => Real.sqrt (Real.sqrt (1 * (16:ℝ) ^ (Y N) /
      ((Y N - 1).factorial : ℝ)))) atTop (𝓝 0) := by
    have := ((FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop (1:ℝ) 16 1).comp Y_tendsto)
    have h2 := (Real.continuous_sqrt.comp Real.continuous_sqrt).tendsto 0
    have h3 := h2.comp this
    rw [Function.comp_apply, Real.sqrt_zero, Real.sqrt_zero] at h3
    exact h3
  have hbad : Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N).filter (fun k => ¬ k ^ 2 < (P k).factorial)).card : ℝ) / N)
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
      (Eventually.of_forall fun N => by positivity) ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact bad_ratio_le hN
  have : Tendsto (fun N : ℕ =>
      1 - (((Finset.Icc 1 N).filter (fun k => ¬ k ^ 2 < (P k).factorial)).card : ℝ) / N)
      atTop (𝓝 1) := by simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hbad
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hsum := Finset.card_filter_add_card_filter_not
    (s := Finset.Icc 1 N) (fun k => k ^ 2 < (P k).factorial)
  simp only [Nat.card_Icc, add_tsub_cancel_right] at hsum
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [eq_div_iff hNpos.ne', sub_mul, div_mul_cancel₀ _ hNpos.ne', one_mul]
  have : ((((Finset.Icc 1 N).filter (fun k => k ^ 2 < (P k).factorial)).card : ℕ) : ℝ) +
      (((Finset.Icc 1 N).filter (fun k => ¬ k ^ 2 < (P k).factorial)).card : ℝ) = N := by
    exact_mod_cast hsum
  linarith


end OMA.A122380Proof

open OMA.A122380Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a122380.main := main_proof
