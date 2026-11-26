import FormalConjectures.Wikipedia.ColossallyAbundantNumber
import Mathlib.NumberTheory.Harmonic.Bounds

/-! For each positive exponent the normalized divisor sum attains a maximum.
Doubling improves the unnormalized abundancy ratio, so by taking the exponent
small we can exclude any prescribed finite initial interval from the maximizers. -/

-- Problem: Alaoglu–Erdős Conjectures on Colossally Abundant Numbers — infinite colossallyAbundant
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/ColossallyAbundantNumber.lean:189 (declaration ColossallyAbundantNumber.infinite_colossallyAbundant)
-- Credit: @dk8827 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter ColossallyAbundantNumber
open scoped ArithmeticFunction.sigma Topology

namespace OMA.ColossallyAbundant

noncomputable def score (ε : ℝ) (n : ℕ) : ℝ :=
  (σ 1 n : ℝ) / (n : ℝ) ^ (1 + ε)

lemma sigma_ratio_le_harmonic {n : ℕ} (hn : 0 < n) :
    (σ 1 n : ℝ) / n ≤ harmonic n := by
  have hsub : n.divisors ⊆ Finset.Icc 1 n := by
    intro d hd
    exact Finset.mem_Icc.mpr
      ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)⟩
  rw [ArithmeticFunction.sigma_eq_sum_div]
  simp only [pow_one, Nat.cast_sum, Finset.sum_div]
  calc
    _ = ∑ d ∈ n.divisors, (d : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos := Nat.pos_of_mem_divisors hd
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
      rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hdR]
      field_simp
    _ ≤ ∑ d ∈ Finset.Icc 1 n, (d : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = harmonic n := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

lemma score_tendsto_zero {ε : ℝ} (hε : 0 < ε) :
    Tendsto (score ε) atTop (𝓝 0) := by
  have hinv : Tendsto (fun x : ℝ => (1 : ℝ) / x ^ ε) atTop (𝓝 0) := by
    refine (tendsto_rpow_neg_atTop hε).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_neg hx, one_div]
  have hlog := (isLittleO_log_rpow_atTop hε).tendsto_div_nhds_zero
  have hbound : Tendsto (fun x : ℝ => (1 + Real.log x) / x ^ ε) atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using hinv.add hlog
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  apply hzero.squeeze' (hbound.comp hnat)
  · exact Filter.Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    change score ε n ≤ (1 + Real.log n) / (n : ℝ) ^ ε
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [score, Real.rpow_add hnR, Real.rpow_one, ← div_div]
    exact div_le_div_of_nonneg_right
      ((sigma_ratio_le_harmonic hn).trans (harmonic_le_one_add_log n)) (by positivity)

lemma exists_maximizer {ε : ℝ} (hε : 0 < ε) :
    ∃ n > 1, ∀ k > 1, score ε k ≤ score ε n := by
  have htwo : 0 < score ε 2 := by
    rw [score, show σ 1 2 = 3 by decide]
    positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((score_tendsto_zero hε).eventually (gt_mem_nhds htwo))
  let bound := max 2 N
  have htwoMem : 2 ∈ Finset.Icc 2 bound := Finset.mem_Icc.mpr ⟨le_rfl, le_max_left _ _⟩
  obtain ⟨n, hn, hmax⟩ :=
    Finset.exists_max_image (Finset.Icc 2 bound) (score ε) ⟨2, htwoMem⟩
  refine ⟨n, (Finset.mem_Icc.mp hn).1, fun k hk => ?_⟩
  by_cases hkb : k ≤ bound
  · exact hmax k (Finset.mem_Icc.mpr ⟨hk, hkb⟩)
  · exact (hN k (le_trans (le_max_right _ _) (le_of_not_ge hkb))).le.trans (hmax 2 htwoMem)

lemma sigma_double_strict {n : ℕ} (hn : 0 < n) : 2 * σ 1 n < σ 1 (2 * n) := by
  let double : ℕ ↪ ℕ := ⟨fun d => 2 * d, by
    intro x y he
    change 2 * x = 2 * y at he
    omega⟩
  let evenDivisors := n.divisors.map double
  have hOne : 1 ∉ evenDivisors := by
    intro h
    obtain ⟨d, _, hd⟩ := Finset.mem_map.mp h
    change 2 * d = 1 at hd
    omega
  have hsub : insert 1 evenDivisors ⊆ (2 * n).divisors := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact Nat.one_mem_divisors.mpr (by omega)
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hd
      refine Nat.mem_divisors.mpr ⟨?_, by omega⟩
      obtain ⟨b, hb⟩ := Nat.dvd_of_mem_divisors ha
      exact ⟨b, by change 2 * n = (2 * a) * b; rw [hb, Nat.mul_assoc]⟩
  have hsum := Finset.sum_le_sum_of_subset (f := fun d : ℕ => d) hsub
  rw [Finset.sum_insert hOne] at hsum
  dsimp only [evenDivisors] at hsum
  rw [Finset.sum_map] at hsum
  change 1 + (∑ d ∈ n.divisors, 2 * d) ≤ ∑ d ∈ (2 * n).divisors, d at hsum
  rw [← Finset.mul_sum] at hsum
  simp only [ArithmeticFunction.sigma_apply, pow_one]
  omega

lemma score_continuous {n : ℕ} (hn : 0 < n) : Continuous (fun ε => score ε n) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : Continuous (fun ε : ℝ => (n : ℝ) ^ (1 + ε)) :=
    (Real.continuous_const_rpow hpos.ne').comp (continuous_const.add continuous_id)
  exact continuous_const.div hpow fun ε => (Real.rpow_pos_of_pos hpos _).ne'

lemma exists_exponent_excluding_small (B : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n ∈ Finset.Icc 2 B, score ε n < score ε (2 * n) := by
  have hnear : ∀ᶠ ε : ℝ in 𝓝 0, ∀ n ∈ Finset.Icc 2 B, score ε n < score ε (2 * n) := by
    apply (Filter.eventually_all_finset _).mpr
    intro n hn
    have hnpos : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    refine (score_continuous hnpos).continuousAt.eventually_lt
      (score_continuous (by omega : 0 < 2 * n)).continuousAt ?_
    simp only [score, add_zero, Real.rpow_one, Nat.cast_mul, Nat.cast_ofNat]
    apply (div_lt_div_iff₀ hnR (by positivity)).mpr
    have hsig : 2 * (σ 1 n : ℝ) < (σ 1 (2 * n) : ℝ) := by
      exact_mod_cast sigma_double_strict hnpos
    linarith only [mul_lt_mul_of_pos_right hsig hnR]
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := eventually_mem_nhdsWithin
  exact (hpos.and (hnear.filter_mono nhdsWithin_le_nhds)).exists

end OMA.ColossallyAbundant

theorem OMA.solution : type_of% @ColossallyAbundantNumber.infinite_colossallyAbundant := by
  by_contra h
  have hfinite := Set.not_infinite.mp h
  obtain ⟨B, hB⟩ := hfinite.bddAbove
  obtain ⟨ε, hε, hsmall⟩ := OMA.ColossallyAbundant.exists_exponent_excluding_small B
  obtain ⟨n, hn, hmax⟩ := OMA.ColossallyAbundant.exists_maximizer hε
  have hmem : n ∈ {k : ℕ | IsColossallyAbundant k} := ⟨hn, ε, hε, hmax⟩
  have hnb : n ≤ B := hB hmem
  exact (not_lt_of_ge (hmax (2 * n) (by omega))) (hsmall n (Finset.mem_Icc.mpr ⟨hn, hnb⟩))
