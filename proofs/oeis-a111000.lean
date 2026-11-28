import OMAStatements.S_oeis_a111000
import Mathlib

namespace OMA.A111000Proof

open OMA.S_oeis_a111000 Filter Topology

/-- `ζ(m + 2) - 1 = ∑_{k ≥ 0} 1/(k + 2)^(m + 2)`. -/
noncomputable def E (m : ℕ) : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 2) ^ (m + 2)

theorem summ_shift (j p : ℕ) (hp : 1 < p) : Summable (fun k : ℕ => 1 / ((k : ℝ) + j) ^ p) := by
  have h := (summable_nat_add_iff j).mpr (Real.summable_one_div_nat_pow.mpr hp)
  refine h.congr (fun k => ?_)
  push_cast; rfl

theorem summ2 (p : ℕ) (hp : 1 < p) : Summable (fun k : ℕ => 1 / ((k : ℝ) + 2) ^ p) := by
  exact_mod_cast summ_shift 2 p hp

theorem summ3 (p : ℕ) (hp : 1 < p) : Summable (fun k : ℕ => 1 / ((k : ℝ) + 3) ^ p) := by
  exact_mod_cast summ_shift 3 p hp

theorem zeta_eq (m : ℕ) : riemannZeta ((m + 2 : ℕ) : ℂ) = ((1 + E m : ℝ) : ℂ) := by
  rw [zeta_nat_eq_tsum_of_gt_one (by omega)]
  have h1 : ∑' k : ℕ, 1 / (k : ℂ) ^ (m + 2) = ((∑' k : ℕ, 1 / (k : ℝ) ^ (m + 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]; push_cast; rfl
  rw [h1]
  congr 1
  have hs : Summable (fun k : ℕ => 1 / (k : ℝ) ^ (m + 2)) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  rw [← hs.sum_add_tsum_nat_add 2]
  simp [Finset.sum_range_succ, E]

theorem E_split (m : ℕ) : E m = 1 / 2 ^ (m + 2) + ∑' k : ℕ, 1 / ((k : ℝ) + 3) ^ (m + 2) := by
  unfold E
  rw [(summ2 (m + 2) (by omega)).tsum_eq_zero_add]
  congr 1
  · simp
  · apply tsum_congr; intro k; push_cast; ring_nf

noncomputable def S : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 3) ^ 2

theorem E_lower (m : ℕ) : 1 / 2 ^ (m + 2) ≤ E m := by
  rw [E_split]
  have : 0 ≤ ∑' k : ℕ, 1 / ((k : ℝ) + 3) ^ (m + 2) := tsum_nonneg (fun k => by positivity)
  linarith

theorem E_upper (m : ℕ) : E m ≤ 1 / 2 ^ (m + 2) + S * (1 / 3) ^ m := by
  rw [E_split]
  have h : ∑' k : ℕ, 1 / ((k : ℝ) + 3) ^ (m + 2) ≤ ∑' k : ℕ, 1 / ((k : ℝ) + 3) ^ 2 * (1 / 3) ^ m := by
    apply Summable.tsum_le_tsum _ (summ3 (m + 2) (by omega))
      ((summ3 2 (by omega)).mul_right _)
    intro k
    have hx : (3 : ℝ) ≤ (k : ℝ) + 3 := by linarith [k.cast_nonneg (α := ℝ)]
    have hx0 : (0 : ℝ) < (k : ℝ) + 3 := by linarith
    rw [show 1 / ((k : ℝ) + 3) ^ (m + 2) = 1 / ((k : ℝ) + 3) ^ 2 * (1 / ((k : ℝ) + 3)) ^ m by
      rw [one_div_pow, one_div_mul_one_div, ← pow_add, show 2 + m = m + 2 from Nat.add_comm 2 m]]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_div_iff₀ hx0 (by norm_num)]; linarith
  rw [tsum_mul_right] at h
  unfold S
  linarith

theorem E_pos (m : ℕ) : 0 < E m := lt_of_lt_of_le (by positivity) (E_lower m)

theorem B_tendsto : Tendsto (fun m : ℕ => 2 ^ (m + 2) * E m) atTop (𝓝 1) := by
  have hS : 0 ≤ S := tsum_nonneg (fun k => by positivity)
  have hup : Tendsto (fun m : ℕ => 1 + 4 * S * (2 / 3 : ℝ) ^ m) atTop (𝓝 (1 + 4 * S * 0)) :=
    tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
      (by norm_num)).const_mul _)
  rw [mul_zero, add_zero] at hup
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
  · intro m
    have := E_lower m
    have h2 : (0 : ℝ) < 2 ^ (m + 2) := by positivity
    simp only
    rw [div_le_iff₀ h2] at this
    linarith
  · intro m
    have := E_upper m
    have h2 : (0 : ℝ) < 2 ^ (m + 2) := by positivity
    simp only
    have e1 : (2 : ℝ) ^ (m + 2) * (1 / 2 ^ (m + 2) + S * (1 / 3) ^ m) =
        1 + 4 * S * (2 / 3) ^ m := by
      simp only [div_pow, one_pow, pow_add]; field_simp; ring
    calc (2 : ℝ) ^ (m + 2) * E m ≤ 2 ^ (m + 2) * (1 / 2 ^ (m + 2) + S * (1 / 3) ^ m) :=
          mul_le_mul_of_nonneg_left this h2.le
      _ = _ := e1

theorem E_tendsto : Tendsto E atTop (𝓝 0) := by
  have h := B_tendsto.mul ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).comp (tendsto_add_atTop_nat 2))
  rw [one_mul] at h
  refine h.congr (fun m => ?_)
  simp only [Function.comp]
  rw [div_pow, one_pow]; field_simp

theorem zz_eq (m : ℕ) : zz (m + 2) = (riemannZeta ((1 + E m : ℝ) : ℂ)).re := by
  unfold zz
  rw [zeta_eq, Complex.ofReal_re]

theorem A_tendsto : Tendsto (fun m : ℕ => E m * zz (m + 2)) atTop (𝓝 1) := by
  have hg : Tendsto (fun m : ℕ => ((1 + E m : ℝ) : ℂ)) atTop (𝓝[≠] 1) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall (fun m => ?_)⟩
    · have h0 : Tendsto (fun m => (1 : ℝ) + E m) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add E_tendsto
      rw [add_zero] at h0
      have := (Complex.continuous_ofReal.tendsto 1).comp h0
      rw [Complex.ofReal_one] at this
      exact this
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have h' : (1 + E m : ℝ) = 1 := by exact_mod_cast h
      linarith [E_pos m]
  have h := riemannZeta_residue_one.comp hg
  have h2 := (Complex.continuous_re.tendsto _).comp h
  rw [Complex.one_re] at h2
  refine h2.congr (fun m => ?_)
  simp only [Function.comp]
  rw [zz_eq, show ((1 + E m : ℝ) : ℂ) - 1 = ((E m : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul]

end OMA.A111000Proof

open OMA.A111000Proof Filter Topology in
theorem OMA.solution : type_of% @OMA.S_oeis_a111000.main := by
  rw [← tendsto_add_atTop_iff_nat 2]
  have hA := A_tendsto
  have hA1 := A_tendsto.comp (tendsto_add_atTop_nat 1)
  have hB := B_tendsto
  have hB1 := B_tendsto.comp (tendsto_add_atTop_nat 1)
  have h := ((hA.div hA1 one_ne_zero).mul (hB1.div hB one_ne_zero)).div_const 2
  norm_num at h
  refine h.congr (fun m => ?_)
  have e0 := E_pos m
  have e1 := E_pos (m + 1)
  have hz : OMA.S_oeis_a111000.zz (m + 2 + 1) = OMA.S_oeis_a111000.zz (m + 1 + 2) := rfl
  rw [hz]
  by_cases h0 : OMA.S_oeis_a111000.zz (m + 1 + 2) = 0
  · simp [h0]
  · field_simp
    ring
