import OMAStatements.S_oeis_a001954

namespace OeisA001954Disproof

open Real OMA.S_oeis_a001954

private lemma hasSum_telescope :
    HasSum (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have hsum : ∀ N : ℕ,
        (∑ k ∈ Finset.range N, ((1 : ℝ) / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2))) =
          1 - 1 / ((N : ℝ) + 1) := by
      intro N
      induction N with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
    simp_rw [hsum]
    have hlim : Filter.Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using tendsto_const_nhds.sub hlim
  · intro k
    have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h2 : (k : ℝ) + 1 ≤ (k : ℝ) + 2 := by linarith
    have := one_div_le_one_div_of_le h1 h2
    linarith

private lemma re_riemannZeta_three_le_two : (riemannZeta 3).re ≤ 2 := by
  have hzeta : riemannZeta (3 : ℂ) = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ (3 : ℂ) :=
    zeta_eq_tsum_one_div_nat_add_one_cpow (by norm_num)
  have hterm : ∀ n : ℕ, (1 / ((n : ℂ) + 1) ^ (3 : ℂ)) = (((1 : ℝ) / ((n : ℝ) + 1) ^ 3 : ℝ) : ℂ) := by
    intro n
    have h3 : (3 : ℂ) = ((3 : ℕ) : ℂ) := by norm_num
    rw [h3, Complex.cpow_natCast]
    push_cast
    rfl
  have hre : (riemannZeta 3).re = ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 3 := by
    rw [hzeta]
    simp_rw [hterm]
    rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  rw [hre]
  have h1 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hsummable_real : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 3) := by
    have h2 : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 3) :=
      (summable_nat_add_iff 1).mpr h1
    simpa only [Nat.cast_add, Nat.cast_one] using h2
  rw [hsummable_real.tsum_eq_zero_add]
  have h0 : (1 : ℝ) / ((0 : ℕ) + 1 : ℝ) ^ 3 = 1 := by norm_num
  rw [h0]
  have hle : (∑' k : ℕ, (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 1) ^ 3) ≤
      ∑' k : ℕ, ((1 : ℝ) / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) := by
    apply Summable.tsum_le_tsum
    · intro k
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      have hdiff : (1 : ℝ) / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) =
          1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
        field_simp
        ring
      rw [hdiff]
      push_cast
      have hmul : ((k : ℝ) + 1) * ((k : ℝ) + 2) ≤ ((k : ℝ) + 1 + 1) ^ 3 := by
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        nlinarith [sq_nonneg ((k : ℝ) + 2)]
      exact one_div_le_one_div_of_le (by positivity) hmul
    · exact (summable_nat_add_iff 1).mpr hsummable_real
    · exact hasSum_telescope.summable
  rw [hasSum_telescope.tsum_eq] at hle
  linarith

theorem disproof_proof :
    ¬ (∀ n : ℕ, 1 ≤ n → s (a n) < 1 / (n : ℝ) ^ 2 ∧ 1 / (n : ℝ) ^ 2 < s (a n - 1)) := by
  intro hmain
  have h1 := (hmain 1 (le_refl 1)).2
  have ha1 : 2 ≤ a 1 := by
    unfold a
    have hsqrt : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg 2
    have hge : (2 : ℝ) ≤ ((1 : ℕ) + 1 / 2 : ℝ) * (2 + √2) := by nlinarith
    exact Nat.le_floor hge
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 (a 1 - 1) := by
    rw [Finset.mem_Icc]
    omega
  have hsum_ge : (1 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 (a 1 - 1), 1 / (k : ℝ) ^ 3 := by
    have hpos : ∀ k ∈ Finset.Icc 1 (a 1 - 1), (0 : ℝ) ≤ 1 / (k : ℝ) ^ 3 := fun k _ => by positivity
    have hsingle := Finset.single_le_sum hpos hmem
    simpa using hsingle
  have hs_le : s (a 1 - 1) ≤ 1 := by
    unfold s
    have hz := re_riemannZeta_three_le_two
    linarith
  norm_num at h1
  linarith

end OeisA001954Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a001954.main) :=
  OeisA001954Disproof.disproof_proof
