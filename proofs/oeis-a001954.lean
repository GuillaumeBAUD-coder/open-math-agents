import OMAStatements.S_oeis_a001954

namespace ZetaTailCounterexample

open Real OMA.S_oeis_a001954

private theorem zetaThreeLeTwo : (riemannZeta 3).re ≤ 2 := by
  have hz : (riemannZeta 3).re = ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 3 := by
    have hzC : riemannZeta 3 = ∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ 3 :=
      zeta_nat_eq_tsum_of_gt_one (k := 3) (by decide)
    rw [hzC]
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_one,
      ← Complex.ofReal_div, ← Complex.ofReal_tsum, Complex.ofReal_re]
  rw [hz]
  have hterm (n : ℕ) : (1 : ℝ) / (n : ℝ) ^ 3 ≤ 1 / (n : ℝ) ^ 2 := by
    cases n with
    | zero => simp
    | succ n =>
      have hn : (1 : ℝ) ≤ (n.succ : ℝ) := by exact_mod_cast Nat.succ_pos n
      apply one_div_le_one_div_of_le (by positivity)
      rw [pow_succ]
      exact le_mul_of_one_le_right (by positivity) hn
  have hsum := (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 3)).tsum_le_tsum
    hterm hasSum_zeta_two.summable
  rw [hasSum_zeta_two.tsum_eq] at hsum
  have hp : π ^ 2 < (3.15 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ pi_lt_d2 pi_pos.le (by decide)
  linarith

theorem tailLeOne : s (a 1 - 1) ≤ 1 := by
  have ha : 2 ≤ a 1 := by
    apply Nat.le_floor
    push_cast
    have hs := Real.sqrt_nonneg 2
    linarith
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 (a 1 - 1) :=
    Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hsum : (1 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 (a 1 - 1), (1 : ℝ) / (k : ℝ) ^ 3 := by
    calc
      (1 : ℝ) = 1 / ((1 : ℕ) : ℝ) ^ 3 := by norm_num
      _ ≤ _ := Finset.single_le_sum (f := fun k : ℕ => (1 : ℝ) / (k : ℝ) ^ 3)
        (fun k _ => by positivity) hmem
  unfold s
  linarith [zetaThreeLeTwo]

end ZetaTailCounterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a001954.main) := by
  intro h
  have hbad := (h 1 (by decide)).2
  norm_num at hbad
  exact (not_lt_of_ge ZetaTailCounterexample.tailLeOne) hbad
