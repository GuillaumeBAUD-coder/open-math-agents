import OMAStatements.S_oeis_a076902
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
Strong induction and asymptotic squeeze proof for OEIS A076902:
the error e n = a n - n / 3 satisfies |e n| <= |e (n / 2)| + 1 / 3 for n >= 2,
yielding |e n| < log (n + 1) for n > 0 and (a n) / (n / 3) -> 1.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a076902.main := by
  let e : ℕ → ℝ := fun n => (OMA.S_oeis_a076902.a n : ℝ) - (n : ℝ) / 3
  have ha1 : OMA.S_oeis_a076902.a 1 = 1 := by
    unfold OMA.S_oeis_a076902.a
    simp
  have ha2 : OMA.S_oeis_a076902.a 2 = 0 := by
    conv_lhs => unfold OMA.S_oeis_a076902.a
    simp [ha1]
  have ha3 : OMA.S_oeis_a076902.a 3 = 0 := by
    conv_lhs => unfold OMA.S_oeis_a076902.a
    simp [ha1]
  have hstep : ∀ n : ℕ, 2 ≤ n → |e n| ≤ |e (n / 2)| + 1 / 3 := by
    intro n hn
    have ha_rec : OMA.S_oeis_a076902.a n = ((n / 2 : ℕ) : ℤ) - OMA.S_oeis_a076902.a (n / 2) := by
      conv_lhs => unfold OMA.S_oeis_a076902.a
      simp [show ¬ (n ≤ 1) by omega]
    have ha_rec_r : (OMA.S_oeis_a076902.a n : ℝ) =
        ((n / 2 : ℕ) : ℝ) - (OMA.S_oeis_a076902.a (n / 2) : ℝ) := by
      rw [ha_rec, Int.cast_sub, Int.cast_natCast]
    have hdiv : n = 2 * (n / 2) + n % 2 := (Nat.div_add_mod n 2).symm
    have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
    have he_eq : e n = -e (n / 2) - ((n % 2 : ℕ) : ℝ) / 3 := by
      dsimp [e]
      have hdiv_r : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) + ((n % 2 : ℕ) : ℝ) := by exact_mod_cast hdiv
      rw [ha_rec_r, hdiv_r]
      ring
    rw [he_eq, sub_eq_add_neg]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_neg]
    rcases hmod with hr | hr <;> rw [hr] <;> simp only [Nat.cast_zero, Nat.cast_one,
      zero_div, abs_zero, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)] <;> linarith
  have hlog2 : (2 : ℝ) / 3 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog3 : (2 : ℝ) / 3 < Real.log 3 := by
    exact hlog2.trans (Real.log_lt_log (by norm_num) (by norm_num))
  have hlog4 : (1 : ℝ) < Real.log 4 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact Real.exp_one_lt_three.trans (by norm_num)
  have hlog53 : (1 : ℝ) / 3 < Real.log (5 / 3) := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have hexp3 : Real.exp (1 / 3) ^ 3 < (5 / 3 : ℝ) ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
      exact Real.exp_one_lt_three.trans (by norm_num)
    by_contra hge
    push Not at hge
    have hp3 : (5 / 3 : ℝ) ^ 3 ≤ Real.exp (1 / 3) ^ 3 := by gcongr
    linarith
  have hbound : ∀ n : ℕ, 0 < n → |e n| < Real.log ((n : ℝ) + 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hn1 : n = 1
      · subst hn1
        have he1 : e 1 = 2 / 3 := by dsimp [e]; rw [ha1]; norm_num
        rw [he1, abs_of_pos (by norm_num)]
        norm_num
        exact hlog2
      · by_cases hn2 : n = 2
        · subst hn2
          have he2 : e 2 = -(2 / 3) := by dsimp [e]; rw [ha2]; norm_num
          rw [he2, abs_neg, abs_of_pos (by norm_num)]
          norm_num
          exact hlog3
        · by_cases hn3 : n = 3
          · subst hn3
            have he3 : e 3 = -1 := by dsimp [e]; rw [ha3]; norm_num
            rw [he3, abs_neg, abs_one]
            norm_num
            exact hlog4
          · have hn4 : 4 ≤ n := by omega
            have hm2 : 2 ≤ n / 2 := by omega
            have hmlt : n / 2 < n := Nat.div_lt_self hn (by omega)
            have ihm := ih (n / 2) hmlt (by omega)
            have hs := hstep n (by omega)
            have h1 : |e n| < Real.log (((n / 2 : ℕ) : ℝ) + 1) + Real.log (5 / 3) := by
              linarith
            have h2 : Real.log (((n / 2 : ℕ) : ℝ) + 1) + Real.log (5 / 3) =
                Real.log ((((n / 2 : ℕ) : ℝ) + 1) * (5 / 3)) := by
              rw [← Real.log_mul (by positivity) (by positivity)]
            have h3 : (((n / 2 : ℕ) : ℝ) + 1) * (5 / 3) ≤ (n : ℝ) + 1 := by
              have hdiv : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
              have hdiv_r : 2 * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdiv
              have hm2_r : (2 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hm2
              linarith
            have h4 : Real.log ((((n / 2 : ℕ) : ℝ) + 1) * (5 / 3)) ≤ Real.log ((n : ℝ) + 1) :=
              Real.log_le_log (by positivity) h3
            linarith
  refine ⟨hbound, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hzero : Filter.Tendsto (fun n : ℕ => 3 * (Real.log 2 / (n : ℝ) + Real.log (n : ℝ) / (n : ℝ)))
      Filter.atTop (nhds 0) := by
    have hA : Filter.Tendsto (fun n : ℕ => Real.log 2 / (n : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hB : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
    simpa using tendsto_const_nhds.mul (hA.add hB)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
    (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hdiff : (OMA.S_oeis_a076902.a n : ℝ) / ((n : ℝ) / 3) - 1 = 3 * e n / (n : ℝ) := by
    dsimp [e]
    field_simp [hn_pos.ne']
  rw [Real.norm_eq_abs, hdiff, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3),
    abs_of_pos hn_pos]
  have hb := hbound n hn
  have hlog_le : Real.log ((n : ℝ) + 1) ≤ Real.log 2 + Real.log (n : ℝ) := by
    have hle : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    calc Real.log ((n : ℝ) + 1) ≤ Real.log (2 * (n : ℝ)) := Real.log_le_log (by positivity) hle
      _ = Real.log 2 + Real.log (n : ℝ) := Real.log_mul (by norm_num) hn_pos.ne'
  have hnum : |e n| ≤ Real.log 2 + Real.log (n : ℝ) := hb.le.trans hlog_le
  have hdiv_le : 3 * |e n| / (n : ℝ) ≤ 3 * (Real.log 2 / (n : ℝ) + Real.log (n : ℝ) / (n : ℝ)) := by
    have h1 : 3 * |e n| / (n : ℝ) ≤ 3 * (Real.log 2 + Real.log (n : ℝ)) / (n : ℝ) := by gcongr
    have h2 : 3 * (Real.log 2 + Real.log (n : ℝ)) / (n : ℝ) =
        3 * (Real.log 2 / (n : ℝ) + Real.log (n : ℝ) / (n : ℝ)) := by ring
    exact h1.trans_eq h2
  exact hdiv_le
