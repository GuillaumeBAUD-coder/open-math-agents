import OMAReductions.R_Erdos243_erdos_243_R1
import Mathlib

/-!
A rational reciprocal sum gives an integer numerator after multiplying each tail by
the initial denominator and the preceding denominators. Eventual doubling bounds
the remainder after the first term of each tail by a geometric series.

See Koizumi, *Irrationality of the reciprocal sum of doubly exponential
sequences*, https://arxiv.org/abs/2504.05933.
-/

namespace OMA.Erdos243IntegerTail

open Filter Finset
open scoped Topology

private theorem geometric_tail (b : ℕ → ℕ) (hp : ∀ n, 0 < b n)
    (hd : ∀ n, 2 * b n ≤ b (n + 1)) (n : ℕ)
    (hs : Summable (fun j => (b (j + n) : ℝ)⁻¹)) :
    (∑' j, (b (j + n) : ℝ)⁻¹) ≤ 2 * (b n : ℝ)⁻¹ := by
  have grow (j : ℕ) : 2 ^ j * b n ≤ b (j + n) := by
    induction j with
    | zero => simp
    | succ j hj =>
      rw [pow_succ', mul_assoc, show j + 1 + n = (j + n) + 1 by omega]
      exact (Nat.mul_le_mul_left 2 hj).trans (hd _)
  have term (j : ℕ) : (b (j + n) : ℝ)⁻¹ ≤ (b n : ℝ)⁻¹ * (1 / 2 : ℝ) ^ j := by
    have hgrow : (2 : ℝ) ^ j * (b n : ℝ) ≤ b (j + n) := by exact_mod_cast grow j
    have hpos : (0 : ℝ) < b n := by exact_mod_cast hp n
    calc
      _ ≤ ((2 : ℝ) ^ j * (b n : ℝ))⁻¹ := inv_anti₀ (by positivity) hgrow
      _ = _ := by rw [mul_inv_rev, ← inv_pow]; norm_num
  have hg := summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  refine (Summable.tsum_le_tsum term hs (hg.mul_left _)).trans_eq ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  ring_nf

private theorem relative_steps {c : ℕ → ℕ} (hp : ∀ n, 0 < c n)
    (h : Tendsto (fun n => (c (n + 1) : ℝ) / c n) atTop (𝓝 1)) :
    ∀ k : ℕ, ∃ N, ∀ n ≥ N,
      k * (c (n + 1) - c n) < c n ∧ k * (c n - c (n + 1)) < c n := by
  intro k
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h) (1 / ((k : ℝ) + 1)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hp' : (0 : ℝ) < c n := by exact_mod_cast hp n
  have hr := hN n hn
  rw [Real.dist_eq, show ((c (n + 1) : ℝ) / c n - 1) =
      ((c (n + 1) : ℝ) - c n) / c n by field_simp, abs_div, abs_of_pos hp'] at hr
  have hb : |(c (n + 1) : ℝ) - c n| < (c n : ℝ) / ((k : ℝ) + 1) := by
    simpa [div_eq_mul_inv, mul_comm] using (div_lt_iff₀ hp').mp hr
  have h1 := (lt_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)).mp hb
  have h2 : (k : ℝ) * |(c (n + 1) : ℝ) - c n| < c n := by
    nlinarith [abs_nonneg ((c (n + 1) : ℝ) - c n)]
  constructor
  · by_cases hs : c n ≤ c (n + 1)
    · have hs' : (c n : ℝ) ≤ c (n + 1) := by exact_mod_cast hs
      rw [abs_of_nonneg (sub_nonneg.mpr hs')] at h2
      exact_mod_cast (show (k : ℝ) * ((c (n + 1) - c n : ℕ) : ℝ) < c n by
        simpa only [Nat.cast_sub hs] using h2)
    · simpa [Nat.sub_eq_zero_of_le (by omega : c (n + 1) ≤ c n)] using hp n
  · by_cases hs : c (n + 1) ≤ c n
    · have hs' : (c (n + 1) : ℝ) ≤ c n := by exact_mod_cast hs
      rw [abs_of_nonpos (sub_nonpos.mpr hs'), neg_sub] at h2
      exact_mod_cast (show (k : ℝ) * ((c n - c (n + 1) : ℕ) : ℝ) < c n by
        simpa only [Nat.cast_sub hs] using h2)
    · simpa [Nat.sub_eq_zero_of_le (by omega : c n ≤ c (n + 1))] using hp n

theorem integer_tail : OMA.R_Erdos243_erdos_243_R1.H1 := by
  intro a hmono hlim hsum
  have hratio : Tendsto (fun n => (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1) := by
    simpa [Function.comp_def] using hlim.comp (tendsto_add_atTop_nat 1)
  have hlarge := hmono.tendsto_atTop.eventually_ge_atTop 4
  have hhalf : ∀ᶠ n in atTop, (1 / 2 : ℝ) < (a (n + 1) : ℝ) / (a n : ℝ) ^ 2 :=
    tendsto_const_nhds.eventually_lt hratio (by norm_num)
  obtain ⟨s, hs⟩ := eventually_atTop.mp (hlarge.and hhalf)
  let b (n : ℕ) := a (n + s)
  have hbmono : StrictMono b := fun _ _ h => hmono (Nat.add_lt_add_right h s)
  have hb4 (n : ℕ) : 4 ≤ b n := (hs _ (by omega : s ≤ n + s)).1
  have hbp (n : ℕ) : 0 < b n := by have := hb4 n; omega
  have hbR (n : ℕ) : (0 : ℝ) < b n := by exact_mod_cast hbp n
  have hbQ (n : ℕ) : (0 : ℚ) < b n := by exact_mod_cast hbp n
  have hquad (n : ℕ) : (b n : ℝ) ^ 2 / 2 < b (n + 1) := by
    have he := (hs _ (by omega : s ≤ n + s)).2
    change 1 / 2 < (a (n + s + 1) : ℝ) / (b n : ℝ) ^ 2 at he
    rw [show n + s + 1 = (n + 1) + s by omega] at he
    have ht := (lt_div_iff₀ (pow_pos (hbR n) 2)).mp he
    linarith
  have hdouble (n : ℕ) : 2 * b n ≤ b (n + 1) := by
    have h4 : (4 : ℝ) ≤ b n := by exact_mod_cast hb4 n
    exact_mod_cast (show (2 : ℝ) * (b n : ℝ) ≤ b (n + 1) by
      nlinarith [hquad n, mul_nonneg (sub_nonneg.mpr h4) (hbR n).le])
  have hbsum : Summable (fun n => (b n : ℚ)⁻¹) := by
    simpa [b, one_div] using (summable_nat_add_iff s).mpr hsum
  have htailSum (n : ℕ) : Summable (fun j => (b (j + n) : ℚ)⁻¹) :=
    (summable_nat_add_iff n).mpr hbsum
  let U (n : ℕ) : ℚ := ∑' j, (b (j + n) : ℚ)⁻¹
  let V (n : ℕ) : ℝ := U n
  have hVsum (n : ℕ) : HasSum (fun j => (b (j + n) : ℝ)⁻¹) (V n) := by
    have hcast := ((htailSum n).hasSum).map (Rat.castHom ℝ) Rat.continuous_coe_real
    simpa [V, U, Function.comp_def, Rat.cast_inv] using hcast
  have hUpos (n : ℕ) : 0 < U n := by
    have ht := (htailSum n).le_tsum 0 (fun j _ => by positivity)
    exact (inv_pos.mpr (hbQ (0 + n))).trans_le ht
  have hVpos (n : ℕ) : 0 < V n := by
    change (0 : ℝ) < (U n : ℝ)
    exact_mod_cast hUpos n
  have hUstep (n : ℕ) : U n = (b n : ℚ)⁻¹ + U (n + 1) := by
    simpa [U, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (htailSum n).tsum_eq_zero_add
  have hVstep (n : ℕ) : V n = (b n : ℝ)⁻¹ + V (n + 1) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (hUstep n)
    simpa [V, Rat.cast_inv] using h
  let d (n : ℕ) : ℕ := (U 0).den * ∏ j ∈ range n, b j
  have hdp (n : ℕ) : 0 < d n :=
    Nat.mul_pos (U 0).den_pos (Finset.prod_pos (fun j _ => hbp j))
  have hdstep (n : ℕ) : d (n + 1) = b n * d n := by simp [d, prod_range_succ, mul_assoc, mul_comm]
  let z : ℕ → ℤ := Nat.rec (U 0).num (fun n z => (b n : ℤ) * z - d n)
  have hzstep (n : ℕ) : z (n + 1) = (b n : ℤ) * z n - d n := rfl
  have hzExact (n : ℕ) : (Int.cast (z n) : ℚ) = (d n : ℚ) * U n := by
    induction n with
    | zero =>
      have hz0 : z 0 = (U 0).num := rfl
      have hd0 : d 0 = (U 0).den := by simp [d]
      rw [hz0, hd0]
      have hn : ((U 0).den : ℚ) ≠ 0 := by exact_mod_cast (U 0).den_ne_zero
      exact ((div_eq_iff hn).mp (Rat.num_div_den (U 0))).trans (mul_comm _ _)
    | succ n ih =>
      rw [hzstep, hdstep]
      push_cast
      rw [ih, hUstep n]
      field_simp [(hbQ n).ne']
      ring
  have hzpos (n : ℕ) : 0 < z n := by
    have hdq : (0 : ℚ) < d n := by exact_mod_cast hdp n
    have : (0 : ℚ) < (Int.cast (z n) : ℚ) := by
      rw [hzExact n]
      exact mul_pos hdq (hUpos n)
    exact_mod_cast this
  let c (n : ℕ) : ℕ := (z n).toNat
  have hcEq (n : ℕ) : (c n : ℤ) = z n := Int.toNat_of_nonneg (hzpos n).le
  have hcp (n : ℕ) : 0 < c n := by
    have hn : (0 : ℤ) < (c n : ℤ) := by rw [hcEq]; exact hzpos n
    exact_mod_cast hn
  have hcrec (n : ℕ) : c (n + 1) + d n = b n * c n := by
    exact_mod_cast (show (c (n + 1) : ℤ) + d n = (b n : ℤ) * c n by
      rw [hcEq (n + 1), hcEq n, hzstep, sub_add_cancel])
  have hcReal (n : ℕ) : (c n : ℝ) = (d n : ℝ) * V n := by
    have hq : (c n : ℚ) = (d n : ℚ) * U n := by
      rw [← hzExact n]
      exact_mod_cast hcEq n
    change (c n : ℝ) = (d n : ℝ) * (U n : ℝ)
    exact_mod_cast hq
  have hVbound (n : ℕ) : V n ≤ 2 * (b n : ℝ)⁻¹ :=
    (hVsum n).tsum_eq ▸ geometric_tail b hbp hdouble n (hVsum n).summable
  have hVerror (n : ℕ) : (b n : ℝ) * V n - 1 = (b n : ℝ) * V (n + 1) := by
    rw [hVstep n, mul_add, mul_inv_cancel₀ (hbR n).ne']
    ring
  have hblim : Tendsto (fun n => (b n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hbmono.tendsto_atTop
  have hRlim : Tendsto (fun n => (b n : ℝ) * V n) atTop (𝓝 1) := by
    have hzer : Tendsto (fun n => (b n : ℝ) * V (n + 1)) atTop (𝓝 0) := by
      refine squeeze_zero (g := fun n => 4 * (b n : ℝ)⁻¹)
        (fun n => mul_nonneg (hbR n).le (hVpos _).le) (fun n => ?_) ?_
      · have hbRecip : (b (n + 1) : ℝ)⁻¹ ≤ ((b n : ℝ) ^ 2 / 2)⁻¹ :=
          inv_anti₀ (div_pos (pow_pos (hbR n) 2) (by norm_num)) (hquad n).le
        calc
          _ ≤ (b n : ℝ) * (2 * ((b n : ℝ)^2/2)⁻¹) :=
            mul_le_mul_of_nonneg_left
              ((hVbound _).trans (mul_le_mul_of_nonneg_left hbRecip (by norm_num))) (hbR _).le
          _ = 4 * (b n : ℝ)⁻¹ := by
            field_simp [(hbR n).ne']
            ring
      · simpa using (tendsto_inv_atTop_zero.comp hblim).const_mul (4 : ℝ)
    have ht := tendsto_const_nhds.add hzer (f := fun n : ℕ => (1 : ℝ))
    simp only [add_zero] at ht
    refine ht.congr fun n => ?_
    linarith [hVerror n]
  have hbratio : Tendsto (fun n => (b (n + 1) : ℝ) / (b n : ℝ) ^ 2) atTop (𝓝 1) := by
    refine (hratio.comp (tendsto_add_atTop_nat s)).congr fun n => ?_
    change (a (n + s + 1) : ℝ) / (a (n + s) : ℝ)^2 =
      (a (n + 1 + s) : ℝ) / (a (n + s) : ℝ)^2
    rw [show n + s + 1 = n + 1 + s by omega]
  have hratioInv : Tendsto (fun n => (b n : ℝ)^2 / b (n + 1)) atTop (𝓝 1) := by
    simpa [inv_div] using hbratio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hRnext : Tendsto (fun n => (b (n + 1) : ℝ) * V (n + 1)) atTop (𝓝 1) :=
    (tendsto_add_atTop_iff_nat 1).mpr hRlim
  have hcratio : Tendsto (fun n => (c (n + 1) : ℝ) / c n) atTop (𝓝 1) := by
    have ht := hratioInv.mul (hRnext.div hRlim (by norm_num : (1 : ℝ) ≠ 0))
    simp only [div_one, mul_one] at ht
    refine ht.congr fun n => ?_
    change (b n : ℝ)^2 / b (n + 1) *
      (((b (n + 1) : ℝ) * V (n + 1)) / ((b n : ℝ) * V n)) =
      (c (n + 1) : ℝ) / c n
    rw [hcReal (n + 1), hcReal n, hdstep]
    push_cast
    have hdR : (0 : ℝ) < d n := by exact_mod_cast hdp n
    field_simp [(hbR n).ne', (hbR (n + 1)).ne', (hVpos n).ne', hdR.ne']
  exact ⟨s, c, d, hcp, hdp, hcrec, hdstep, relative_steps hcp hcratio⟩

end OMA.Erdos243IntegerTail

theorem OMA.solution : OMA.R_Erdos243_erdos_243_R1.H1 :=
  OMA.Erdos243IntegerTail.integer_tail
