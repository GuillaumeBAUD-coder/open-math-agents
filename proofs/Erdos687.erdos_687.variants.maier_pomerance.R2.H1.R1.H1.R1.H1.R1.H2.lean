import OMAReductions.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H1_R1
import Mathlib

theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H1_R1.H2 := by
  unfold OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H1_R1.H2
  intro l f
  have hl1 : (0.6931471803 : ℝ) < l := Real.log_two_gt_d9
  have hl2 : l < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hl0 : 0 < l := by linarith
  have hf : ∀ n, f n = ((n : ℝ) + 5) ^ 2 * (l ^ (n + 4) / ((n + 4).factorial : ℝ)) := fun n => rfl
  have hpos : ∀ n, 0 ≤ f n := fun n => by rw [hf]; positivity
  have hstep : ∀ n, f (n + 1) ≤ f n / 4 := by
    intro n
    rw [hf, hf]
    have e1 : ((n + 1 + 4).factorial : ℝ) = ((n : ℝ) + 5) * ((n + 4).factorial : ℝ) := by
      rw [show n + 1 + 4 = (n + 4) + 1 from rfl, Nat.factorial_succ]; push_cast; ring
    have e2 : l ^ (n + 1 + 4) = l ^ (n + 4) * l := by
      rw [show n + 1 + 4 = (n + 4) + 1 from rfl, pow_succ]
    rw [e1, e2]
    push_cast
    have hF : 0 < ((n + 4).factorial : ℝ) := by positivity
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have key : ((n : ℝ) + 6) ^ 2 * l ≤ ((n : ℝ) + 5) ^ 3 / 4 := by
      have h1 : ((n : ℝ) + 6) ^ 2 * l ≤ ((n : ℝ) + 6) ^ 2 * 0.7 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith [hn, mul_nonneg hn hn, mul_nonneg (mul_nonneg hn hn) hn]
    have ht : 0 ≤ l ^ (n + 4) / ((n + 4).factorial : ℝ) := by positivity
    calc ((n : ℝ) + 1 + 5) ^ 2 * (l ^ (n + 4) * l / (((n : ℝ) + 5) * ((n + 4).factorial : ℝ)))
        = (l ^ (n + 4) / ((n + 4).factorial : ℝ)) * ((((n : ℝ) + 6) ^ 2 * l) / ((n : ℝ) + 5)) := by
          field_simp; ring
      _ ≤ (l ^ (n + 4) / ((n + 4).factorial : ℝ)) * ((((n : ℝ) + 5) ^ 3 / 4) / ((n : ℝ) + 5)) := by
          gcongr
      _ = ((n : ℝ) + 5) ^ 2 * (l ^ (n + 4) / ((n + 4).factorial : ℝ)) / 4 := by
          field_simp
  have hgeo : ∀ n, f (n + 1) ≤ f 1 * (1 / 4 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have := hstep (k + 1)
      rw [pow_succ]
      linarith
  have hg : Summable (fun n : ℕ => f 1 * (1 / 4 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hs1 : Summable (fun n : ℕ => f (n + 1)) :=
    Summable.of_nonneg_of_le (fun n => hpos _) hgeo hg
  have hs : Summable f := (summable_nat_add_iff 1).mp hs1
  refine ⟨hs, ?_⟩
  have htail : ∑' n, f (n + 1) ≤ f 1 * (4 / 3) := by
    calc ∑' n, f (n + 1) ≤ ∑' n : ℕ, f 1 * (1 / 4 : ℝ) ^ n := hs1.tsum_le_tsum hgeo hg
      _ = f 1 * (4 / 3) := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  have htot : ∑' n, f n ≤ f 0 + f 1 * (4 / 3) := by
    rw [hs.tsum_eq_zero_add]; linarith
  have h0 : f 0 = 25 / 24 * l ^ 4 := by rw [hf]; norm_num [Nat.factorial]; ring
  have h1 : f 1 = 3 / 10 * l ^ 5 := by rw [hf]; norm_num [Nat.factorial]; ring
  have hc : 0 ≤ (1 / 2 : ℝ) * (3 / l - 2) := by
    have : 2 ≤ 3 / l := by rw [le_div_iff₀ hl0]; linarith
    linarith
  have hb3 : l ^ 3 < 0.33311 := by
    have := pow_lt_pow_left₀ hl2 hl0.le (by norm_num : (3 : ℕ) ≠ 0)
    norm_num at this
    linarith
  have hb30 : 0 < l ^ 3 := by positivity
  have ha : 3 - 2 * l < 1.6138 := by linarith
  have ha0 : 0 < 3 - 2 * l := by linarith
  have hcb : 25 / 24 + 2 / 5 * l < 1.3190 := by linarith
  have hcb0 : 0 < 25 / 24 + 2 / 5 * l := by linarith
  have hab : (3 - 2 * l) * l ^ 3 < 1.6138 * 0.33311 := mul_lt_mul'' ha hb3 ha0.le hb30.le
  have habc : (3 - 2 * l) * l ^ 3 * (25 / 24 + 2 / 5 * l) < 1.6138 * 0.33311 * 1.3190 :=
    mul_lt_mul'' hab hcb (by positivity) hcb0.le
  calc (1 / 2 : ℝ) * (3 / l - 2) * ∑' n, f n
      ≤ (1 / 2 : ℝ) * (3 / l - 2) * (f 0 + f 1 * (4 / 3)) := mul_le_mul_of_nonneg_left htot hc
    _ = (3 - 2 * l) * l ^ 3 * (25 / 24 + 2 / 5 * l) / 2 := by
        rw [h0, h1]; field_simp; ring
    _ < 37 / 100 := by norm_num at habc ⊢; linarith
