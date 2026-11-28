import OMAStatements.S_oeis_a288229

namespace Discovery
open OMA.S_oeis_a288229 PowerSeries Finset

noncomputable abbrev seq := a (Real.pi / 2)
noncomputable abbrev den := denominator (Real.pi / 2)
noncomputable abbrev wt := weight (Real.pi / 2)

theorem weight_zero : wt 0 = 1 := by
  have h : ⌊Real.pi / 2⌋ = (1 : ℤ) := Int.floor_eq_iff.mpr
    ⟨by push_cast; linarith [Real.pi_gt_three], by push_cast; linarith [Real.pi_lt_four]⟩
  norm_num [wt, weight, h]

theorem den_unit : constantCoeff den = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simpa only [den, denominator, coeff_mk, pow_zero, one_mul] using weight_zero

theorem initial : seq 0 = 1 := by
  change coeff 0 den⁻¹ = 1
  rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_inv, den_unit, inv_one]

theorem reciprocal_recurrence (n : ℕ) :
    seq (n+1) = -∑ j ∈ range (n+1), seq j * ((-1 : ℚ)^(n+1-j) * wt (n+1-j)) := by
  have h := congrArg (coeff (R := ℚ) (n+1)) (show den⁻¹ * den = 1 by
    rw [mul_comm, PowerSeries.mul_inv_cancel den (by rw [den_unit]; norm_num)])
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ] at h
  simp only [Nat.sub_self, coeff_one, Nat.succ_ne_zero, if_false] at h
  change (∑ j ∈ range (n+1), seq j * coeff (n+1-j) den) + seq (n+1) * coeff 0 den = 0 at h
  rw [coeff_zero_eq_constantCoeff_apply, den_unit, mul_one] at h
  rw [eq_neg_iff_add_eq_zero, add_comm]
  simpa only [den, denominator, coeff_mk, wt] using h


theorem weight_step (n : ℕ) : 1 ≤ wt (n+1) - wt n ∧ wt (n+1) - wt n ≤ 2 := by
  let x : ℝ := ((n : ℝ)+1) * (Real.pi / 2)
  let y : ℝ := (((n+1 : ℕ) : ℝ)+1) * (Real.pi / 2)
  have hy : y = x + Real.pi / 2 := by dsimp [x,y]; push_cast; ring
  have hpos : (0 : ℝ) < (⌊y⌋ : ℝ) - (⌊x⌋ : ℝ) := by
    linarith [Int.lt_floor_add_one y, Int.floor_le x, Real.pi_gt_three]
  have hsmall : (⌊y⌋ : ℝ) - (⌊x⌋ : ℝ) < 3 := by
    linarith [Int.floor_le y, Int.lt_floor_add_one x, Real.pi_lt_four]
  have h1 : (0 : ℤ) < ⌊y⌋ - ⌊x⌋ := by exact_mod_cast hpos
  have h2 : ⌊y⌋ - ⌊x⌋ < (3 : ℤ) := by exact_mod_cast hsmall
  change 1 ≤ (⌊y⌋ : ℚ) - (⌊x⌋ : ℚ) ∧ (⌊y⌋ : ℚ) - (⌊x⌋ : ℚ) ≤ 2
  constructor
  · exact_mod_cast (show 1 ≤ ⌊y⌋ - ⌊x⌋ by omega)
  · exact_mod_cast (show ⌊y⌋ - ⌊x⌋ ≤ 2 by omega)

noncomputable abbrev shift (p : PowerSeries ℚ) := p + X*p
noncomputable abbrev filterSeries (p : PowerSeries ℚ) := shift p - X*(X*shift p)
noncomputable abbrev err (k : ℕ) := coeff k (filterSeries den)

theorem error_bound (n : ℕ) : |err (n+3)| ≤ 1 := by
  change |coeff (n+3) (filterSeries den)| ≤ 1
  simp only [filterSeries, shift, map_sub, map_add, coeff_succ_X_mul, den, denominator, coeff_mk]
  change |(-1 : ℚ)^(n+3)*wt (n+3) + (-1 : ℚ)^(n+2)*wt (n+2) -
    ((-1 : ℚ)^(n+1)*wt (n+1) + (-1 : ℚ)^n*wt n)| ≤ 1
  have h : (-1 : ℚ)^(n+3)*wt (n+3) + (-1 : ℚ)^(n+2)*wt (n+2) -
      ((-1 : ℚ)^(n+1)*wt (n+1) + (-1 : ℚ)^n*wt n) =
      (-1 : ℚ)^n*((wt (n+1)-wt n)-(wt (n+3)-wt (n+2))) := by simp only [pow_succ]; ring
  rw [h, abs_mul, abs_pow]; norm_num
  exact abs_le.mpr ⟨by linarith [(weight_step n).1,(weight_step (n+2)).2],
                    by linarith [(weight_step n).2,(weight_step (n+2)).1]⟩


theorem weight_prefix : wt 0=1 ∧ wt 1=3 ∧ wt 2=4 ∧ wt 3=6 ∧ wt 4=7 ∧ wt 5=9 ∧ wt 6=10 ∧ wt 7=12 := by
  repeat' apply And.intro
  all_goals
    unfold wt weight
    norm_cast
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith [Real.pi_gt_d4,Real.pi_lt_d4]

theorem error_prefix : err 0=1 ∧ err 1= -2 ∧ err 2=0 ∧ err 3=0 ∧ err 4=0 ∧ err 5=0 ∧ err 6=0 ∧ err 7=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := weight_prefix
  have hd (k : ℕ) : coeff k den = (-1 : ℚ)^k * wt k := coeff_mk _ _
  norm_num [err,filterSeries,shift,coeff_succ_X_mul,coeff_zero_X_mul,hd,den_unit,h0,h1,h2,h3,h4,h5,h6,h7]


theorem seq_prefix : seq 0=1 ∧ seq 1=3 ∧ seq 2=5 ∧ seq 3=9 ∧ seq 4=18 ∧ seq 5=36 ∧ seq 6=72 := by
  obtain ⟨w0,w1,w2,w3,w4,w5,w6,_⟩ := weight_prefix
  have h0 := initial
  have h1 := reciprocal_recurrence 0
  norm_num [sum_range_succ,h0,w0,w1] at h1
  have h2 := reciprocal_recurrence 1
  norm_num [sum_range_succ,h0,h1,w0,w1,w2] at h2
  have h3 := reciprocal_recurrence 2
  norm_num [sum_range_succ,h0,h1,h2,w0,w1,w2,w3] at h3
  have h4 := reciprocal_recurrence 3
  norm_num [sum_range_succ,h0,h1,h2,h3,w0,w1,w2,w3,w4] at h4
  have h5 := reciprocal_recurrence 4
  norm_num [sum_range_succ,h0,h1,h2,h3,h4,w0,w1,w2,w3,w4,w5] at h5
  have h6 := reciprocal_recurrence 5
  norm_num [sum_range_succ,h0,h1,h2,h3,h4,h5,w0,w1,w2,w3,w4,w5,w6] at h6
  exact ⟨h0,h1,h2,h3,h4,h5,h6⟩


theorem filtered_product : den⁻¹ * filterSeries den = filterSeries 1 := by
  have hd := PowerSeries.mul_inv_cancel den (show constantCoeff den ≠ 0 by rw [den_unit]; norm_num)
  dsimp only [filterSeries,shift]
  linear_combination (1 + (X : PowerSeries ℚ) - X^2 - X^3) * hd

theorem filtered_lower (n : ℕ) (hn : ∀ j ≤ n+5, 0 ≤ seq j) :
    2 * seq (n+5) - ∑ j ∈ range (n+1), seq j ≤ seq (n+6) := by
  have hc := congrArg (coeff (R := ℚ) (n+6)) filtered_product
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  change (∑ j ∈ range (n+6+1), seq j * err (n+6-j)) = coeff (n+6) (filterSeries 1) at hc
  have hz : coeff (n+6) (filterSeries 1) = 0 := by
    simp [filterSeries,shift,coeff_succ_X_mul,coeff_one,coeff_X]
  obtain ⟨h0,h1,h2,h3,h4,h5,_,_⟩ := error_prefix
  rw [hz] at hc
  iterate 6 rw [sum_range_succ] at hc
  simp only [Nat.add_sub_add_left, Nat.sub_self, h0,h1,h2,h3,h4,h5,mul_zero,mul_one,add_zero] at hc
  have ht : (∑ j ∈ range (n+1), seq j * err (n+6-j)) ≤ ∑ j ∈ range (n+1), seq j := by
    apply sum_le_sum
    intro j hj
    have hj' := mem_range.mp hj
    have he := (abs_le.mp (error_bound (n+6-j-3))).2
    rw [show n+6-j-3+3 = n+6-j by omega] at he
    exact mul_le_of_le_one_right (hn j (by omega)) he
  linarith


theorem growth_induction (u : ℕ → ℚ)
    (start : ∀ n ≤ 5, 0 < u n ∧ 3*u n ≤ 2*u (n+1))
    (advance : ∀ n, (∀ j ≤ n+5, 0 ≤ u j) → 2*u (n+5) - ∑ j ∈ range (n+1), u j ≤ u (n+6)) :
    ∀ n, 0 < u n ∧ 3*u n ≤ 2*u (n+1) := by
  suffices inv : ∀ n, (0 < u n ∧ 3*u n ≤ 2*u (n+1)) ∧ ∑ j ∈ range (n+1), u j ≤ 3*u n from
    fun n => (inv n).1
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have pos : 0 < u n := by
      cases n with
      | zero => exact (start 0 (by decide)).1
      | succ k =>
        obtain ⟨hp,hr⟩ := (ih k (by omega)).1
        linarith
    have next : 3*u n ≤ 2*u (n+1) := by
      by_cases hs : n ≤ 5
      · exact (start n hs).2
      · obtain ⟨k,rfl⟩ : ∃ k, n=k+5 := ⟨n-5,by omega⟩
        have h := advance k (by
          intro j hj
          rcases lt_or_eq_of_le hj with hj|rfl
          · exact (ih j hj).1.1.le
          · exact pos.le)
        have s := (ih k (by omega)).2
        linarith [(ih k (by omega)).1.2,(ih (k+1) (by omega)).1.2,(ih (k+2) (by omega)).1.2,
                  (ih (k+3) (by omega)).1.2,(ih (k+4) (by omega)).1.2,(ih k (by omega)).1.1]
    refine ⟨⟨pos,next⟩,?_⟩
    cases n with
    | zero => simp; linarith
    | succ k =>
      rw [sum_range_succ]
      linarith [(ih k (by omega)).2,(ih k (by omega)).1.2]


theorem growth : ∀ n, 0 < seq n ∧ 3*seq n ≤ 2*seq (n+1) := by
  apply growth_induction seq _ filtered_lower
  intro n hn
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := seq_prefix
  have cases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 := by omega
  rcases cases with h|h|h|h|h|h <;> subst n <;> norm_num [h0,h1,h2,h3,h4,h5,h6]


theorem tail (n : ℕ) : seq (n+1) < seq (n+2) := by
  obtain ⟨hp,hr⟩ := growth (n+1)
  linarith

end Discovery

theorem OMA.solution : type_of% @OMA.S_oeis_a288229.main := by
  apply strictMono_nat_of_lt_succ
  intro n
  change Discovery.seq n < Discovery.seq (n+1)
  obtain ⟨hp,hr⟩ := Discovery.growth n
  linarith
