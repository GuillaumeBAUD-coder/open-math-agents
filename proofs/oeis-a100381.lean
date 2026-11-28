import OMAStatements.S_oeis_a100381
import Mathlib

namespace OMA.P100381

open OMA.S_oeis_a100381 Finset

/-- `c j = 1 / a(j+2)`. -/
noncomputable def c (j : ℕ) : ℝ := 1 / (2 ^ (j + 1) * ((j : ℝ) + 1) * ((j : ℝ) + 2))

lemma c_pos (j : ℕ) : 0 < c j := by unfold c; positivity

lemma a_cast (j : ℕ) : (1 : ℝ) / (a (j + 2) : ℝ) = c j := by
  unfold a c
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_choose_two]
  push_cast
  congr 1
  rw [pow_succ]
  ring

lemma c_succ (j : ℕ) : 2 * ((j : ℝ) + 3) * c (j + 1) = ((j : ℝ) + 1) * c j := by
  unfold c
  push_cast
  rw [pow_succ 2 (j + 1)]
  field_simp
  ring

lemma c_zero : c 0 = 1 / 4 := by unfold c; norm_num

lemma c_half (j : ℕ) : c (j + 1) < c j / 2 := by
  have h := c_succ j
  have hp := c_pos j
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  by_contra hcon
  rw [not_lt] at hcon
  have h2 := mul_le_mul_of_nonneg_left hcon (by linarith : (0 : ℝ) ≤ 2 * ((j : ℝ) + 3))
  nlinarith

/-- Partial sums of `c` starting at index `j`. -/
noncomputable def s (j m : ℕ) : ℝ := ∑ i ∈ range (m + 1), c (j + i)

lemma s_zero (j : ℕ) : s j 0 = c j := by simp [s]

lemma s_succ (j m : ℕ) : s j (m + 1) = c j + s (j + 1) m := by
  unfold s
  rw [Finset.sum_range_succ']
  simp only [add_zero]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  omega

lemma s_pos (j m : ℕ) : 0 < s j m :=
  Finset.sum_pos (fun i _ => c_pos _) ⟨0, by simp⟩

lemma K_eq : ∀ (m j : ℕ), K j m = (j : ℝ) + 2 * ((j : ℝ) + 2) * c j / s j m := by
  intro m
  induction m with
  | zero =>
    intro j
    rw [K, s_zero]
    have := c_pos j
    field_simp
    ring
  | succ m ih =>
    intro j
    rw [K, ih (j + 1), s_succ]
    have hx := c_pos j
    have hy := s_pos (j + 1) m
    have hc := c_succ j
    push_cast
    have h3 : 2 * ((j : ℝ) + 1 + 2) * c (j + 1) = ((j : ℝ) + 1) * c j := by rw [← hc]; ring
    rw [h3]
    have hne : ((j : ℝ) + 1) + ((j : ℝ) + 1) * c j / s (j + 1) m ≠ 0 := by positivity
    have hne2 : c j + s (j + 1) m ≠ 0 := by positivity
    field_simp
    ring

lemma invK (n : ℕ) : 1 / K 0 n = s 0 n := by
  rw [K_eq n 0, c_zero]
  have hs := s_pos 0 n
  simp only [Nat.cast_zero, zero_add]
  field_simp
  ring

lemma sumK (n : ℕ) : ∑ k ∈ Icc 2 (n + 2), (1 : ℝ) / (a k : ℝ) = 1 / K 0 n := by
  have hI : Icc 2 (n + 2) = Ico 2 (n + 3) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [invK, hI, Finset.sum_Ico_eq_sum_range]
  unfold s
  have e : n + 3 - 2 = n + 1 := by omega
  rw [e]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show 2 + i = i + 2 by omega, a_cast, zero_add]

/-- Alternating partial sums of `c` starting at index `j`. -/
noncomputable def W (j m : ℕ) : ℝ := ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * c (j + i)

lemma W_zero (j : ℕ) : W j 0 = c j := by simp [W]

lemma W_succ (j m : ℕ) : W j (m + 1) = c j - W (j + 1) m := by
  unfold W
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, add_zero]
  rw [add_comm, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pow_succ, show j + (i + 1) = j + 1 + i by omega]
  ring

lemma W_bounds : ∀ (m j : ℕ), c j / 2 < W j m ∧ W j m ≤ c j := by
  intro m
  induction m with
  | zero =>
    intro j
    rw [W_zero]
    have := c_pos j
    constructor <;> linarith
  | succ m ih =>
    intro j
    rw [W_succ]
    obtain ⟨h1, h2⟩ := ih (j + 1)
    have := c_half j
    have := c_pos (j + 1)
    constructor <;> linarith

lemma L_eq : ∀ (m j : ℕ), L j m = -(j : ℝ) + 2 * ((j : ℝ) + 2) * c j / W j m := by
  intro m
  induction m with
  | zero =>
    intro j
    rw [L, W_zero]
    have := c_pos j
    field_simp
    ring
  | succ m ih =>
    intro j
    rw [L, ih (j + 1), W_succ]
    have hx := c_pos j
    obtain ⟨hw1, hw2⟩ := W_bounds m (j + 1)
    have hh := c_half j
    have hq := c_pos (j + 1)
    have hc := c_succ j
    push_cast
    have h3 : 2 * ((j : ℝ) + 1 + 2) * c (j + 1) = ((j : ℝ) + 1) * c j := by rw [← hc]; ring
    rw [h3]
    have hw : 0 < W (j + 1) m := by linarith
    have hd : 0 < c j - W (j + 1) m := by linarith
    have hw' := hw.ne'
    have hd' := hd.ne'
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hrw : -((j : ℝ) + 1) + ((j : ℝ) + 1) * c j / W (j + 1) m
        = ((j : ℝ) + 1) * (c j - W (j + 1) m) / W (j + 1) m := by
      field_simp
      ring
    rw [hrw]
    field_simp
    ring

lemma invL (n : ℕ) : 1 / L 0 n = W 0 n := by
  rw [L_eq n 0, c_zero]
  obtain ⟨h1, h2⟩ := W_bounds n 0
  have hc := c_pos 0
  have hs : 0 < W 0 n := by linarith
  simp only [Nat.cast_zero, zero_add, neg_zero]
  field_simp
  ring

lemma sumL (n : ℕ) : ∑ k ∈ Icc 2 (n + 2), (-1 : ℝ) ^ k / (a k : ℝ) = 1 / L 0 n := by
  have hI : Icc 2 (n + 2) = Ico 2 (n + 3) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [invL, hI, Finset.sum_Ico_eq_sum_range]
  unfold W
  have e : n + 3 - 2 = n + 1 := by omega
  rw [e]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show 2 + i = i + 2 by omega, div_eq_mul_one_div, a_cast, zero_add, pow_add]
  norm_num

lemma hasSum_c : HasSum c (1 - Real.log 2) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := 1 / 2) (by rw [abs_of_pos] <;> norm_num)
  have hl : -Real.log (1 - 1 / 2) = Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv, neg_neg]
  rw [hl] at h
  have h2 := (hasSum_nat_add_iff' 1).2 h
  have h3 := h.sub (h2.mul_left 2)
  have hv : Real.log 2 - 2 * (Real.log 2 - ∑ i ∈ range 1, (1 / 2 : ℝ) ^ (i + 1) / ((i : ℝ) + 1))
      = 1 - Real.log 2 := by
    simp
    ring
  rw [hv] at h3
  have hfun : c = fun b : ℕ => (1 / 2 : ℝ) ^ (b + 1) / ((b : ℝ) + 1)
      - 2 * ((1 / 2 : ℝ) ^ (b + 1 + 1) / (((b + 1 : ℕ) : ℝ) + 1)) := by
    funext k
    unfold c
    push_cast
    rw [pow_succ (1 / 2 : ℝ) (k + 1), one_div_pow]
    field_simp
    ring
  rw [hfun]
  exact h3

lemma hasSum_alt : HasSum (fun k : ℕ => (-1 : ℝ) ^ k * c k) (3 * Real.log (3 / 2) - 1) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := -(1 / 2))
    (by rw [abs_neg, abs_of_pos] <;> norm_num)
  have hl : -Real.log (1 - -(1 / 2)) = -Real.log (3 / 2) := by norm_num
  rw [hl] at h
  have h2 := (hasSum_nat_add_iff' 1).2 h
  have h3 := h.neg.sub (h2.mul_left 2)
  have hv : - -Real.log (3 / 2) - 2 * (-Real.log (3 / 2)
      - ∑ i ∈ range 1, (-(1 / 2) : ℝ) ^ (i + 1) / ((i : ℝ) + 1)) = 3 * Real.log (3 / 2) - 1 := by
    simp
    ring
  rw [hv] at h3
  have hfun : (fun k : ℕ => (-1 : ℝ) ^ k * c k) = fun b : ℕ => -((-(1 / 2) : ℝ) ^ (b + 1) / ((b : ℝ) + 1))
      - 2 * ((-(1 / 2) : ℝ) ^ (b + 1 + 1) / (((b + 1 : ℕ) : ℝ) + 1)) := by
    funext k
    unfold c
    push_cast
    have e1 : (-(1 / 2) : ℝ) ^ (k + 1) = -((-1 : ℝ) ^ k / 2 ^ (k + 1)) := by
      rw [neg_pow, one_div_pow, pow_succ (-1 : ℝ) k]
      ring
    have e2 : (-(1 / 2) : ℝ) ^ (k + 1 + 1) = (-1 : ℝ) ^ k / (2 ^ (k + 1) * 2) := by
      rw [neg_pow, one_div_pow, pow_succ (-1 : ℝ) (k + 1), pow_succ (-1 : ℝ) k, pow_succ (2 : ℝ) (k + 1)]
      ring
    rw [e1, e2]
    field_simp
    ring
  rw [hfun]
  exact h3

end OMA.P100381

theorem OMA.solution : type_of% @OMA.S_oeis_a100381.main := by
  refine ⟨OMA.P100381.sumK, OMA.P100381.sumL, ?_, ?_, ?_, ?_⟩
  · have h := OMA.P100381.hasSum_c
    convert h using 1
    ext k
    exact OMA.P100381.a_cast k
  · have ht := OMA.P100381.hasSum_c.tendsto_sum_nat
    have ht' := ht.comp (Filter.tendsto_add_atTop_nat 1)
    refine ht'.congr (fun n => ?_)
    rw [OMA.P100381.invK]
    simp [OMA.P100381.s]
  · have h := OMA.P100381.hasSum_alt
    convert h using 1
    ext k
    rw [div_eq_mul_one_div, OMA.P100381.a_cast, pow_add]
    norm_num
  · have ht := OMA.P100381.hasSum_alt.tendsto_sum_nat
    have ht' := ht.comp (Filter.tendsto_add_atTop_nat 1)
    refine ht'.congr (fun n => ?_)
    rw [OMA.P100381.invL]
    simp [OMA.P100381.W]
