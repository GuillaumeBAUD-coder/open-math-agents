import OMAStatements.S_oeis_a002467
import Mathlib

namespace A002467aux

lemma D_real (n : ℕ) : (numDerangements n : ℝ) =
    (n.factorial : ℝ) * ∑ m ∈ Finset.range (n + 1), (-1 : ℝ) ^ m / (m.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h := numDerangements_succ k
    have h' : (numDerangements (k + 1) : ℝ)
        = ((k : ℝ) + 1) * (numDerangements k : ℝ) - (-1) ^ k := by
      exact_mod_cast h
    rw [h', ih, Finset.sum_range_succ _ (k + 1), Nat.factorial_succ]
    push_cast
    have hk : (k.factorial : ℝ) ≠ 0 := by positivity
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring

lemma tail_bound (n : ℕ) :
    |Real.exp (-1) - ∑ m ∈ Finset.range (n + 1), (-1 : ℝ) ^ m / (m.factorial : ℝ)|
      ≤ ((n : ℝ) + 2) / (((n + 1).factorial : ℝ) * ((n : ℝ) + 1)) := by
  have hb := Real.exp_bound (x := -1) (by norm_num) (n := n + 1) (by omega)
  refine hb.trans (le_of_eq ?_)
  rw [abs_neg, abs_one, one_pow, one_mul]
  push_cast
  ring

lemma near (n : ℕ) (hn : 2 ≤ n) :
    |(n.factorial : ℝ) * Real.exp (-1) - (numDerangements n : ℝ)| < 1 / 2 := by
  have hpos : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  rw [D_real, ← mul_sub, abs_mul, abs_of_pos hpos]
  have h1 := mul_le_mul_of_nonneg_left (tail_bound n) hpos.le
  have h2 : (n.factorial : ℝ) * (((n : ℝ) + 2) / (((n + 1).factorial : ℝ) * ((n : ℝ) + 1)))
      = ((n : ℝ) + 2) / (((n : ℝ) + 1) * ((n : ℝ) + 1)) := by
    rw [Nat.factorial_succ]
    push_cast
    have hk1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  have h3 : ((n : ℝ) + 2) / (((n : ℝ) + 1) * ((n : ℝ) + 1)) < 1 / 2 := by
    have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

end A002467aux

theorem OMA.solution : type_of% @OMA.S_oeis_a002467.main := by
  intro n hn
  unfold OMA.S_oeis_a002467.a
  have he : (2 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have hu0 : 0 < 1 / Real.exp 1 := by positivity
  have hu : 1 / Real.exp 1 < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) he
  have hexp : Real.exp (-1) = 1 / Real.exp 1 := by rw [Real.exp_neg, one_div]
  symm
  rw [round_eq_iff]
  by_cases h1 : n = 1
  · subst h1
    rw [Nat.factorial_one, numDerangements_one]
    generalize 1 / Real.exp 1 = u at hu0 hu
    constructor
    · norm_num
      linarith
    · norm_num
      linarith
  · have hk := A002467aux.near n (by omega)
    rw [abs_lt, hexp] at hk
    have hf : (1 : ℝ) ≤ (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    generalize 1 / Real.exp 1 = u at hu0 hu hk
    have hprod : (n.factorial : ℝ) * u ≤ (n.factorial : ℝ) * (1 / 2) :=
      mul_le_mul_of_nonneg_left hu.le (by linarith)
    have hD : numDerangements n ≤ n.factorial := by
      have h2 : (numDerangements n : ℝ) < (n.factorial : ℝ) + 1 := by linarith [hk.1]
      have h3 : numDerangements n < n.factorial + 1 := by exact_mod_cast h2
      omega
    rw [Nat.cast_sub hD]
    have e : (1 - u) * (n.factorial : ℝ) = (n.factorial : ℝ) - (n.factorial : ℝ) * u := by ring
    rw [e]
    push_cast
    constructor
    · linarith [hk.2]
    · linarith [hk.1]
