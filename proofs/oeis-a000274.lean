import OMAStatements.S_oeis_a000274
import Mathlib.Combinatorics.Derangements.Exponential

/-!
Mathar's factorial-floor formula, proved by Sela Fried in Corollary 3 of
On sequence A000274 in the OEIS (https://oeis.org/A000274/a000274.pdf).
The normalized derangement counts tend to 1/e. Their even and odd subsequences
approach the limit from opposite sides, which identifies the two floors.
-/

open Filter
open scoped Topology

namespace OMA.A000274

private noncomputable def ratio (n : ℕ) : ℝ := (numDerangements n : ℝ) / n.factorial

private theorem factorial_pos (n : ℕ) : 0 < (n.factorial : ℝ) := by positivity

private theorem ratio_step (n : ℕ) :
    ratio (n + 1) = ratio n - (-1 : ℝ) ^ n / (n + 1).factorial := by
  have hD : (numDerangements (n + 1) : ℝ) =
      ((n : ℝ) + 1) * (numDerangements n : ℝ) - (-1 : ℝ) ^ n := by
    exact_mod_cast numDerangements_succ n
  unfold ratio
  rw [hD, sub_div, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  congr 1
  field_simp [ne_of_gt (factorial_pos n), show (n : ℝ) + 1 ≠ 0 by positivity]

private noncomputable def gap (n : ℕ) : ℝ :=
  1 / ((n + 1).factorial : ℝ) - 1 / ((n + 2).factorial : ℝ)

private theorem gap_pos (n : ℕ) : 0 < gap n := by
  apply sub_pos.mpr (one_div_lt_one_div_of_lt (factorial_pos (n + 1)) ?_)
  exact_mod_cast Nat.factorial_lt_of_lt (show 0 < n + 1 by omega)
    (show n + 1 < n + 2 by omega)

private theorem ratio_two_steps (n : ℕ) :
    ratio (n + 2) = ratio n - (-1 : ℝ) ^ n * gap n := by
  rw [ratio_step (n + 1), ratio_step n, pow_succ, gap, div_eq_mul_inv, div_eq_mul_inv,
    one_div, one_div]
  ring

private theorem sign_shift (n j : ℕ) : (-1 : ℝ) ^ (n + 2 * j) = (-1 : ℝ) ^ n := by
  rw [pow_add, pow_mul]
  norm_num

private theorem signed_step (n : ℕ) :
    (-1 : ℝ) ^ n * ratio (n + 2) < (-1 : ℝ) ^ n * ratio n := by
  have hs : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have h := congrArg (fun t : ℝ => t * gap n) hs
  rw [ratio_two_steps]
  nlinarith only [h, gap_pos n]

private theorem signed_limit_le (n : ℕ) :
    (-1 : ℝ) ^ n * Real.exp (-1) ≤ (-1 : ℝ) ^ n * ratio n := by
  let f : ℕ → ℝ := fun k => (-1 : ℝ) ^ n * ratio (n + 2 * k)
  have ht : Tendsto (fun k : ℕ => n + 2 * k) atTop atTop :=
    tendsto_atTop_atTop.mpr fun a => ⟨a, by omega⟩
  have hl : Tendsto f atTop (𝓝 ((-1 : ℝ) ^ n * Real.exp (-1))) :=
    (numDerangements_tendsto_inv_e.comp ht).const_mul _
  have hf : Antitone f := by
    apply antitone_nat_of_succ_le
    intro k
    have hs := (signed_step (n + 2 * k)).le
    rw [sign_shift] at hs
    change (-1 : ℝ) ^ n * ratio (n + 2 * (k + 1)) ≤
      (-1 : ℝ) ^ n * ratio (n + 2 * k)
    rw [show n + 2 * (k + 1) = n + 2 * k + 2 by omega]
    exact hs
  have hle := le_of_tendsto' hl (fun k => hf (Nat.zero_le k))
  simpa [f] using hle

private theorem signed_limit_lt (n : ℕ) :
    (-1 : ℝ) ^ n * Real.exp (-1) < (-1 : ℝ) ^ n * ratio n := by
  have h := signed_limit_le (n + 2)
  rw [show n + 2 = n + 2 * 1 by omega, sign_shift] at h
  exact h.trans_lt (signed_step n)

private theorem scaled_ratio (n : ℕ) :
    ratio n * (n.factorial : ℝ) = (numDerangements n : ℝ) :=
  div_mul_cancel₀ _ (ne_of_gt (factorial_pos n))

private theorem scaled_next_ratio (n : ℕ) :
    ratio (n + 1) * (n.factorial : ℝ) =
      (numDerangements n : ℝ) - (-1 : ℝ) ^ n * ((n.factorial : ℝ) / (n + 1).factorial) := by
  rw [ratio_step, sub_mul, scaled_ratio]
  ring

private theorem scaled_floor (n : ℕ) :
    ⌊(n.factorial : ℝ) / Real.exp 1⌋ =
      (numDerangements n : ℤ) - (if Even n then 1 else 0) := by
  have hfac : (n.factorial : ℝ) / (n + 1).factorial ≤ 1 :=
    (div_le_one (factorial_pos (n + 1))).mpr (by exact_mod_cast Nat.factorial_le (Nat.le_succ n))
  have h := signed_limit_lt n
  have h' := signed_limit_lt (n + 1)
  have hp := factorial_pos n
  by_cases he : Even n
  · rw [he.neg_one_pow] at h
    rw [pow_succ, he.neg_one_pow] at h'
    simp only [one_mul] at h h'
    have hhi := mul_lt_mul_of_pos_right h hp
    have hlo := mul_lt_mul_of_pos_right (show ratio (n + 1) < Real.exp (-1) by linarith) hp
    rw [scaled_ratio] at hhi
    rw [scaled_next_ratio, he.neg_one_pow, one_mul] at hlo
    apply Int.floor_eq_iff.mpr
    rw [if_pos he]
    push_cast
    rw [div_eq_mul_inv, ← Real.exp_neg]
    constructor <;> linarith
  · have ho := Nat.not_even_iff_odd.mp he
    rw [ho.neg_one_pow] at h
    rw [pow_succ, ho.neg_one_pow] at h'
    norm_num at h'
    have hlo := mul_lt_mul_of_pos_right (show ratio n < Real.exp (-1) by linarith) hp
    have hhi := mul_lt_mul_of_pos_right h' hp
    rw [scaled_ratio] at hlo
    rw [scaled_next_ratio, ho.neg_one_pow, neg_one_mul, sub_neg_eq_add] at hhi
    apply Int.floor_eq_iff.mpr
    rw [if_neg he, sub_zero]
    push_cast
    rw [div_eq_mul_inv, ← Real.exp_neg]
    constructor <;> linarith

private theorem floor_difference (k : ℕ) :
    ⌊((k + 1).factorial : ℝ) / Real.exp 1⌋ - ⌊(k.factorial : ℝ) / Real.exp 1⌋ =
      (k : ℤ) * (numDerangements k : ℤ) := by
  rw [scaled_floor, scaled_floor, numDerangements_succ]
  by_cases he : Even k
  · have hn : ¬ Even (k + 1) := by simpa [Nat.even_add_one] using he
    rw [if_neg hn, if_pos he, he.neg_one_pow]
    ring
  · have hn : Even (k + 1) := Nat.even_add_one.mpr he
    rw [if_pos hn, if_neg he, (Nat.not_even_iff_odd.mp he).neg_one_pow]
    ring

end OMA.A000274

theorem OMA.solution : type_of% @OMA.S_oeis_a000274.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  unfold OMA.S_oeis_a000274.a
  rw [Nat.add_sub_cancel, OMA.A000274.floor_difference]
  push_cast
  rfl
