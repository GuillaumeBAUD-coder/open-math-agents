import OMAStatements.S_mo_249619
import Mathlib

namespace MO249619Proof
open Set Filter Topology

lemma bump_zero_of_one_le (x : ℝ) (hx : 1 ≤ |x|) : OMA.S_mo_249619.bump x = 0 := by
  unfold OMA.S_mo_249619.bump
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    rcases le_abs.mp hx with h3 | h3
    · have hx1 : x = 1 := le_antisymm h2 h3
      rw [hx1, mul_one]
      exact Real.cos_pi_div_two
    · have hx1 : x = -1 := by linarith
      have h4 : Real.pi * (-1) / 2 = -(Real.pi / 2) := by ring
      rw [hx1, h4, Real.cos_neg, Real.cos_pi_div_two]
  · rfl

def kseq (c : ℕ → ℤ) : ℕ → ℤ
  | 0 => c 0
  | n + 1 => max (kseq c n + 1) (c (n + 1))

lemma kseq_strictMono (c : ℕ → ℤ) : StrictMono (kseq c) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [kseq]
  exact lt_of_lt_of_le (lt_add_one _) (le_max_left _ _)

lemma le_kseq (c : ℕ → ℤ) (n : ℕ) : c n ≤ kseq c n := by
  cases n with
  | zero => rw [kseq]
  | succ n => rw [kseq]; exact le_max_right _ _

lemma exists_seq (y : ℝ) (x : ℕ → ℝ) (hx : ∀ n, y ≠ x n) :
    ∃ k : ℕ → ℤ, StrictMono k ∧ ∀ n, OMA.S_mo_249619.bump ((k n : ℝ) * (y - x n)) = 0 := by
  refine ⟨kseq (fun n => ⌈1 / |y - x n|⌉), kseq_strictMono _, fun n => ?_⟩
  apply bump_zero_of_one_le
  have hd : 0 < |y - x n| := abs_pos.mpr (sub_ne_zero.mpr (hx n))
  have h1 : 1 / |y - x n| ≤ ((⌈1 / |y - x n|⌉ : ℤ) : ℝ) := Int.le_ceil _
  have h2 : ((⌈1 / |y - x n|⌉ : ℤ) : ℝ) ≤ (kseq (fun n => ⌈1 / |y - x n|⌉) n : ℝ) := by
    exact_mod_cast le_kseq (fun n => ⌈1 / |y - x n|⌉) n
  rw [abs_mul]
  have h4 : 1 / |y - x n| ≤ |(kseq (fun n => ⌈1 / |y - x n|⌉) n : ℝ)| :=
    le_trans (le_trans h1 h2) (le_abs_self _)
  calc (1 : ℝ) = (1 / |y - x n|) * |y - x n| := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right h4 hd.le

lemma exists_irr : ∃ y : ℝ, 0 ≤ y ∧ y ≤ 1 ∧ ∀ q : ℚ, y ≠ (q : ℝ) := by
  have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num
  have hs2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_iff]; norm_num
  refine ⟨Real.sqrt 2 - 1, by linarith, by linarith, ?_⟩
  intro q hq
  apply irrational_sqrt_two
  refine ⟨q + 1, ?_⟩
  push_cast
  linarith

end MO249619Proof

theorem OMA.solution : type_of% @OMA.S_mo_249619.main := by
  intro r
  obtain ⟨y, hy0, hy1, hirr⟩ := MO249619Proof.exists_irr
  obtain ⟨k, hk, hz⟩ :=
    MO249619Proof.exists_seq y (fun n => (((r n).val : ℚ) : ℝ)) (fun n => hirr _)
  refine ⟨k, hk, y, ⟨hy0, hy1⟩, ?_⟩
  have hfun : (fun n => OMA.S_mo_249619.bump (k n * (y - ((r n).val : ℝ)))) = fun _ => 0 :=
    funext hz
  rw [hfun]
  exact tendsto_const_nhds
