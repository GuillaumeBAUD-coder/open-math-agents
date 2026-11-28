import OMAStatements.S_oeis_a029576
import Mathlib

namespace OMA.S_oeis_a029576

lemma hS (k : ℕ) : S k = 9 ^ k * (k.factorial : ℚ) *
    (1 - ∑ j ∈ Finset.range (k + 1), (-1 : ℚ) ^ j / (9 ^ j * (j.factorial : ℚ))) := by
  induction k with
  | zero => simp [S]
  | succ k ih =>
    rw [S, ih, Finset.sum_range_succ _ (k + 1), Nat.factorial_succ]
    push_cast
    field_simp
    ring

lemma Spos (k : ℕ) : 1 ≤ S (k + 1) := by
  induction k with
  | zero => norm_num [S]
  | succ k ih =>
    rw [S]
    have h1 : ((k : ℚ) + 1 + 1) ≥ 1 := by linarith [(Nat.cast_nonneg k : (0:ℚ) ≤ k)]
    have : (-1 : ℚ) ^ (k + 1 + 1) ≤ 1 := by
      rcases neg_one_pow_eq_or ℚ (k + 1 + 1) with h | h <;> rw [h] <;> norm_num
    push_cast
    nlinarith [this]

theorem sol : type_of% @main := by
  constructor
  · intro n hn hm
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h : (m + 1) / 9 = m / 9 := by omega
    simp only [a, Nat.add_sub_cancel, h, Nat.factorial_succ]
    push_cast
    ring
  · intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have e1 : 9 * (j + 2) / 9 = j + 2 := by omega
    have e2 : (9 * (j + 2) - 1) / 9 = j + 1 := by omega
    have e3 : j + 2 - 1 = j + 1 := by omega
    have hpos := Spos j
    have hj := hS (j + 1)
    have hj2 := hS (j + 2)
    have hne : (1 - ∑ i ∈ Finset.range (j + 1 + 1), (-1 : ℚ) ^ i / (9 ^ i * (i.factorial : ℚ))) ≠ 0 := by
      intro h0
      rw [h0] at hj
      simp at hj
      linarith
    have hfac : (9 * (j + 2)).factorial = (9 * (j + 2)) * (9 * (j + 2) - 1).factorial := by
      have : 9 * (j + 2) = (9 * (j + 2) - 1) + 1 := by omega
      conv_lhs => rw [this, Nat.factorial_succ]
      rw [← this]
    simp only [a, e1, e2, e3]
    rw [hj2, hj, hfac]
    have h9 : (9 * (j + 2) - 1 + 1 : ℕ) = 9 * (j + 2) := by omega
    have hc : ((9 * (j + 2) - 1 : ℕ) : ℚ) + 1 = 9 * ((j : ℚ) + 2) := by
      have : ((9 * (j + 2) - 1 : ℕ) : ℚ) + 1 = ((9 * (j + 2) - 1 + 1 : ℕ) : ℚ) := by push_cast; ring
      rw [this, h9]; push_cast; ring
    have hf : ((j + 2).factorial : ℚ) = ((j : ℚ) + 2) * ((j + 1).factorial : ℚ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hf]
    have h9ne : (9 : ℚ) ^ (j + 1) * ((j + 1).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
end OMA.S_oeis_a029576

theorem OMA.solution : type_of% @OMA.S_oeis_a029576.main := OMA.S_oeis_a029576.sol
