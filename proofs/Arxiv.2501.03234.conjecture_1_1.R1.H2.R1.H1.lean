import OMAReductions.R_Arxiv_2501_03234_conjecture_1_1_R1_H2_R1
import Mathlib

/-! Block estimate: the odd harmonic sum over [0, L(m+1)) is at most the sum over [0, L) plus the
sum over [0, m), since the block [L j, L j + L) contributes at most L/(2 L j + 1) <= 1/(2 j - 1).
With m = L - 1 and monotonicity this gives the bound for every n <= L^2. -/

open Finset

theorem OMA.solution : OMA.R_Arxiv_2501_03234_conjecture_1_1_R1_H2_R1.H1 := by
  intro n L _ hnL
  -- block estimate: O(L*(m+1)) ≤ O(L) + O(m)
  have block : ∀ m : ℕ, ∑ k ∈ range (L * (m + 1)), (1 : ℚ)/(2*k+1) ≤
      ∑ k ∈ range L, (1 : ℚ)/(2*k+1) + ∑ k ∈ range m, (1 : ℚ)/(2*k+1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have e : L * (m + 1 + 1) = L * (m + 1) + L := by ring
      rw [e, Finset.sum_range_add, Finset.sum_range_succ]
      have hterm : ∀ i ∈ range L, (1 : ℚ) / (2 * ((L * (m + 1) + i : ℕ) : ℚ) + 1) ≤
          1 / (2 * ((L * (m + 1) : ℕ) : ℚ) + 1) := by
        intro i _
        apply one_div_le_one_div_of_le (by positivity)
        push_cast
        have : (0 : ℚ) ≤ i := by positivity
        linarith
      have hsum : ∑ i ∈ range L, (1 : ℚ) / (2 * ((L * (m + 1) + i : ℕ) : ℚ) + 1) ≤
          L * (1 / (2 * ((L * (m + 1) : ℕ) : ℚ) + 1)) := by
        calc _ ≤ ∑ i ∈ range L, (1 / (2 * ((L * (m + 1) : ℕ) : ℚ) + 1)) := Finset.sum_le_sum hterm
          _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hcmp : (L : ℚ) * (1 / (2 * ((L * (m + 1) : ℕ) : ℚ) + 1)) ≤ 1 / (2 * (m : ℚ) + 1) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        push_cast
        have : (0 : ℚ) ≤ L := by positivity
        nlinarith
      push_cast at hsum hcmp ⊢
      linarith
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    have : n = 0 := by simpa using hnL
    subst this
    simp
  · have hmono : ∑ k ∈ range n, (1 : ℚ)/(2*k+1) ≤ ∑ k ∈ range (L * (L - 1 + 1)), (1 : ℚ)/(2*k+1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · apply Finset.range_mono
        have : L * (L - 1 + 1) = L ^ 2 := by rw [Nat.sub_add_cancel hL]; ring
        omega
      · intro i _ _; positivity
    have hsub : ∑ k ∈ range (L - 1), (1 : ℚ)/(2*k+1) ≤ ∑ k ∈ range L, (1 : ℚ)/(2*k+1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (Nat.sub_le L 1)
      · intro i _ _; positivity
    have := block (L - 1)
    linarith
