import OMAStatements.S_oeis_a306810
import Mathlib

namespace A306810Proof

open OMA.S_oeis_a306810

/-- The alternating binomial sum of the sequence b shifted by i. -/
def W (i n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1) ^ (n + k) * (n.choose k : ℤ) * (b (k + i) : ℤ)

lemma a_W (n : ℕ) : a n = W 0 n := by
  unfold a W
  simp

lemma W_succ (i n : ℕ) : W i (n + 1) = W (i + 1) n - W i n := by
  have hA : W i (n + 1)
      = (∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n + k) * (n.choose k : ℤ) * (b (k + 1 + i) : ℤ))
        + (∑ k ∈ Finset.range (n + 1),
            (-1 : ℤ) ^ (n + k) * (n.choose (k + 1) : ℤ) * (b (k + 1 + i) : ℤ))
        - (-1 : ℤ) ^ n * (b i : ℤ) := by
    unfold W
    rw [Finset.sum_range_succ', ← Finset.sum_add_distrib]
    have h0 : (-1 : ℤ) ^ (n + 1 + 0) * ((n + 1).choose 0 : ℤ) * (b (0 + i) : ℤ)
        = -((-1 : ℤ) ^ n * (b i : ℤ)) := by
      rw [Nat.choose_zero_right, Nat.zero_add, Nat.add_zero]
      push_cast
      ring
    rw [h0]
    have h1 : ∀ k ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ (n + 1 + (k + 1)) * ((n + 1).choose (k + 1) : ℤ) * (b (k + 1 + i) : ℤ)
          = (-1 : ℤ) ^ (n + k) * (n.choose k : ℤ) * (b (k + 1 + i) : ℤ)
            + (-1 : ℤ) ^ (n + k) * (n.choose (k + 1) : ℤ) * (b (k + 1 + i) : ℤ) := by
      intro k _
      rw [Nat.choose_succ_succ]
      push_cast
      ring
    rw [Finset.sum_congr rfl h1]
    ring
  have hB : W (i + 1) n
      = ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n + k) * (n.choose k : ℤ) * (b (k + 1 + i) : ℤ) := by
    unfold W
    apply Finset.sum_congr rfl
    intro k _
    rw [show k + (i + 1) = k + 1 + i by omega]
  have hC : (∑ k ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ (n + k) * (n.choose (k + 1) : ℤ) * (b (k + 1 + i) : ℤ))
      = ∑ k ∈ Finset.range n,
        (-1 : ℤ) ^ (n + k) * (n.choose (k + 1) : ℤ) * (b (k + 1 + i) : ℤ) := by
    rw [Finset.sum_range_succ, Nat.choose_succ_self]
    simp
  have hD : W i n
      = -(∑ k ∈ Finset.range n,
          (-1 : ℤ) ^ (n + k) * (n.choose (k + 1) : ℤ) * (b (k + 1 + i) : ℤ))
        + (-1 : ℤ) ^ n * (b i : ℤ) := by
    unfold W
    rw [Finset.sum_range_succ', ← Finset.sum_neg_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro k _
      ring
    · simp
  linarith [hA, hB, hC, hD]

lemma b_succ (k : ℕ) : b (k + 1) = if (k + 1) % 3 = 2 then 2 * (k + 2) / 3 else 1 := by
  rw [b]

lemma bid (k : ℕ) : (b (k + 7) : ℤ) - 2 * (b (k + 4) : ℤ) + (b (k + 1) : ℤ) = 0 := by
  have h1 := b_succ k
  have h4 := b_succ (k + 3)
  have h7 := b_succ (k + 6)
  have hN : b (k + 7) + b (k + 1) = 2 * b (k + 4) := by
    rw [show k + 7 = k + 6 + 1 from rfl, show k + 4 = k + 3 + 1 from rfl, h1, h4, h7]
    split_ifs <;> omega
  omega

lemma W_zero (m : ℕ) : W 7 m - 2 * W 4 m + W 1 m = 0 := by
  unfold W
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro k _
  have hb := bid k
  linear_combination ((-1 : ℤ) ^ (m + k) * (m.choose k : ℤ)) * hb

lemma main_rec (m : ℕ) :
    W 0 (m + 7) + 7 * W 0 (m + 6) + 21 * W 0 (m + 5) + 33 * W 0 (m + 4) + 27 * W 0 (m + 3)
      + 9 * W 0 (m + 2) = 0 := by
  have hz := W_zero m
  have h0_6 : W 0 (m + 7) = W 1 (m + 6) - W 0 (m + 6) := W_succ 0 (m + 6)
  have h0_5 : W 0 (m + 6) = W 1 (m + 5) - W 0 (m + 5) := W_succ 0 (m + 5)
  have h1_5 : W 1 (m + 6) = W 2 (m + 5) - W 1 (m + 5) := W_succ 1 (m + 5)
  have h0_4 : W 0 (m + 5) = W 1 (m + 4) - W 0 (m + 4) := W_succ 0 (m + 4)
  have h1_4 : W 1 (m + 5) = W 2 (m + 4) - W 1 (m + 4) := W_succ 1 (m + 4)
  have h2_4 : W 2 (m + 5) = W 3 (m + 4) - W 2 (m + 4) := W_succ 2 (m + 4)
  have h0_3 : W 0 (m + 4) = W 1 (m + 3) - W 0 (m + 3) := W_succ 0 (m + 3)
  have h1_3 : W 1 (m + 4) = W 2 (m + 3) - W 1 (m + 3) := W_succ 1 (m + 3)
  have h2_3 : W 2 (m + 4) = W 3 (m + 3) - W 2 (m + 3) := W_succ 2 (m + 3)
  have h3_3 : W 3 (m + 4) = W 4 (m + 3) - W 3 (m + 3) := W_succ 3 (m + 3)
  have h0_2 : W 0 (m + 3) = W 1 (m + 2) - W 0 (m + 2) := W_succ 0 (m + 2)
  have h1_2 : W 1 (m + 3) = W 2 (m + 2) - W 1 (m + 2) := W_succ 1 (m + 2)
  have h2_2 : W 2 (m + 3) = W 3 (m + 2) - W 2 (m + 2) := W_succ 2 (m + 2)
  have h3_2 : W 3 (m + 3) = W 4 (m + 2) - W 3 (m + 2) := W_succ 3 (m + 2)
  have h4_2 : W 4 (m + 3) = W 5 (m + 2) - W 4 (m + 2) := W_succ 4 (m + 2)
  have h1_1 : W 1 (m + 2) = W 2 (m + 1) - W 1 (m + 1) := W_succ 1 (m + 1)
  have h2_1 : W 2 (m + 2) = W 3 (m + 1) - W 2 (m + 1) := W_succ 2 (m + 1)
  have h3_1 : W 3 (m + 2) = W 4 (m + 1) - W 3 (m + 1) := W_succ 3 (m + 1)
  have h4_1 : W 4 (m + 2) = W 5 (m + 1) - W 4 (m + 1) := W_succ 4 (m + 1)
  have h5_1 : W 5 (m + 2) = W 6 (m + 1) - W 5 (m + 1) := W_succ 5 (m + 1)
  have h1_0 : W 1 (m + 1) = W 2 m - W 1 m := W_succ 1 m
  have h2_0 : W 2 (m + 1) = W 3 m - W 2 m := W_succ 2 m
  have h3_0 : W 3 (m + 1) = W 4 m - W 3 m := W_succ 3 m
  have h4_0 : W 4 (m + 1) = W 5 m - W 4 m := W_succ 4 m
  have h5_0 : W 5 (m + 1) = W 6 m - W 5 m := W_succ 5 m
  have h6_0 : W 6 (m + 1) = W 7 m - W 6 m := W_succ 6 m
  linear_combination (1) * h0_6 + (6) * h0_5 + (1) * h1_5 + (15) * h0_4 + (5) * h1_4 + (1) * h2_4 + (18) * h0_3 + (10) * h1_3 + (4) * h2_3 + (1) * h3_3 + (9) * h0_2 + (8) * h1_2 + (6) * h2_2 + (3) * h3_2 + (1) * h4_2 + (1) * h1_1 + (2) * h2_1 + (3) * h3_1 + (2) * h4_1 + (1) * h5_1 + (-1) * h1_0 + (-1) * h2_0 + (-1) * h3_0 + (1) * h4_0 + (1) * h5_0 + (1) * h6_0 + hz

end A306810Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a306810.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  have e1 : m + 7 - 1 = m + 6 := by omega
  have e2 : m + 7 - 2 = m + 5 := by omega
  have e3 : m + 7 - 3 = m + 4 := by omega
  have e4 : m + 7 - 4 = m + 3 := by omega
  have e5 : m + 7 - 5 = m + 2 := by omega
  rw [e1, e2, e3, e4, e5]
  simp only [A306810Proof.a_W]
  have key := A306810Proof.main_rec m
  linarith
