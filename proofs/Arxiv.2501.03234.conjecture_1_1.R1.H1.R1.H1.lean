import OMAReductions.R_Arxiv_2501_03234_conjecture_1_1_R1_H1_R1
import Mathlib

-- Step Arxiv.2501.03234.conjecture_1_1.R1.H1.R1.H1: hypothesis H1 of reduction Arxiv.2501.03234.conjecture_1_1.R1.H1.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Kronecker substitution. P = A^2 R = Σ_e c_e B^e where c_e counts the triples (i, j, k) with
i + j + (n - 1 - k) = e, weighted by w i w j w k. Since n^2 < B each c_e is a base-B digit, so
(P / B^m) % B = c_m. The digits at m = n - 1 (where k = i + j) and m = 2n - 1 (where k = i + j - n)
add up to the wrapped sum. -/

open Finset

namespace Arxiv250103234StepH1

lemma split_sum (B L : ℕ) (c : ℕ → ℕ) :
    ∑ e ∈ range (L + 1), c e * B ^ e = c 0 + B * ∑ e ∈ range L, c (e + 1) * B ^ e := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, mul_one, pow_succ]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma digit (B : ℕ) (hB : 0 < B) : ∀ (m L : ℕ) (c : ℕ → ℕ), (∀ e, c e < B) →
    ((∑ e ∈ range L, c e * B ^ e) / B ^ m) % B = if m < L then c m else 0 := by
  intro m
  induction m with
  | zero =>
    intro L c hc
    rcases L with _ | L
    · simp
    · rw [split_sum, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hc 0)]
      simp
  | succ m ih =>
    intro L c hc
    rcases L with _ | L
    · simp
    · rw [split_sum, pow_succ, mul_comm (B ^ m) B, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (hc 0), zero_add]
      rw [ih L (fun e => c (e + 1)) (fun e => hc (e + 1))]
      simp only [Nat.add_lt_add_iff_right]

theorem main : ∀ (n B : ℕ) (w : ℕ → ℕ), 0<n → n^2<B → (∀ i<n, w i≤1) →
    let A := ∑ i ∈ range n, w i * B^i
    let R := ∑ i ∈ range n, w i * B^(n-1-i)
    let P := A^2 * R
    (∑ i ∈ range n, ∑ j ∈ range n, w i*w j*w ((i+j)%n)) = (P/B^(n-1))%B + (P/B^(2*n-1))%B := by
  intro n B w hn hB hw A R P
  have hB0 : 0 < B := lt_of_le_of_lt (Nat.zero_le _) hB
  let f : ℕ → ℕ → ℕ → ℕ := fun i j k => i + j + (n - 1 - k)
  let c : ℕ → ℕ := fun e => ∑ i ∈ range n, ∑ j ∈ range n, ∑ k ∈ range n,
    if f i j k = e then w i * w j * w k else 0
  -- P as a triple sum
  have hP : P = ∑ i ∈ range n, ∑ j ∈ range n, ∑ k ∈ range n, w i * w j * w k * B ^ f i j k := by
    simp only [P, A, R, sq]
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    simp only [f]; rw [pow_add, pow_add]; ring
  have hPc : P = ∑ e ∈ range (3 * n), c e * B ^ e := by
    rw [hP]
    simp only [c, Finset.sum_mul, ite_mul, zero_mul]
    symm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j hj
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k hk
    rw [Finset.sum_ite_eq]
    rw [if_pos]
    simp only [mem_range] at hi hj hk ⊢
    simp only [f]; omega
  have hc : ∀ e, c e < B := by
    intro e
    have h1 : ∀ i ∈ range n, ∀ j ∈ range n, (∑ k ∈ range n, if f i j k = e then w i * w j * w k else 0) ≤ 1 := by
      intro i hi j hj
      calc (∑ k ∈ range n, if f i j k = e then w i * w j * w k else 0)
          ≤ ∑ k ∈ range n, if f i j k = e then 1 else 0 := by
            apply Finset.sum_le_sum; intro k hk
            split_ifs
            · have := hw i (mem_range.mp hi); have := hw j (mem_range.mp hj)
              have := hw k (mem_range.mp hk)
              calc w i * w j * w k ≤ 1 * 1 * 1 := by gcongr
                _ = 1 := by norm_num
            · exact le_rfl
        _ = ((range n).filter (fun k => f i j k = e)).card := by
            rw [Finset.card_filter]
        _ ≤ 1 := by
            apply Finset.card_le_one.mpr
            intro a ha b hb
            simp only [mem_filter, mem_range, f] at ha hb
            omega
    calc c e ≤ ∑ i ∈ range n, ∑ j ∈ range n, 1 := by
          apply Finset.sum_le_sum; intro i hi; apply Finset.sum_le_sum; intro j hj; exact h1 i hi j hj
      _ = n ^ 2 := by simp [sq]
      _ < B := hB
  have hd1 : (P / B ^ (n - 1)) % B = c (n - 1) := by
    rw [hPc, digit B hB0 _ _ c hc, if_pos (by omega)]
  have hd2 : (P / B ^ (2 * n - 1)) % B = c (2 * n - 1) := by
    rw [hPc, digit B hB0 _ _ c hc, if_pos (by omega)]
  rw [hd1, hd2]
  simp only [c, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  simp only [mem_range] at hi hj
  by_cases hij : i + j < n
  · have hmod : (i + j) % n = i + j := Nat.mod_eq_of_lt hij
    rw [hmod]
    have s1 : (∑ k ∈ range n, if f i j k = n - 1 then w i * w j * w k else 0) = w i * w j * w (i + j) := by
      rw [Finset.sum_eq_single (i + j)]
      · rw [if_pos]; simp only [f]; omega
      · intro k hk hne; rw [if_neg]; simp only [mem_range] at hk; simp only [f]; omega
      · intro h; exact absurd (mem_range.mpr hij) h
    have s2 : (∑ k ∈ range n, if f i j k = 2 * n - 1 then w i * w j * w k else 0) = 0 := by
      apply Finset.sum_eq_zero; intro k hk; rw [if_neg]; simp only [mem_range] at hk; simp only [f]; omega
    rw [Finset.sum_add_distrib, s1, s2, add_zero]
  · have hmod : (i + j) % n = i + j - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    have s1 : (∑ k ∈ range n, if f i j k = n - 1 then w i * w j * w k else 0) = 0 := by
      apply Finset.sum_eq_zero; intro k hk; rw [if_neg]; simp only [mem_range] at hk; simp only [f]; omega
    have s2 : (∑ k ∈ range n, if f i j k = 2 * n - 1 then w i * w j * w k else 0) = w i * w j * w (i + j - n) := by
      rw [Finset.sum_eq_single (i + j - n)]
      · rw [if_pos]; simp only [f]; omega
      · intro k hk hne; rw [if_neg]; simp only [mem_range] at hk; simp only [f]; omega
      · intro h; exact absurd (mem_range.mpr (by omega)) h
    rw [Finset.sum_add_distrib, s1, s2, zero_add]

end Arxiv250103234StepH1

theorem OMA.solution : OMA.R_Arxiv_2501_03234_conjecture_1_1_R1_H1_R1.H1 := Arxiv250103234StepH1.main
