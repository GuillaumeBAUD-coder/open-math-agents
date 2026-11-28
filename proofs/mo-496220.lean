import OMAStatements.S_mo_496220
import Mathlib.Tactic

/-!
Refine the ordered-partition polynomial by a lower bound on the smallest
element of its first block. The difference between two successive bounds
counts first blocks with a prescribed minimum. Removing this minimum
either leaves a nonempty first block or exposes an arbitrary partition.
The resulting recurrence gives the prefix sums of R, including its two
endpoint corrections.
-/

namespace OrderedPartitionRows

open OMA.S_mo_496220 Polynomial Finset

private abbrev Poly := Polynomial ℤ

private noncomputable def tail : ℕ → ℕ → Poly
  | 0, _ => 0
  | n + 1, k => ∑ i ∈ range (n + 1), block (i+1) k (n-i) * ordered (n-i)

private theorem tail_zero (n : ℕ) (hn : 0 < n) : tail n 0 = ordered n := by
  cases n with
  | zero => omega
  | succ n => rw [tail, ordered]

private theorem block_empty (m k h : ℕ) (hk : h < k) : block (m+1) k h = 0 := by
  simp [block, Icc_eq_empty_of_lt hk]

private theorem tail_empty (n k : ℕ) (hn : n ≤ k) : tail n k = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [tail]
    apply sum_eq_zero
    intro i hi
    rw [block_empty i k (n-i) (by omega), zero_mul]

private theorem cut (m k h : ℕ) (hk : k ≤ h) :
    block (m+1) k h - block (m+1) (k+1) h = X^k * block m k h := by
  have he : Icc k h = insert k (Icc (k+1) h) := by
    ext j
    simp only [mem_Icc, mem_insert]
    omega
  simp only [block]
  rw [he, sum_insert (by simp)]
  ring

private theorem cut_nonempty (m k h : ℕ) :
    block (m+2) k h - block (m+2) (k+1) h = X^k * block (m+1) k h := by
  by_cases hk : k ≤ h
  · exact cut (m+1) k h hk
  · have h₁ : h < k := by omega
    have h₂ : h < k+1 := by omega
    rw [block_empty (m+1) k h h₁, block_empty (m+1) (k+1) h h₂, block_empty m k h h₁]
    simp

private theorem peel (n k : ℕ) :
    tail (n+1) k = block 1 k n * ordered n +
       ∑ i ∈ range n, block (i+2) k (n-(i+1)) * ordered (n-(i+1)) := by
  rw [tail, sum_range_succ']
  simp [add_comm]
  apply sum_congr rfl
  intro i hi
  rw [show 1+(i+1)=i+2 by omega]

private theorem tail_diff (n k : ℕ) (hk : k ≤ n) :
    tail (n+1) k - tail (n+1) (k+1) = X^k * (ordered n + tail n k) := by
  have first := cut 0 k n hk
  simp only [block] at first
  rw [peel n k, peel n (k+1)]
  have hd : block 1 k n - block 1 (k+1) n = X^k := by
    simpa only [block, mul_one] using first
  have hsum :
      (∑ i ∈ range n, block (i+2) k (n-(i+1)) * ordered (n-(i+1))) -
        (∑ i ∈ range n, block (i+2) (k+1) (n-(i+1)) * ordered (n-(i+1))) =
        X^k * tail n k := by
    rw [← sum_sub_distrib]
    simp_rw [← sub_mul, cut_nonempty, mul_assoc]
    rw [← mul_sum]
    cases n with
    | zero => simp [tail]
    | succ n => simp [tail]
  linear_combination hsum + ordered n * hd

private noncomputable def pref (n k : ℕ) : Poly := ∑ j ∈ range k, R n j

private theorem pref_succ (n k : ℕ) : pref n (k+1) = pref n k + R n k := by
  exact sum_range_succ _ _

private theorem diagonal (n : ℕ) : R n n = 1 := by cases n <;> simp [R]

private theorem entry (n k : ℕ) (hk : k ≤ n) :
    R (n+1) k = X^k * (2 * pref n (n+1) - 1 - pref n k) := by
  rw [R, if_neg (by omega), if_neg (by omega)]
  rfl

private theorem prefix_values (n : ℕ) (hn : 0 < n) : ∀ k ≤ n,
    pref n k = 2 * (ordered n - tail n k) - (if k = 0 then 0 else 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hzero : n = 0
    · subst n
      intro k hk
      interval_cases k <;> norm_num [pref, R, tail, ordered, block, sum_range_succ]
    · have hn' : 0 < n := by omega
      have total : pref n (n+1) = 2 * ordered n := by
        rw [pref_succ, diagonal, ih hn' n le_rfl, tail_empty n n le_rfl, if_neg hzero]
        ring
      intro k hk
      induction k with
      | zero => simp [pref, tail_zero (n+1) (by omega)]
      | succ k step =>
        have hkn : k ≤ n := by omega
        have hdiff := tail_diff n k hkn
        rw [pref_succ, step (by omega), entry n k hkn, total, ih hn' k hkn]
        by_cases hz : k = 0
        · subst k
          simp only [pow_zero, one_mul, if_true, Nat.succ_ne_zero, if_false] at *
          rw [tail_zero n hn'] at *
          linear_combination -2 * hdiff
        · simp only [if_neg hz, Nat.succ_ne_zero, if_false]
          linear_combination -2 * hdiff

theorem result : type_of% @OMA.S_mo_496220.main := by
  intro n hn
  have total : pref n (n+1) = 2 * ordered n := by
    rw [pref_succ, diagonal, prefix_values n hn n le_rfl, tail_empty n n le_rfl, if_neg (by omega)]
    ring
  rw [entry n 0 (by omega), total]
  simp [pref]
  ring

end OrderedPartitionRows

theorem OMA.solution : type_of% @OMA.S_mo_496220.main := OrderedPartitionRows.result
