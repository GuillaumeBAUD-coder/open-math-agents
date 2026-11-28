import OMAStatements.S_mo_496220
import Mathlib

namespace OrderedWeights

open Finset OMA.S_mo_496220
open scoped BigOperators

private noncomputable def total (n : ℕ) : Polynomial ℤ :=
  ∑ j ∈ range (n + 1), R n j

private noncomputable def tail (n lo : ℕ) : Polynomial ℤ :=
  ∑ j ∈ Ico lo n, R n j

private theorem diagonal (n : ℕ) : R n n = 1 := by
  cases n <;> simp [R]

private theorem total_eq (n : ℕ) : total n = tail n 0 + 1 := by
  simp only [total, tail, Nat.Ico_zero_eq_range, sum_range_succ, diagonal]

private theorem update (n k : ℕ) (hk : k ≤ n) :
    R (n + 1) k = Polynomial.X ^ k * (total n + tail n k) := by
  have hsum := sum_range_add_sum_Ico (R n) hk
  rw [R, if_neg (by omega : k ≠ n + 1), if_neg (by omega : ¬ n + 1 < k)]
  apply congrArg (Polynomial.X ^ k * ·)
  change 2 * total n - 1 - (∑ j ∈ range k, R n j) = total n + tail n k
  rw [total_eq]
  have hsum' : (∑ j ∈ range k, R n j) + tail n k = tail n 0 := by
    simpa only [tail, Nat.Ico_zero_eq_range] using hsum
  rw [← hsum']
  ring

private theorem block_empty {m lo hi : ℕ} (hlt : hi < lo) :
    block (m + 1) lo hi = 0 := by
  rw [block, Finset.Icc_eq_empty (by omega), sum_empty]

private theorem block_zero_width (m : ℕ) : block m 0 0 = 1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [block, ih]

private theorem extend_block (lo hi top i : ℕ) (hle : hi ≤ top) :
    (∑ j ∈ Icc lo top, Polynomial.X ^ j * block (i + 1) j hi) =
      block (i + 2) lo hi := by
  rw [show block (i + 2) lo hi =
    ∑ j ∈ Icc lo hi, Polynomial.X ^ j * block (i + 1) j hi by rw [block]]
  symm
  apply sum_subset
  · intro j hj
    obtain ⟨hl, hr⟩ := mem_Icc.mp hj
    exact mem_Icc.mpr ⟨hl, hr.trans hle⟩
  · intro j hj hn
    have hgt : hi < j := by
      exact lt_of_not_ge (fun h => hn (mem_Icc.mpr ⟨(mem_Icc.mp hj).1, h⟩))
    rw [block_empty hgt, mul_zero]

private theorem tail_sum (n lo : ℕ) :
    tail n lo = ∑ i ∈ range n, block (i + 1) lo (n - 1 - i) * total (n - 1 - i) := by
  induction n generalizing lo with
  | zero => simp [tail]
  | succ n ih =>
    have hsplit :
        tail (n + 1) lo =
          (∑ j ∈ Icc lo n, Polynomial.X ^ j * total n) +
          ∑ j ∈ Icc lo n, Polynomial.X ^ j * tail n j := by
      rw [tail, Finset.Ico_add_one_right_eq_Icc, ← sum_add_distrib]
      apply sum_congr rfl
      intro j hj
      rw [update n j (mem_Icc.mp hj).2, mul_add]
    rw [hsplit, ← sum_mul]
    have hblock :
        (∑ j ∈ Icc lo n, (Polynomial.X : Polynomial ℤ) ^ j) = block 1 lo n := by
      simp [block]
    rw [hblock]
    have hsum : (∑ j ∈ Icc lo n, Polynomial.X ^ j * tail n j) =
        ∑ i ∈ range n, block (i + 2) lo (n - 1 - i) * total (n - 1 - i) := by
      simp_rw [ih, mul_sum, ← mul_assoc]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      rw [← sum_mul, extend_block lo (n - 1 - i) n i (by omega)]
    rw [hsum, sum_range_succ']
    simp only [Nat.add_sub_cancel, Nat.sub_zero]
    rw [add_comm]
    congr 1
    apply sum_congr rfl
    intro i _
    have hi : n - (i + 1) = n - 1 - i := by omega
    rw [hi]

private theorem total_ordered (n : ℕ) (hn : 0 < n) : total n = 2 * ordered n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [total_eq, tail_sum, ordered]
    simp only [Nat.succ_sub_one]
    rw [sum_range_succ, sum_range_succ]
    have hzero : total 0 = 1 := by simp [total, diagonal]
    simp only [Nat.sub_self, block_zero_width, ordered, hzero, one_mul]
    rw [mul_add, mul_sum]
    have heq :
        (∑ i ∈ range m, block (i + 1) 0 (m - i) * total (m - i)) =
          ∑ i ∈ range m, 2 * (block (i + 1) 0 (m - i) * ordered (m - i)) := by
      apply sum_congr rfl
      intro i hi
      have hi' := mem_range.mp hi
      rw [ih (m - i) (by omega) (by omega)]
      ring
    rw [heq]
    ring

theorem identity : type_of% @OMA.S_mo_496220.main := by
  intro n hn
  rw [update n 0 (Nat.zero_le n), pow_zero, one_mul]
  rw [show tail n 0 = total n - 1 by rw [total_eq]; ring, total_ordered n hn]
  ring

end OrderedWeights

theorem OMA.solution : type_of% @OMA.S_mo_496220.main := OrderedWeights.identity