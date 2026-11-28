import OMAStatements.S_oeis_a179902
import Mathlib

namespace OMA.P179902
open OMA.S_oeis_a179902

lemma coeff_row (r m : ℕ) :
    PowerSeries.coeff m (row r) = ∑ k ∈ Finset.range (m + 1), u r k * v r (m - k) := by
  rw [row, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk]

lemma c0 (r : ℕ) : PowerSeries.coeff 0 (row r) = 1 := by
  rw [coeff_row]; simp [u, v]

lemma c1 (r : ℕ) : PowerSeries.coeff 1 (row r) = r := by
  rw [coeff_row]; simp [Finset.sum_range_succ, u, v]

lemma c2 (r m : ℕ) : PowerSeries.coeff (m + 1 + 1) (row r) = 2 * r + r ^ 2 * m := by
  rw [coeff_row, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ']
  have h : ∀ k ∈ Finset.range m, u r (k + 1) * v r (m + 1 + 1 - (k + 1)) = r * r := by
    intro k hk
    rw [Finset.mem_range] at hk
    have h0 : k + 1 ≠ 0 := by omega
    have h1 : m + 1 + 1 - (k + 1) ≠ 0 := by omega
    have h2 : m + 1 + 1 - (k + 1) ≠ 1 := by omega
    simp only [u, v]
    rw [if_neg h0, if_neg h1, if_neg h2]
  rw [Finset.sum_congr rfl h]
  have e1 : m + 1 + 1 - (m + 1) = 1 := by omega
  have e2 : m + 1 + 1 - (m + 1 + 1) = 0 := by omega
  rw [e1, e2]
  simp [u, v]
  ring

lemma a_eq (n : ℕ) : a n = ∑ j ∈ Finset.range n, PowerSeries.coeff j (row (n - j)) := by
  unfold a T A
  refine Finset.sum_nbij' (fun k => k - 1) (fun j => j + 1) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢; omega
  · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro j hj; simp
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    have : n + 1 - k = n - (k - 1) := by omega
    rw [this]

lemma b_eq (n : ℕ) :
    a (n + 2) = ∑ j ∈ Finset.range n, (2 * (n - j) + (n - j) ^ 2 * j) + (n + 1) + 1 := by
  rw [a_eq, show n + 2 = n + 1 + 1 from rfl, Finset.sum_range_succ', Finset.sum_range_succ']
  have h : ∀ j ∈ Finset.range n, PowerSeries.coeff (j + 1 + 1) (row (n + 1 + 1 - (j + 1 + 1)))
      = 2 * (n - j) + (n - j) ^ 2 * j := by
    intro j hj
    rw [c2]
    have : n + 1 + 1 - (j + 1 + 1) = n - j := by omega
    rw [this]
  rw [Finset.sum_congr rfl h, c1, c0]
  have : n + 1 + 1 - (0 + 1) = n + 1 := by omega
  rw [this]

lemma b_int (n : ℕ) :
    (a (n + 2) : ℤ) = ∑ j ∈ Finset.range n, (2 * ((n : ℤ) - j) + ((n : ℤ) - j) ^ 2 * j) + n + 2 := by
  rw [b_eq]
  push_cast
  have h : ∀ j ∈ Finset.range n, (2 * ((n - j : ℕ) : ℤ) + ((n - j : ℕ) : ℤ) ^ 2 * (j : ℤ))
      = 2 * ((n : ℤ) - j) + ((n : ℤ) - j) ^ 2 * j := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Nat.cast_sub hj.le]
  rw [Finset.sum_congr rfl h]
  ring

lemma Q (x : ℤ) (n : ℕ) :
    12 * ∑ j ∈ Finset.range n, (2 * (x - j) + (x - j) ^ 2 * j)
      = 24 * x * n - 12 * n * (n - 1) + 6 * x ^ 2 * n * (n - 1)
        - 4 * x * (n - 1) * n * (2 * n - 1) + 3 * (n : ℤ) ^ 2 * (n - 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

lemma closed (n : ℕ) : (12 : ℤ) * a (n + 2) = (n : ℤ) ^ 4 + 11 * (n : ℤ) ^ 2 + 24 * n + 24 := by
  rw [b_int]
  have hQ := Q (n : ℤ) n
  linear_combination hQ

lemma par (n : ℕ) : a (n + 2) % 2 = if n % 4 = 0 then 0 else 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (by omega : n < 4 ∨ 4 ≤ n) with h | h
    · have h12 := closed n
      interval_cases n <;> norm_num at h12 ⊢ <;> omega
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have ihm := ih m (by omega)
      have key : (12 : ℤ) * a (m + 4 + 2)
          = 12 * a (m + 2) + 16 * (m : ℤ) ^ 3 + 96 * (m : ℤ) ^ 2 + 344 * m + 528 := by
        rw [closed (m + 4), closed m]; push_cast; ring
      have hm : (m + 4) % 4 = m % 4 := by omega
      rw [hm, ← ihm]
      generalize (m : ℤ) ^ 3 = A at key
      generalize (m : ℤ) ^ 2 = B at key
      omega

lemma a_one : a 1 = 1 := by
  rw [a_eq]; simp [c0]

theorem sol : type_of% @OMA.S_oeis_a179902.main := by
  intro n hn
  rcases (by omega : n = 1 ∨ 2 ≤ n) with h | h
  · subst h; rw [a_one]; decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [par m]
    by_cases hm : m % 4 = 0
    · have : (m + 2) % 4 = 2 := by omega
      rw [if_pos hm, if_pos this]
    · have : (m + 2) % 4 ≠ 2 := by omega
      rw [if_neg hm, if_neg this]

end OMA.P179902

theorem OMA.solution : type_of% @OMA.S_oeis_a179902.main := OMA.P179902.sol
