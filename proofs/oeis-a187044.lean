import OMAStatements.S_oeis_a187044
import Mathlib

namespace OMA.S_oeis_a187044

lemma entry_zero : ∀ n k : ℕ, n < k → entry n k = 0
  | 0, k, h => by simp [entry]; omega
  | 1, k, h => by simp [entry]; omega
  | n + 2, k, h => by
    have h1 : ¬ k ≤ n + 1 := by omega
    have h2 : k ≠ n + 2 := by omega
    simp [entry, h1, h2]

lemma entry_step (n k : ℕ) (h : k ≤ n + 1) :
    entry (n + 2) k = entry (n + 1) k + ((n + 1 : ℕ) : ℤ) * entry n k := by
  simp [entry, h]

lemma entry_diag (n : ℕ) : entry (n + 2) (n + 2) = 1 := by
  simp [entry]

lemma rs_rec (n : ℕ) : rowSum (n + 2) = rowSum (n + 1) + ((n : ℤ) + 1) * rowSum n + 1 := by
  unfold rowSum
  rw [Finset.sum_range_succ, entry_diag]
  have h1 : ∀ k ∈ Finset.range (n + 2), entry (n + 2) k = entry (n + 1) k + ((n : ℤ) + 1) * entry n k := by
    intro k hk
    have hk := Finset.mem_range.mp hk
    rw [entry_step n k (by omega)]; push_cast; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_range_succ (fun k => entry n k) (n + 1), entry_zero n (n + 1) (by omega)]
  ring

end OMA.S_oeis_a187044

theorem OMA.solution : type_of% @OMA.S_oeis_a187044.main := by
  intro n hn
  open OMA.S_oeis_a187044 in
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h1 := rs_rec (m + 1)
  have h2 := rs_rec m
  have e1 : m + 3 - 1 = m + 2 := rfl
  have e2 : m + 3 - 2 = m + 1 := rfl
  have e3 : m + 3 - 3 = m := rfl
  rw [e1, e2, e3]
  push_cast at h1 h2 ⊢
  linear_combination h1 - h2
