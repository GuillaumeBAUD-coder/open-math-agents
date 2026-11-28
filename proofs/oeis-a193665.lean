import OMAStatements.S_oeis_a193665
import Mathlib

namespace OMA.S_oeis_a193665
open Finset

def Sf (n : ℕ) : ℤ := ∑ j ∈ range (n + 1), ((n + 1 - j : ℕ) : ℤ) * r j
def Tf (n : ℕ) : ℤ := ∑ j ∈ range (n + 1), r j

lemma r_succ (n : ℕ) : r (n + 1) = ((n : ℤ) + 1) * Sf n := by
  rw [r, Fin.sum_univ_eq_sum_range (fun i => ((((i : ℕ) : ℤ) + 1) * ((n : ℤ) + 1)) * r (n - i)) (n + 1)]
  unfold Sf
  rw [Finset.mul_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < n + 1 := Finset.mem_range.1 hj
  have e1 : n + 1 - 1 - j = n - j := by omega
  have e2 : n - (n - j) = j := by omega
  have e3 : n + 1 - j = (n - j) + 1 := by omega
  simp only [e1, e2, e3]
  push_cast [Nat.cast_sub (show j ≤ n by omega)]
  ring

lemma a_eq (n : ℕ) : a n = r (n + 1) := by
  rw [r_succ]
  unfold a Sf
  rw [Finset.mul_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < n + 1 := Finset.mem_range.1 hj
  have e1 : n + 1 - 1 - j = n - j := by omega
  have e2 : n - (n - j) = j := by omega
  have e3 : n + 1 - j = (n - j) + 1 := by omega
  simp only [e1, e2, e3]
  push_cast [Nat.cast_sub (show j ≤ n by omega)]
  ring

lemma Sf_succ (n : ℕ) : Sf (n + 1) = Sf n + Tf (n + 1) := by
  unfold Sf Tf
  rw [Finset.sum_range_succ (fun j => ((n + 1 + 1 - j : ℕ) : ℤ) * r j) (n + 1)]
  rw [Finset.sum_range_succ (fun j => r j) (n + 1)]
  have : ∑ j ∈ range (n + 1), ((n + 1 + 1 - j : ℕ) : ℤ) * r j
      = ∑ j ∈ range (n + 1), (((n + 1 - j : ℕ) : ℤ) * r j + r j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < n + 1 := Finset.mem_range.1 hj
    have : n + 1 + 1 - j = (n + 1 - j) + 1 := by omega
    rw [this]; push_cast; ring
  rw [this, Finset.sum_add_distrib, show n + 1 + 1 - (n + 1) = 1 by omega]
  push_cast
  ring

lemma Tf_succ (n : ℕ) : Tf (n + 1) = Tf n + r (n + 1) := by
  unfold Tf; rw [Finset.sum_range_succ]

lemma Sf_rec (n : ℕ) : Sf (n + 2) = ((n : ℤ) + 4) * Sf (n + 1) - Sf n := by
  have h1 := Sf_succ (n + 1)
  have h2 := Sf_succ n
  have h3 := Tf_succ (n + 1)
  have h4 := r_succ (n + 1)
  push_cast at h4
  linarith

lemma main_aux (n : ℕ) : a (n + 3) + (-((n + 3 : ℕ) : ℤ) - 4) * a (n + 2) + (((n + 3 : ℕ) : ℤ) + 1) * a (n + 1) - a n = 0 := by
  rw [a_eq, a_eq, a_eq, a_eq, r_succ, r_succ, r_succ, r_succ]
  have e1 := Sf_rec (n + 1)
  have e2 := Sf_rec n
  push_cast at *
  linear_combination ((n:ℤ) + 4) * e1 - ((n:ℤ) + 1) * e2

end OMA.S_oeis_a193665

theorem OMA.solution : type_of% @OMA.S_oeis_a193665.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have := OMA.S_oeis_a193665.main_aux m
  simpa using this
