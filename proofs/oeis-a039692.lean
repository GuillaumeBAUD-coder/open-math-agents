import OMAStatements.S_oeis_a039692
import Mathlib

namespace OMA.S_oeis_a039692
open Finset

lemma sum_stirling (k : ℕ) : ∀ N : ℕ, k < N → ∑ m ∈ range N, Nat.stirlingFirst k m = k.factorial := by
  induction k with
  | zero =>
    intro N hN
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb
      obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
      exact Nat.stirlingFirst_zero_succ c
    · intro h
      exact absurd (Finset.mem_range.2 hN) h
  | succ k ih =>
    intro N hN
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have hz : Nat.stirlingFirst (k + 1) 0 = 0 := Nat.stirlingFirst_succ_zero k
    have hrec : ∀ m, Nat.stirlingFirst (k + 1) (m + 1) = k * Nat.stirlingFirst k (m + 1) + Nat.stirlingFirst k m :=
      fun m => Nat.stirlingFirst_succ_succ k m
    simp only [hrec, Finset.sum_add_distrib, ← Finset.mul_sum, hz, add_zero]
    have h1 := ih N' (by omega)
    have h2 := ih (N' + 1) (by omega)
    rw [Finset.sum_range_succ'] at h2
    have h0 : k * Nat.stirlingFirst k 0 = 0 := by cases k <;> simp
    have h3 := congrArg (fun z => k * z) h2
    simp only [mul_add] at h3
    rw [Nat.factorial_succ]
    nlinarith [h1, h3, h0]

end OMA.S_oeis_a039692

theorem OMA.solution : type_of% @OMA.S_oeis_a039692.main := by
  intro n hn
  unfold OMA.S_oeis_a039692.entry
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hfib := Nat.fib_succ_eq_sum_choose n
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hfib
  have key : ∀ k ∈ Finset.range (n + 1),
      ∑ m ∈ Finset.range (n + 1), (Nat.stirlingFirst k m : ℚ) * (k.choose (n - k) : ℚ) / (k.factorial : ℚ)
        = (k.choose (n - k) : ℚ) := by
    intro k hk
    have hkn : k < n + 1 := Finset.mem_range.1 hk
    have hs := OMA.S_oeis_a039692.sum_stirling k (n + 1) hkn
    have hs' : ∑ m ∈ Finset.range (n + 1), (Nat.stirlingFirst k m : ℚ) = (k.factorial : ℚ) := by
      exact_mod_cast hs
    have hne : (k.factorial : ℚ) ≠ 0 := by positivity
    rw [← Finset.sum_div, ← Finset.sum_mul, hs']
    field_simp
  rw [Finset.sum_congr rfl key]
  have : (∑ k ∈ Finset.range (n + 1), (k.choose (n - k) : ℚ)) = (Nat.fib (n + 1) : ℚ) := by
    exact_mod_cast hfib.symm
  rw [this]
