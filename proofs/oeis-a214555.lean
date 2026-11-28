import OMAStatements.S_oeis_a214555
import Mathlib

open OMA.S_oeis_a214555 in
theorem OMA.solution : type_of% @OMA.S_oeis_a214555.main := by
  have hrep : ∀ k d : ℕ, 9 * ((Nat.ofDigits 10 (List.replicate k d) : ℕ) : ℤ) = d * (10 ^ k - 1) := by
    intro k d
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.replicate_succ, Nat.ofDigits_cons]
      push_cast at ih ⊢
      rw [pow_succ]
      linear_combination 10 * ih
  have key : ∀ n, 9 * (a n : ℤ) = 45 + 40 * ((10 : ℤ) ^ n - 1) + 900 * ((10 : ℤ) ^ n) ^ 2
      - 90 * (10 : ℤ) ^ n + 3600 * ((10 : ℤ) ^ n) ^ 2 + 5000 * ((10 : ℤ) ^ n) ^ 2 * ((10 : ℤ) ^ n - 1) := by
    intro n
    have h1 := hrep n 4
    have h2 := hrep (n + 1) 9
    have h3 := hrep n 5
    simp only [a, digitList, List.reverse_append, List.reverse_replicate, List.reverse_cons,
      List.reverse_nil, List.nil_append, Nat.ofDigits_append, List.length_replicate,
      List.length_singleton, List.length_append, List.singleton_append, Nat.ofDigits_cons,
      Nat.ofDigits_nil, List.cons_append]
    push_cast at h1 h2 h3 ⊢
    linear_combination 10 * h1 + 10 ^ (n + 1) * h2 + 10 ^ (2 * n + 3) * h3
  intro n
  have k0 := key n
  have k1 := key (n + 1)
  have k2 := key (n + 2)
  have k3 := key (n + 3)
  have k4 := key (n + 4)
  simp only [pow_add] at k1 k2 k3 k4
  have : 9 * ((a (n + 4) : ℤ) - (1111 * a (n + 3) - 112110 * a (n + 2) + 1111000 * a (n + 1)
      - 1000000 * a n)) = 0 := by
    linear_combination k4 - 1111 * k3 + 112110 * k2 - 1111000 * k1 + 1000000 * k0
  linarith
