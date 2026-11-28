import OMAStatements.S_oeis_a093387
import Mathlib

namespace A093387
open OMA.S_oeis_a093387

/-- The middle binomial coefficient binomial(n, floor(n/2)). -/
def b (n : ℕ) : ℤ := (Nat.choose n (n / 2) : ℤ)

lemma a_eq (n : ℕ) : a n = (2 : ℤ) ^ (n - 1) - b n := rfl

lemma b_even (n : ℕ) (hn : n % 2 = 0) (h2 : 2 ≤ n) : b n = 2 * b (n - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 2 := ⟨(n - 2) / 2, by omega⟩
  unfold b
  rw [show (2 * j + 2) / 2 = j + 1 by omega, show 2 * j + 2 - 1 = 2 * j + 1 by omega,
    show (2 * j + 1) / 2 = j by omega, show 2 * j + 2 = 2 * j + 1 + 1 by omega,
    Nat.choose_succ_succ, Nat.choose_symm_half]
  push_cast
  ring

lemma b_odd (n : ℕ) (hn : n % 2 = 1) : ((n : ℤ) + 1) * b n = 2 * (n : ℤ) * b (n - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 1 := ⟨(n - 1) / 2, by omega⟩
  unfold b
  rw [show (2 * j + 1) / 2 = j by omega, show 2 * j + 1 - 1 = 2 * j by omega,
    show (2 * j) / 2 = j by omega]
  have h := Nat.choose_mul_succ_eq (2 * j) j
  rw [show 2 * j + 1 - j = j + 1 by omega] at h
  have h' : (((2 * j).choose j * (2 * j + 1) : ℕ) : ℤ) = (((2 * j + 1).choose j * (j + 1) : ℕ) : ℤ) := by
    rw [h]
  push_cast at h' ⊢
  linear_combination (-2 : ℤ) * h'

end A093387

theorem OMA.solution : type_of% @OMA.S_oeis_a093387.main := by
  intro n hn
  rw [A093387.a_eq, A093387.a_eq, A093387.a_eq, A093387.a_eq]
  have p1 : (2 : ℤ) ^ (n - 1) = 8 * 2 ^ (n - 4) := by
    rw [show n - 1 = (n - 4) + 3 by omega]; ring
  have p2 : (2 : ℤ) ^ (n - 1 - 1) = 4 * 2 ^ (n - 4) := by
    rw [show n - 1 - 1 = (n - 4) + 2 by omega]; ring
  have p3 : (2 : ℤ) ^ (n - 2 - 1) = 2 * 2 ^ (n - 4) := by
    rw [show n - 2 - 1 = (n - 4) + 1 by omega]; ring
  have p4 : (2 : ℤ) ^ (n - 3 - 1) = 2 ^ (n - 4) := by
    rw [show n - 3 - 1 = n - 4 by omega]
  rw [p1, p2, p3, p4]
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have h1 := A093387.b_even n he (by omega)
    have h2 := A093387.b_even (n - 2) (by omega) (by omega)
    rw [show n - 2 - 1 = n - 3 by omega] at h2
    linear_combination (-((n : ℤ) + 1)) * h1 + 4 * ((n : ℤ) - 2) * h2
  · have h1 := A093387.b_odd n ho
    have h2 := A093387.b_even (n - 1) (by omega) (by omega)
    rw [show n - 1 - 1 = n - 2 by omega] at h2
    have h3 := A093387.b_odd (n - 2) (by omega)
    rw [show n - 2 - 1 = n - 3 by omega] at h3
    have hc : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by
      rw [Nat.cast_sub (by omega)]; rfl
    rw [hc] at h3
    linear_combination (-1 : ℤ) * h1 + 2 * h2 + 4 * h3
