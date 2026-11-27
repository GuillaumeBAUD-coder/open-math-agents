import OMAStatements.S_oeis_a037958
import Mathlib

-- Problem: oeis-a037958
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P037958
open OMA.S_oeis_a037958

lemma ae (k : ℕ) : (a (2 * k + 10) : ℚ) = ((2 * k + 10).choose (k + 1) : ℚ) := by
  unfold a; rw [if_neg (by omega), show (2 * k + 10 - 8) / 2 = k + 1 by omega]; all_goals (push_cast; rfl)

lemma ao (k : ℕ) : (a (2 * k + 9) : ℚ) = ((2 * k + 9).choose k : ℚ) := by
  unfold a; rw [if_neg (by omega), show (2 * k + 9 - 8) / 2 = k by omega]; all_goals (push_cast; rfl)

lemma ae' (k : ℕ) : (a (2 * k + 8) : ℚ) = ((2 * k + 8).choose k : ℚ) := by
  unfold a; rw [if_neg (by omega), show (2 * k + 8 - 8) / 2 = k by omega]; all_goals (push_cast; rfl)

lemma c1 (k : ℕ) : ((2 * k + 9).choose k : ℚ) = ((2 * k + 8).choose k : ℚ) * (2 * k + 9) / (k + 9) := by
  rw [Nat.cast_choose ℚ (by omega), Nat.cast_choose ℚ (by omega), show 2 * k + 9 - k = (k + 8) + 1 by omega,
    show 2 * k + 8 - k = k + 8 by omega, show 2 * k + 9 = (2 * k + 8) + 1 by ring,
    Nat.factorial_succ (2 * k + 8), Nat.factorial_succ (k + 8)]
  have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((k + 8).factorial : ℚ) ≠ 0 := by positivity
  push_cast; field_simp; ring

lemma c2 (k : ℕ) : ((2 * k + 10).choose (k + 1) : ℚ) = ((2 * k + 9).choose k : ℚ) * (2 * k + 10) / (k + 1) := by
  rw [Nat.cast_choose ℚ (by omega), Nat.cast_choose ℚ (by omega), show 2 * k + 10 - (k + 1) = k + 9 by omega,
    show 2 * k + 9 - k = k + 9 by omega, show 2 * k + 10 = (2 * k + 9) + 1 by ring,
    Nat.factorial_succ (2 * k + 9), Nat.factorial_succ k]
  have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((k + 9).factorial : ℚ) ≠ 0 := by positivity
  push_cast; field_simp; ring

theorem sol : type_of% @OMA.S_oeis_a037958.main := by
  intro n hn
  rcases (show n < 10 ∨ 10 ≤ n by omega) with h | h
  · interval_cases n <;> decide
  rw [← Int.cast_inj (α := ℚ)]
  push_cast
  rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 5 := ⟨j - 5, by omega⟩
    subst hj
    rw [show k + 5 + (k + 5) = 2 * k + 10 by ring, show 2 * k + 10 - 1 = 2 * k + 9 by omega,
      show 2 * k + 10 - 2 = 2 * k + 8 by omega, ae, ao, ae', c2, c1]
    push_cast
    field_simp
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 5 := ⟨j - 5, by omega⟩
    subst hj
    rw [show 2 * (k + 5) + 1 = 2 * (k + 1) + 9 by ring, show 2 * (k + 1) + 9 - 1 = 2 * k + 10 by omega,
      show 2 * (k + 1) + 9 - 2 = 2 * k + 9 by omega, ao, ae, ao, c1 (k + 1), c2]
    rw [show 2 * (k + 1) + 8 = 2 * k + 10 by ring, c2, c1]
    push_cast
    field_simp
    ring

end OMA.P037958

theorem OMA.solution : type_of% @OMA.S_oeis_a037958.main := OMA.P037958.sol
