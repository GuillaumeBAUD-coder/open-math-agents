import OMAStatements.S_oeis_a052227
import Mathlib

lemma OMA.cc (n : ℕ) : ((3 * n).choose n : ℚ) =
    (3 * n).factorial / (n.factorial * (2 * n).factorial) := by
  rw [Nat.cast_choose ℚ (by omega : n ≤ 3 * n), show 3 * n - n = 2 * n by omega]

theorem OMA.solution : type_of% @OMA.S_oeis_a052227.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
  simp only [OMA.S_oeis_a052227.a, OMA.cc]
  rw [show 3 * (k + 2) = 3 * k + 5 + 1 by ring, show 2 * (k + 2) = 2 * k + 3 + 1 by ring,
    show 3 * (k + 1) = 3 * k + 2 + 1 by ring, show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
  simp only [Nat.factorial_succ, show 3 * k + 5 = 3 * k + 4 + 1 by ring,
    show 3 * k + 4 = 3 * k + 3 + 1 by ring, show 3 * k + 3 = 3 * k + 2 + 1 by ring,
    show 3 * k + 2 = 3 * k + 1 + 1 by ring, show 2 * k + 3 = 2 * k + 2 + 1 by ring,
    show 2 * k + 2 = 2 * k + 1 + 1 by ring, Nat.factorial_succ]
  have : ((3 * k).factorial : ℚ) ≠ 0 := by positivity
  have : ((2 * k).factorial : ℚ) ≠ 0 := by positivity
  have : (k.factorial : ℚ) ≠ 0 := by positivity
  have : (2 * (k : ℚ) + 1) ≠ 0 := by positivity
  have : (2 * ((k : ℚ) + 1) + 1) ≠ 0 := by positivity
  have : (2 * ((k : ℚ) + 2) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring
