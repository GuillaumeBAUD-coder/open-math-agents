import OMAStatements.S_oeis_a052204
import Mathlib

lemma OMA.cc (n : ℕ) : ((4 * n).choose n : ℚ) =
    (4 * n).factorial / (n.factorial * (3 * n).factorial) := by
  rw [Nat.cast_choose ℚ (by omega : n ≤ 4 * n), show 4 * n - n = 3 * n by omega]

theorem OMA.solution : type_of% @OMA.S_oeis_a052204.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
  simp only [OMA.S_oeis_a052204.a, OMA.cc]
  rw [show 4 * (k + 2) = 4 * k + 7 + 1 by ring, show 3 * (k + 2) = 3 * k + 5 + 1 by ring,
    show 4 * (k + 1) = 4 * k + 3 + 1 by ring, show 3 * (k + 1) = 3 * k + 2 + 1 by ring]
  simp only [Nat.factorial_succ, show 4 * k + 7 = 4 * k + 6 + 1 by ring,
    show 4 * k + 6 = 4 * k + 5 + 1 by ring, show 4 * k + 5 = 4 * k + 4 + 1 by ring,
    show 4 * k + 4 = 4 * k + 3 + 1 by ring, show 4 * k + 3 = 4 * k + 2 + 1 by ring,
    show 4 * k + 2 = 4 * k + 1 + 1 by ring,
    show 3 * k + 5 = 3 * k + 4 + 1 by ring, show 3 * k + 4 = 3 * k + 3 + 1 by ring,
    show 3 * k + 3 = 3 * k + 2 + 1 by ring, show 3 * k + 2 = 3 * k + 1 + 1 by ring,
    Nat.factorial_succ]
  have : ((4 * k).factorial : ℚ) ≠ 0 := by positivity
  have : ((3 * k).factorial : ℚ) ≠ 0 := by positivity
  have : (k.factorial : ℚ) ≠ 0 := by positivity
  have : (3 * (k : ℚ) + 1) ≠ 0 := by positivity
  have : (3 * ((k : ℚ) + 1) + 1) ≠ 0 := by positivity
  have : (3 * ((k : ℚ) + 2) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring
