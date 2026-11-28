import OMAStatements.S_oeis_a152661
import Mathlib
open OMA.S_oeis_a152661

theorem OMA.solution : type_of% @OMA.S_oeis_a152661.main := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · simp only [sameParity]
    rw [show t + 4 - 2 = t + 1 + 1 by omega, show t + 3 - 2 = t + 1 by omega,
      show t + 2 - 2 = t by omega]
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' t
    · simp only [show (2 * j + 4) / 2 = j + 2 by omega, show (2 * j + 4 + 1) / 2 = j + 2 by omega,
        show (2 * j + 3) / 2 = j + 1 by omega, show (2 * j + 3 + 1) / 2 = j + 2 by omega,
        show (2 * j + 2) / 2 = j + 1 by omega, show (2 * j + 2 + 1) / 2 = j + 1 by omega]
      simp only [Nat.factorial_succ]
      push_cast
      ring
    · simp only [show (2 * j + 1 + 4) / 2 = j + 2 by omega, show (2 * j + 1 + 4 + 1) / 2 = j + 3 by omega,
        show (2 * j + 1 + 3) / 2 = j + 2 by omega, show (2 * j + 1 + 3 + 1) / 2 = j + 2 by omega,
        show (2 * j + 1 + 2) / 2 = j + 1 by omega, show (2 * j + 1 + 2 + 1) / 2 = j + 2 by omega]
      simp only [Nat.factorial_succ]
      push_cast
      ring
  · simp only [sameParity, evenOddPairs]
    rw [show t + 2 - 2 = t by omega, show t + 1 - 1 = t by omega]
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' t
    · simp only [show (2 * j + 2) / 2 = j + 1 by omega, show (2 * j + 2 + 1) / 2 = j + 1 by omega,
        show (2 * j + 1) / 2 = j by omega, show (2 * j + 1 + 1) / 2 = j + 1 by omega]
      push_cast
      ring
    · simp only [show (2 * j + 1 + 2) / 2 = j + 1 by omega, show (2 * j + 1 + 2 + 1) / 2 = j + 2 by omega,
        show (2 * j + 1 + 1) / 2 = j + 1 by omega, show (2 * j + 1 + 1 + 1) / 2 = j + 1 by omega]
      push_cast
      ring
