import OMAStatements.S_oeis_a372991
import Mathlib

-- Proof: every term is positive, so a(m+3) a(m+2) a(m+1) = (2m+6)! and a(m+2) a(m+1) a(m) = (2m+4)!;
-- dividing gives a(m+3) = (2m+6)(2m+5) a(m).

namespace OMA.P_oeis_a372991
open OMA.S_oeis_a372991

lemma pos : ∀ n, 0 < a n
  | 0 => by simp [a]
  | 1 => by simp [a]
  | n + 2 => by
    rw [a]
    have h1 := pos (n + 1)
    have h0 := pos n
    positivity

lemma step (m : ℕ) : a (m + 3) = (2 * (m : ℚ) + 6) * (2 * m + 5) * a m := by
  have h1 := pos (m + 1)
  have h0 := pos m
  have h2 : a (m + 2) = (Nat.factorial (2 * (m + 2)) : ℚ) / (a (m + 1) * a m) := by rw [a]
  have h3 : a (m + 3) = (Nat.factorial (2 * (m + 3)) : ℚ) / (a (m + 2) * a (m + 1)) := by rw [a]
  rw [h3, h2]
  have f : (Nat.factorial (2 * (m + 3)) : ℚ) =
      (2 * m + 6) * (2 * m + 5) * (Nat.factorial (2 * (m + 2)) : ℚ) := by
    rw [show 2 * (m + 3) = (2 * (m + 2) + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  rw [f]
  have hf : (0 : ℚ) < (Nat.factorial (2 * (m + 2)) : ℚ) := by positivity
  field_simp

end OMA.P_oeis_a372991

theorem OMA.solution : type_of% @OMA.S_oeis_a372991.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [OMA.P_oeis_a372991.step, show m + 3 - 3 = m by omega]
  push_cast
  ring
