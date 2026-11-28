import Mathlib

/-!
# A078130: Numbers having exactly one representation as sum of cubes > 1.

Source: https://oeis.org/A078130
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: the sequence is finite; is a(63)=218 the last entry?
-/

namespace OMA.S_oeis_a078130

/-- Number of partitions of `n` into cubes greater than `1`. -/
noncomputable def numCubePartitions (n : ℕ) : ℕ :=
  Nat.card { P : Nat.Partition n // ∀ p ∈ P.parts, ∃ m : ℕ, 2 ≤ m ∧ p = m ^ 3 }

theorem main :
    { n : ℕ | numCubePartitions n = 1 }.Finite := by sorry

end OMA.S_oeis_a078130
