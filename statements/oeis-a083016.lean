import Mathlib

/-!
# A083016: Rearrangement of primes such that the sum of two consecutive terms is a square.

Source: https://oeis.org/A083016
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Bunyakovsky's conjecture implies that a(n) always exists.
-/

namespace OMA.S_oeis_a083016

noncomputable def seqRev : ℕ → List ℕ
  | 0 => [2]
  | n + 1 =>
    let prev := seqRev n
    let last := prev.headD 2
    let next := sInf {q : ℕ | Nat.Prime q ∧ q ∉ prev ∧ IsSquare (last + q)}
    next :: prev

theorem main :
    ∀ n : ℕ, ∃ q : ℕ, Nat.Prime q ∧ q ∉ seqRev n ∧ IsSquare ((seqRev n).headD 2 + q) := by
  sorry

end OMA.S_oeis_a083016
