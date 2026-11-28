import Mathlib

/-!
# A083758: Lexicographically earliest infinite sequence of distinct primes such that the concatenation of the initial n terms is a prime for all n.

Source: https://oeis.org/A083758
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: every prime except 5 is a term.
-/

namespace OMA.S_oeis_a083758

def concat10 (x y : ℕ) : ℕ :=
  x * 10 ^ (Nat.digits 10 y).length + y

def concatList (L : List ℕ) : ℕ :=
  L.foldl concat10 0

noncomputable def seqRev : ℕ → List ℕ
  | 0 => [2]
  | n + 1 =>
    let prev := seqRev n
    let pref := concatList prev.reverse
    let next := sInf {p : ℕ | Nat.Prime p ∧ p ∉ prev ∧ Nat.Prime (concat10 pref p)}
    next :: prev

noncomputable def a (n : ℕ) : ℕ :=
  (seqRev n).headD 2

theorem main :
    ∀ p : ℕ, Nat.Prime p → p ≠ 5 → ∃ n : ℕ, a n = p := by
  sorry

end OMA.S_oeis_a083758
