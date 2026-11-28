import Mathlib

/-!
# A006689: Initially-connected finite automata with 2 inputs and n unlabeled states

Source: https://oeis.org/A006689
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
Let `a(n)` be the number of deterministic, completely-defined, initially-connected
finite automata with 2 inputs and `n` unlabeled states (i.e. up to state relabeling
preserving the initial state and transitions).
Then `a(n) = n * P(n + 1, n + 1)`, where `P(n, k)` satisfies:
- `P(n, 1) = 1` for `n ≥ 1`,
- `P(n, k) = P(n - 1, k) + (n - 1) * P(n, k - 1)` for `1 < k < n`,
- `P(n, n) = (n - 1) * P(n, n - 1)` for `n ≥ 2`.
-/

namespace OMA.S_oeis_a006689

/-- A deterministic, completely-defined, initially-connected finite automaton with
2 inputs (`Fin 2`) and `n` states (`Fin n`). -/
structure ICDA (n : ℕ) where
  init : Fin n
  trans : Fin n → Fin 2 → Fin n
  connected : ∀ q : Fin n, ∃ w : List (Fin 2), w.foldl trans init = q

/-- Isomorphism of initially-connected automata on `Fin n` (state relabeling). -/
def icdaIso (n : ℕ) (A B : ICDA n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), σ A.init = B.init ∧ ∀ q c, σ (A.trans q c) = B.trans (σ q) c

/-- The auxiliary triangle `P(n, k)` from the conjecture. -/
def P : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | _ + 1, 1 => 1
  | n + 1, k + 1 =>
      if k + 1 = n + 1 then n * P (n + 1) k
      else if k + 1 < n + 1 then P n (k + 1) + n * P (n + 1) k
      else 0

/-- For every `n ≥ 1`, the number of isomorphism classes of initially-connected
2-input DFAs on `n` states equals `n * P(n + 1, n + 1)`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      Nat.card (Quot (icdaIso n)) = n * P (n + 1) (n + 1) := by
  sorry

end OMA.S_oeis_a006689
