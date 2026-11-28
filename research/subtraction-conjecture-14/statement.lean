/-
Additive three-action friendly/antagonistic discrepancies and their first heap.
Source: Bhagat, Kulkarni, Larsson and Murali, arXiv:2510.24280v2,
Definition 2 and Conjecture 14. https://arxiv.org/abs/2510.24280

Put a=s3, b=s2, and s1=a+b, with positive ordered actions a<b. A discrepancy
exists exactly when b/a is not an integer. In that case the positive interval
index n satisfies n*a<b<(n+1)*a, and the least distinguishing heap is
(n+2)*b+n*(a+b). The division condition a does not divide b is equivalent
to the source's noninteger ratio because a>0.

This is a separate proposed target for Conjecture 14, not the existing
Conjecture 4 target. Human registration and statement review are required.
The generic step/outcome bodies are copied exactly from the approved model.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Filter

namespace OMA.S_arxiv_2510_24280_conjecture14

/-- One application of the recurrence of Definition 2 at heap `h`, for a mover who is friendly
(`friendly = true`) or antagonistic, where `prev k` is the outcome at the smaller heap `k`, seen from the
player who moves there. The result is (mover's total, other player's total). -/
def step (S : Finset ℕ) (friendly : Bool) (h : ℕ) (prev : ℕ → ℕ × ℕ) : ℕ × ℕ :=
  let moves := S.filter (fun s => s ≤ h)
  let mine : ℕ → ℕ := fun s => s + (prev (h - s)).2
  let theirs : ℕ → ℕ := fun s => (prev (h - s)).1
  let best := moves.sup mine
  let ties := moves.filter (fun s => mine s = best)
  (best,
    if friendly then ties.sup theirs
    else if hne : ties.Nonempty then ties.inf' hne theirs else 0)

/-- The outcome `o_X(h)` of the source: (total of the player to move, total of the other player) at heap
`h`, the player to move following convention `c₁` and the other player `c₂`. -/
def outcome (S : Finset ℕ) (c₁ c₂ : Bool) (h : ℕ) : ℕ × ℕ :=
  step S c₁ h (fun k => if _ : k < h then outcome S c₂ c₁ k else (0, 0))
termination_by h


theorem main : ∀ a b : ℕ,0<a → a<b →
    ((∃ h : ℕ,outcome {a,b,a+b} true true h≠
      outcome {a,b,a+b} false false h) ↔ ¬a∣b) ∧
    (¬a∣b → ∃ n : ℕ,0<n ∧ n*a<b ∧ b<(n+1)*a ∧
      IsLeast {h : ℕ | outcome {a,b,a+b} true true h≠
        outcome {a,b,a+b} false false h}
        ((n+2)*b+n*(a+b))) := by
  sorry

end OMA.S_arxiv_2510_24280_conjecture14
