/-
Dominant-extension inheritance for self-interest cumulative subtraction games.
Source: Bhagat, Kulkarni, Larsson and Murali, arXiv:2510.24280v2,
Definition 2 and Conjecture 13. https://arxiv.org/abs/2510.24280

For positive ordered moves a<b<c with c>=2b, all-heaps agreement of the
friendly/friendly and antagonistic/antagonistic games on {a,b} implies the
same agreement on {a,b,c}. This is separate from Conjecture 4 and the other
conjectures of that paper. The finite-set game definitions below are copied
exactly from the approved Definition 2 translation, under this new namespace.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Filter

namespace OMA.S_arxiv_2510_24280_conjecture13

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


/-- Conjecture 13: a dominant third move preserves all-heaps symmetric
friendly/antagonistic agreement of the two-move game. -/
theorem main : ∀ a b c : ℕ, 0<a → a<b → b<c → 2*b≤c →
    (∀ h, outcome {a,b} true true h=outcome {a,b} false false h) →
    ∀ h, outcome {a,b,c} true true h=outcome {a,b,c} false false h := by
  sorry

end OMA.S_arxiv_2510_24280_conjecture13
