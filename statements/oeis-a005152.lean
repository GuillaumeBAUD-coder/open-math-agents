import Mathlib

/-!
# A005152: Maximum Rotation Distance Between Binary Trees

Source: https://oeis.org/A005152
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

A005152(n) is the maximum rotation distance between any two binary trees with `n` internal nodes.

Conjecture (Sleator, Tarjan, Thurston): `A005152(n) = 2 * n - 6` for all `n ≥ 11`.
-/

namespace OMA.S_oeis_a005152

/-- Binary trees with internal nodes. -/
inductive BinTree
  | leaf
  | node (l r : BinTree)

/-- Number of internal nodes in a binary tree. -/
def BinTree.size : BinTree → ℕ
  | .leaf => 0
  | .node l r => 1 + l.size + r.size

/-- Single left or right rotation step at any node in a binary tree. -/
inductive RotStep : BinTree → BinTree → Prop
  | rotRight (a b c : BinTree) :
      RotStep (.node (.node a b) c) (.node a (.node b c))
  | rotLeft (a b c : BinTree) :
      RotStep (.node a (.node b c)) (.node (.node a b) c)
  | inLeft {l l' r : BinTree} :
      RotStep l l' → RotStep (.node l r) (.node l' r)
  | inRight {l r r' : BinTree} :
      RotStep r r' → RotStep (.node l r) (.node l r')

/-- `RotSteps k t₁ t₂` holds if `t₂` is reachable from `t₁` in `k` rotation steps. -/
inductive RotSteps : ℕ → BinTree → BinTree → Prop
  | refl (t : BinTree) : RotSteps 0 t t
  | step {k : ℕ} {t₁ t₂ t₃ : BinTree} :
      RotStep t₁ t₂ → RotSteps k t₂ t₃ → RotSteps (k + 1) t₁ t₃

/-- Minimum number of rotations to transform `t₁` into `t₂`. -/
noncomputable def rotDist (t₁ t₂ : BinTree) : ℕ :=
  sInf { k : ℕ | RotSteps k t₁ t₂ }

/-- Maximum rotation distance among all binary trees with `n` internal nodes. -/
noncomputable def maxRotDist (n : ℕ) : ℕ :=
  sSup { d : ℕ | ∃ t₁ t₂ : BinTree, t₁.size = n ∧ t₂.size = n ∧ rotDist t₁ t₂ = d }

theorem main :
    ∀ n : ℕ, 11 ≤ n → maxRotDist n = 2 * n - 6 := by
  sorry

end OMA.S_oeis_a005152
