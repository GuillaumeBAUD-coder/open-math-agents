import Mathlib

/-!
# Midsquare with natural sides and diagonal

Source: https://math.stackexchange.com/questions/4806891/does-there-exist-a-midsquare-with-natural-sides-and-diagonal
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

A midsquare is an orthodiagonal and equidiagonal quadrilateral (diagonals are perpendicular
and have equal length). Are there positive integers $a, b, c, d, e$ such that there exists
a convex midsquare with side lengths $a, b, c, d$ and diagonal length $e$?

Conventions:
- Vertices are points in $\mathbb{R}^2$ (`ℝ × ℝ`), with consecutive sides $P_1 P_2, P_2 P_3,
  P_3 P_4, P_4 P_1$ of lengths $a, b, c, d$ and diagonals $P_1 P_3, P_2 P_4$ of length $e$.
- Convexity is expressed by requiring the two open diagonal segments to intersect.
-/

namespace OMA.S_mse_4806891

/-- Squared Euclidean distance between two points in $\mathbb{R}^2$. -/
def sqDist (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Four points in $\mathbb{R}^2$ form a convex midsquare with sides `a, b, c, d` and diagonal `e`. -/
def IsMidsquare (P₁ P₂ P₃ P₄ : ℝ × ℝ) (a b c d e : ℕ) : Prop :=
  sqDist P₁ P₂ = (a : ℝ) ^ 2 ∧
  sqDist P₂ P₃ = (b : ℝ) ^ 2 ∧
  sqDist P₃ P₄ = (c : ℝ) ^ 2 ∧
  sqDist P₄ P₁ = (d : ℝ) ^ 2 ∧
  sqDist P₁ P₃ = (e : ℝ) ^ 2 ∧
  sqDist P₂ P₄ = (e : ℝ) ^ 2 ∧
  (P₃.1 - P₁.1) * (P₄.1 - P₂.1) + (P₃.2 - P₁.2) * (P₄.2 - P₂.2) = 0 ∧
  ∃ t s : ℝ, 0 < t ∧ t < 1 ∧ 0 < s ∧ s < 1 ∧
    (1 - t) * P₁.1 + t * P₃.1 = (1 - s) * P₂.1 + s * P₄.1 ∧
    (1 - t) * P₁.2 + t * P₃.2 = (1 - s) * P₂.2 + s * P₄.2

theorem main :
    ∃ (a b c d e : ℕ) (P₁ P₂ P₃ P₄ : ℝ × ℝ),
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧
      IsMidsquare P₁ P₂ P₃ P₄ a b c d e := by
  sorry

end OMA.S_mse_4806891
