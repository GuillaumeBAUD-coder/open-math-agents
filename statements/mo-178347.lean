import Mathlib

/-!
# On increasing the penalty term in convex optimization with regularization

Source: https://mathoverflow.net/questions/178347 (asked in 2014; no answer in the MathOverflow data
dump of 30 September 2026).
Credit: @ricnov

The source. Given the two strictly convex (unique solution) optimization problems

  Problem 1: `min_X f(X) + ‖X‖_F ^ 2`,        Problem 2: `min_X f(X) + n ‖X‖_2 ^ 2`,

where `X ∈ S_{++}^n` (being positive definite), `f(X)` is strictly convex, `‖·‖_F` is the Frobenius
norm and `‖·‖_2` is the spectral norm, let `X₁` and `X₂` denote the solutions to Problem 1 and
Problem 2, respectively. Question: prove that `f(X₁) ≤ f(X₂)` (or provide a counterexample if this
does not always hold).

`main` states that the inequality always holds; a disproof is a counterexample.

Translation choices.
* `S_{++}^n` is the set of real `n × n` matrices that are positive definite (`Matrix.PosDef`, which
  includes symmetry).
* `f` is a real-valued function of a matrix that is strictly convex on `S_{++}^n` (`StrictConvexOn`).
* `‖X‖_F ^ 2` is written out as the sum of the squares of the entries of `X`.
* `‖X‖_2` is the operator norm of `X` acting on Euclidean space, i.e. the largest singular value:
  Mathlib's norm on matrices from the scope `Matrix.Norms.L2Operator`.
* `X₁` (respectively `X₂`) is a solution of Problem 1 (respectively Problem 2): it is positive
  definite and minimises the objective over `S_{++}^n`. By strict convexity each problem has at most
  one solution; that the two solutions exist is a hypothesis, as in the source.
-/

namespace OMA.S_mo_178347

open scoped Matrix.Norms.L2Operator

theorem main : ∀ (n : ℕ) (f : Matrix (Fin n) (Fin n) ℝ → ℝ),
    StrictConvexOn ℝ {X : Matrix (Fin n) (Fin n) ℝ | X.PosDef} f →
    ∀ X₁ X₂ : Matrix (Fin n) (Fin n) ℝ, X₁.PosDef → X₂.PosDef →
      (∀ Y : Matrix (Fin n) (Fin n) ℝ, Y.PosDef →
        f X₁ + ∑ i, ∑ j, X₁ i j ^ 2 ≤ f Y + ∑ i, ∑ j, Y i j ^ 2) →
      (∀ Y : Matrix (Fin n) (Fin n) ℝ, Y.PosDef →
        f X₂ + n * ‖X₂‖ ^ 2 ≤ f Y + n * ‖Y‖ ^ 2) →
      f X₁ ≤ f X₂ := by
  sorry

end OMA.S_mo_178347
