import Mathlib

/-!
# Convexity of the truncated Frobenius norm

Source: ohana, https://mathoverflow.net/questions/412654 (CC BY-SA 4.0).
Credit: @connoranderson.

Singular values are listed in decreasing order. Mathlib numbers them from
zero, so omitting the largest k leaves indices k through m−1.
-/

namespace OMA.S_mo_412654

noncomputable def tailNorm {m n : ℕ} (k : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i ∈ Finset.Ico k m, ((Matrix.toEuclideanLin A).singularValues i)^2)

theorem main : ∀ (m n k : ℕ), 0 < k →
    (ConvexOn ℝ Set.univ (tailNorm (m:=m) (n:=n) k) ↔ min m n ≤ k) := by
  sorry

end OMA.S_mo_412654
