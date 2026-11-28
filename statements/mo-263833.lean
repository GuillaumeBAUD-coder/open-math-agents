import Mathlib

/-!
# Quantum coupon collection

Source: https://mathoverflow.net/questions/263833 (CC BY-SA 4.0).

For symmetric positive definite `X_1, …, X_n ∈ S^d_{++}` let
`Q_n(X_1, …, X_n) = ∑_{k=1}^n (-1)^(k+1) ∑_{i_1 < ⋯ < i_k} (X_{i_1} + ⋯ + X_{i_k})^(-1)`
(for commuting matrices this is the coupon collector's expected waiting time). Conjecture: for
`n ≥ 1`, `Q_n(X_1, …, X_n) ≻ 0`.

We state the conjecture.

Formalization notes:
* The inner sums run over nonempty `s ⊆ Fin n` with sign `(-1)^(|s|+1)`; `⁻¹` is the matrix inverse.
* Over `ℝ`, `Matrix.PosDef` means symmetric positive definite.
* Checked numerically on 3000 random instances (`2 ≤ n ≤ 6`, `d = 2, 3`, widely varying scales): the
  smallest eigenvalue of `Q_n` was always positive.
-/

namespace OMA.S_mo_263833

/-- The alternating sum of inverses of subset sums of positive definite matrices is positive definite. -/
theorem main : ∀ (n d : ℕ), 1 ≤ n → ∀ X : Fin n → Matrix (Fin d) (Fin d) ℝ, (∀ i, (X i).PosDef) →
    (∑ s ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun s => s.Nonempty),
      ((-1 : ℝ) ^ (s.card + 1)) • (∑ i ∈ s, X i)⁻¹).PosDef := by
  sorry

end OMA.S_mo_263833
