import Mathlib

/-!
# Comparison of principal diagonals of two positive definite matrix

Source: https://mathoverflow.net/questions/269499
Credit: @ivillar

Status: false as stated. A comment on the question says that there are counterexamples already
for `k = 3` with `X = [1 2; 1 1; 1 1]`. A concrete one: with this `X`, `D₁ = D₃ = diag(1, 1, 2)`
and `D₂ = I`, the `[1,1]` entry on the left is `11/2` while the one on the right is `6`. The
statement is kept as the target of a disproof.

Let us consider a matrix with positive elements: ${\bf X}^{k\times2}=[X_1:\ldots:X_k]^T$ with
$X_i=(1,X_{1i})^T$, $i=1,\ldots,k$. Also consider ${\bf X}^{(-1)}$ as the Moore-Penrose inverse
of ${\bf X}$ and the projection matrix $P_X={\bf X}{\bf X}^{(-1)}$. Let us consider three
$k\times k$ diagonal matrices with positive elements, denoted $D_1,D_2$ and $D_3$. Then is it
always true that
$$[{\bf X}^TD_1P_XD_2P_X^TD_3{\bf X}]_{[1,1]}\geq[{\bf X}^TD_1D_2D_3{\bf X}]_{[1,1]}$$
and
$$[{\bf X}^TD_1P_XD_2P_X^TD_3{\bf X}]_{[2,2]}\geq[{\bf X}^TD_1D_2D_3{\bf X}]_{[2,2]},$$
where $M_{[1,1]}$ is the $[1,1]$ element of $M$?

Formalization notes:
* `designMatrix x` is the `k × 2` matrix with rows `(1, x i)`, `x i > 0`.
* `P_X = X X⁺` is the orthogonal projection onto the column space of `X`. It is specified by
  the properties that characterize it: `P` is symmetric and idempotent, `P X = X`, and
  `P = X Y` for some matrix `Y`.
* The two inequalities are the cases `j = 0` and `j = 1` of the conclusion.
-/

namespace OMA.S_mo_269499

open Matrix

/-- The `k × 2` matrix with rows `(1, x i)`. -/
def designMatrix {k : ℕ} (x : Fin k → ℝ) : Matrix (Fin k) (Fin 2) ℝ :=
  Matrix.of fun i j => if j = 0 then 1 else x i

theorem main : ∀ (k : ℕ) (x : Fin k → ℝ), (∀ i, 0 < x i) →
    ∀ P : Matrix (Fin k) (Fin k) ℝ, Pᵀ = P → P * P = P →
      P * designMatrix x = designMatrix x →
      (∃ Y : Matrix (Fin 2) (Fin k) ℝ, P = designMatrix x * Y) →
      ∀ d₁ d₂ d₃ : Fin k → ℝ, (∀ i, 0 < d₁ i) → (∀ i, 0 < d₂ i) → (∀ i, 0 < d₃ i) →
        ∀ j : Fin 2,
          ((designMatrix x)ᵀ * diagonal d₁ * diagonal d₂ * diagonal d₃ * designMatrix x) j j ≤
            ((designMatrix x)ᵀ * diagonal d₁ * P * diagonal d₂ * Pᵀ * diagonal d₃ *
              designMatrix x) j j := by
  sorry

end OMA.S_mo_269499
