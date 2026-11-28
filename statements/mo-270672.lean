import Mathlib

/-!
# There are just two possibilities for matrices in $M_n(\mathbb{F}_p)$?

Source: https://mathoverflow.net/questions/270672
Credit: @ivillar

Status: false as stated. The matrix `A = diag(1, 0)` is not orthogonal, and it is not completely
non-orthogonal either: `P = A` is a nonzero projection with `P A = A P` and
`P Aᵀ A = P A Aᵀ = P`. This counterexample is given in the comments to the question. The
statement is kept as the target of a disproof.

Let $p$ be a prime number and consider the *-ring $M_n(\mathbb{F}_p)$, the $n\times n$
matrices over the finite field $\mathbb{F}_p$ (the involution is just the transpose).

Q. True or false: Every matrix $A\in M_n(\mathbb{F}_p)$ is orthogonal or completely
non-orthogonal!

* A matrix $A$ is called orthogonal if $A^*A=AA^*=id$.
* A matrix $A$ is called completely non-orthogonal if there is no non-zero projection $P$ such
  that $PA=AP$ and $PA^*A=PAA^*=P$.

Formalization notes:
* `𝔽_p` is `ZMod p` for a prime `p`, and `A^*` is the transpose.
* A projection in the *-ring is a self-adjoint idempotent: `P * P = P` and `Pᵀ = P`.
-/

namespace OMA.S_mo_270672

open Matrix

/-- `A` is orthogonal: `Aᵀ A = A Aᵀ = 1`. -/
def IsOrthogonal {p n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod p)) : Prop :=
  Aᵀ * A = 1 ∧ A * Aᵀ = 1

/-- `A` is completely non-orthogonal: no nonzero projection `P` commutes with `A` and satisfies
`P Aᵀ A = P A Aᵀ = P`. -/
def IsCompletelyNonOrthogonal {p n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod p)) : Prop :=
  ¬ ∃ P : Matrix (Fin n) (Fin n) (ZMod p), P ≠ 0 ∧ P * P = P ∧ Pᵀ = P ∧ P * A = A * P ∧
    P * (Aᵀ * A) = P ∧ P * (A * Aᵀ) = P

theorem main : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (A : Matrix (Fin n) (Fin n) (ZMod p)),
    IsOrthogonal A ∨ IsCompletelyNonOrthogonal A := by
  sorry

end OMA.S_mo_270672
