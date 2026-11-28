import Mathlib

-- SIC-POVM: do SIC-POVMs exist in all dimensions?
-- Source: https://en.wikipedia.org/wiki/SIC-POVM (section Definition, unsolved-problem box)
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
The source defines a SIC-POVM over a `d`-dimensional Hilbert space as a set of `d^2` rank-1
projectors `Π_1, ..., Π_{d^2}` with `Tr(Π_i Π_j) = (d δ_ij + 1) / (d + 1)`; the POVM is then
`F_i = Π_i / d`. The open problem asks whether such a family exists in every dimension `d`.

Conventions:
* The `d`-dimensional complex Hilbert space is `ℂ^d`, so operators are `d × d` complex matrices.
* A rank-1 projector is an orthogonal projection (Hermitian and idempotent) of rank one,
  as in the quantum-information usage of the source.
* Dimensions are `d ≥ 1`.
-/

namespace OMA.S_wp_sic_povm

/-- A SIC in dimension `d`: `d^2` rank-1 orthogonal projectors on `ℂ^d` whose pairwise
Hilbert–Schmidt inner products are `Tr(P_i P_j) = (d δ_ij + 1) / (d + 1)`. -/
def IsSIC (d : ℕ) (P : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ i, (P i).IsHermitian ∧ P i * P i = P i ∧ (P i).rank = 1) ∧
    ∀ i j, (P i * P j).trace = ((d : ℂ) * (if i = j then 1 else 0) + 1) / ((d : ℂ) + 1)

/-- SIC-POVMs exist in every finite dimension `d ≥ 1`. -/
theorem main : ∀ d : ℕ, 1 ≤ d → ∃ P : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ, IsSIC d P := by
  sorry

end OMA.S_wp_sic_povm
