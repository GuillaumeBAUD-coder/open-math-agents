import Mathlib

/-!
# Properties of one dimensional null space

Source: https://mathoverflow.net/questions/251630
Credit: @JeremyDevs

Question (MathOverflow 251630, 2016). Let `G` denote the set of all `3 × 3` real symmetric
matrices and let `G⁺` denote the set of all `3 × 3` positive semidefinite matrices. Let
`S : G → G` be a linear transformation satisfying the conditions `S² = S` and `S(G⁺) ⊆ G⁺`.
Suppose `dim N(S) = 1`, where `N(S)` denotes the null space of `S`. Can we find a non-zero
positive semidefinite matrix in `N(S)`?

The answer is yes, and `main` states it. Sketch: let `R` span `N(S)`. Since `S(SA - A) = 0`,
`S A = A + φ(A) R` for a linear functional `φ`, and `φ(R) = -1`. If neither `R` nor `-R` is
positive semidefinite, there are `x, y` with `xᵀRx > 0 > yᵀRy`. For a vector `v` orthogonal to
some `x', y'` with `x'ᵀRx' > 0 > y'ᵀRy'`, positivity of `S(vvᵀ) = vvᵀ + φ(vvᵀ) R` on `x'` and
`y'` forces `φ(vvᵀ) = 0`. In dimension `3` such `v` form a nonempty open set (it contains the
cross product of `x` and `y`), so the quadratic form `v ↦ φ(vvᵀ)` vanishes identically, hence
`φ = 0`, contradicting `φ(R) = -1`. (The dimension matters: the analogous statement for `2 × 2`
matrices is false.)

Conventions:
* `G` is the real vector space `Sym3` of symmetric matrices in `Matrix (Fin 3) (Fin 3) ℝ`
  (a `Submodule`), and `S : Sym3 →ₗ[ℝ] Sym3`.
* `S² = S` is `S ∘ₗ S = S`; positive semidefinite is Mathlib's `Matrix.PosSemidef`;
  `S(G⁺) ⊆ G⁺` says `S A` is positive semidefinite whenever `A` is.
* `dim N(S) = 1` is `Module.finrank ℝ (LinearMap.ker S) = 1`.
-/

namespace OMA.S_mo_251630

/-- The real vector space `G` of symmetric `3 × 3` real matrices. -/
def Sym3 : Submodule ℝ (Matrix (Fin 3) (Fin 3) ℝ) where
  carrier := {A | A.IsSymm}
  add_mem' := fun ha hb => Matrix.IsSymm.add ha hb
  zero_mem' := Matrix.isSymm_zero
  smul_mem' := fun c _ ha => Matrix.IsSymm.smul ha c

/-- A positive idempotent linear map on the symmetric `3 × 3` real matrices whose null space is
one dimensional has a nonzero positive semidefinite matrix in its null space. -/
theorem main : ∀ (S : Sym3 →ₗ[ℝ] Sym3) (hS : S ∘ₗ S = S)
    (hpos : ∀ A : Sym3, (A : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef →
      (S A : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef)
    (hker : Module.finrank ℝ (LinearMap.ker S) = 1),
    ∃ A : Sym3, A ≠ 0 ∧ S A = 0 ∧ (A : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  sorry

end OMA.S_mo_251630
