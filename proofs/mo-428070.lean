import OMAStatements.S_mo_428070
import Mathlib

/-!
# MathOverflow 428070: no finite group algebra over `ℚ` contains a square root of `2`

Let `ε : ℚ[G] → ℚ` be the augmentation map (the algebra homomorphism induced by the trivial
character `G → ℚ`, `g ↦ 1`). If `x² = 2` in `ℚ[G]`, then `ε(x)² = ε(2) = 2` in `ℚ`,
which is impossible because `√2` is irrational. So the statement is false.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_428070.main) := by
  rintro ⟨G, group, -, x, hx⟩
  let _ : Group G := group
  -- the augmentation map
  obtain ⟨ε, -⟩ : ∃ ε : MonoidAlgebra ℚ G →ₐ[ℚ] ℚ, True :=
    ⟨MonoidAlgebra.lift ℚ ℚ G (1 : G →* ℚ), trivial⟩
  have h := congrArg ε hx
  rw [map_pow, map_ofNat] at h
  -- a rational number whose square is `2`
  have hq : ((ε x : ℚ) : ℝ) ^ 2 = 2 := by exact_mod_cast h
  refine irrational_sqrt_two ⟨|ε x|, ?_⟩
  rw [← hq, Real.sqrt_sq_eq_abs]
  push_cast
  rfl
