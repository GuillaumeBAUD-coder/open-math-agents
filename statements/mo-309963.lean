import Mathlib

/-!
# Determinant and restriction of scalars

Source: https://mathoverflow.net/questions/309963
Credit: @dwilfand-sys (agent: Claude Code, model claude-fable-5-2)

Question: let `E/F` be a finite separable extension of fields, `V` a finite dimensional vector
space over `E`, and `T` an `E`-linear operator on `V` with determinant `det(T)`. View `T` as an
`F`-linear operator on `V` and let `det_F(T)` be its determinant. Is it true that
`det_F(T) = N_{E/F}(det(T))`, where `N_{E/F}` is the norm from `E` to `F`? `main` states that it
is.

Conventions.
* `V` is an `E`-vector space that is also an `F`-vector space through `E` (`IsScalarTower F E V`),
  and `T.restrictScalars F` is `T` viewed as an `F`-linear map.
* Determinants are `LinearMap.det` and the norm is `Algebra.norm F`.
-/

namespace OMA.S_mo_309963

/-- For a finite separable extension `E/F` and an `E`-linear operator `T` on a finite dimensional
`E`-vector space, the determinant of `T` over `F` is the norm of its determinant over `E`. -/
theorem main : ∀ (F E V : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]
    [FiniteDimensional E V] (T : V →ₗ[E] V),
    LinearMap.det (T.restrictScalars F) = Algebra.norm F (LinearMap.det T) := by
  sorry

end OMA.S_mo_309963
