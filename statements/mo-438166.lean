import Mathlib

/-!
# Finitistic dimension conjecture — why artin algebras?

Source: https://mathoverflow.net/questions/438166
Credit: @my-other-github-account

The question asks whether there is a ring `A`, finitely generated over a commutative Noetherian
ring `K` of finite Krull dimension, such that `A` has infinite finitistic dimension.

Conventions, following the setting of the finitistic dimension conjecture for Artin algebras that
the source quotes:
- `A` finitely generated over `K` is read as an Artin-algebra-style `K`-algebra which is finitely
  generated as a `K`-module (`Module.Finite K A`).
- finite Krull dimension is `ringKrullDim K < ⊤`.
- the finitistic dimension is the little finitistic dimension of left `A`-modules: the supremum of
  the projective dimensions of finitely generated `A`-modules of finite projective dimension.
  Infinite means this supremum is `⊤`.

The definition of `littleFinitisticDimension` is adapted from OpenAI, openai/math (Apache-2.0),
commit 3344da59991ed94f9ba711217b29c1d760badfa6, lean/ComparatorChallenges/LittleFinitistic.lean.
The question is stated as the existence of such a pair `K`, `A`.
-/

namespace OMA.S_mo_438166

noncomputable section

open CategoryTheory

universe u

/-- The little finitistic dimension of a ring `A`: the supremum of the projective dimensions of
the finitely generated left `A`-modules whose projective dimension is finite. -/
def littleFinitisticDimension (A : Type u) [Ring A] : WithBot ℕ∞ :=
  ⨆ (M : ModuleCat.{u} A) (_ : Module.Finite A M) (_ : projectiveDimension M < ⊤),
    projectiveDimension M

theorem main :
    ∃ (K : Type) (_ : CommRing K) (A : Type) (_ : Ring A) (_ : Algebra K A),
      IsNoetherianRing K ∧ ringKrullDim K < ⊤ ∧ Module.Finite K A ∧
        littleFinitisticDimension A = ⊤ := by
  sorry

end

end OMA.S_mo_438166
