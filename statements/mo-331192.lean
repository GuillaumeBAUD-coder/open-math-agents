import Mathlib

/-!
# Bounds for the finitistic dimension

Question by Mare (MathOverflow, CC BY-SA): https://mathoverflow.net/questions/331192
Credit: @my-other-github-account

We read the module convention in light of the cited radical-cube bound
(doi:10.1006/jabr.1993.1205). Huisgen-Zimmermann restates it in arXiv:1407.2383,
p. 8, for the little finitistic dimension defined on p. 2. Bounding this supremum
is equivalent to bounding each finitely generated left module of finite projective dimension.
-/

namespace OMA.S_mo_331192

open CategoryTheory

universe u v

theorem main :
    ∀ (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A]
    [FiniteDimensional k A] (r : ℕ), 3 ≤ r →
    (Ideal.jacobson (⊥ : Ideal A)) ^ r = ⊥ → ∀ (M : ModuleCat.{v} A), Module.Finite A M →
    (∃ n : ℕ, HasProjectiveDimensionLE M n) →
    HasProjectiveDimensionLE M (Module.finrank k A ^ (r - 1) + 1) := by
  sorry

end OMA.S_mo_331192
