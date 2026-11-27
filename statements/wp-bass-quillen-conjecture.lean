import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Bass–Quillen conjecture

Source: https://en.wikipedia.org/wiki/Bass–Quillen_conjecture
Credit: @tongenspace

The Bass–Quillen conjecture (Bass 1973, Section 4.1; Quillen 1976) asserts that for any regular
Noetherian commutative ring `A` and any `n : ℕ`, every finitely generated projective module over
the polynomial ring `A[t₁, ..., tₙ]` is extended from a finitely generated projective `A`-module,
i.e. isomorphic to `A[t₁, ..., tₙ] ⊗[A] M` for some finitely generated projective `A`-module `M`.

## Encoding

* `IsRegularRing A` is Mathlib's exact definition of a regular Noetherian commutative ring: it
  extends `IsNoetherianRing A` and requires `IsRegularLocalRing (Localization.AtPrime p)` for every
  prime ideal `p` of `A`.
* The polynomial ring `A[t₁, ..., tₙ]` is `MvPolynomial (Fin n) A`, with its canonical `A`-algebra
  structure (`MvPolynomial.C`).
* Vector bundles over a ring `R` are finitely generated projective `R`-modules
  (`[Module.Finite R P] [Module.Projective R P]`).
* Equivalence with the Wikipedia formulation `Vect_r(A) ≃ Vect_r(A[t₁, ..., tₙ])`:
  injectivity of `M ↦ A[t₁, ..., tₙ] ⊗[A] M` on isomorphism classes holds over every commutative
  ring by base change along the evaluation map `tᵢ ↦ 0`; surjectivity onto `Vect_r(A[t₁, ..., tₙ])`
  for all `r` is equivalent to every finitely generated projective `A[t₁, ..., tₙ]`-module being
  extended from a finitely generated projective `A`-module (since every regular Noetherian ring
  decomposes as a finite product of regular domains, over which every finitely generated projective
  module has constant rank).
* Following Mathlib's base-change convention, the scalar extension of an `A`-module `M` to
  `MvPolynomial (Fin n) A` is written `MvPolynomial (Fin n) A ⊗[A] M`.
-/

namespace OMA.S_wp_bass_quillen_conjecture

open scoped TensorProduct

/-- The Bass–Quillen conjecture: for every regular Noetherian commutative ring `A`, every `n : ℕ`,
and every finitely generated projective `A[t₁, ..., tₙ]`-module `P`, there exists a finitely
generated projective `A`-module `M` such that `P ≃ₗ[A[t₁, ..., tₙ]] A[t₁, ..., tₙ] ⊗[A] M`. -/
theorem main :
    ∀ (A : Type) [CommRing A] [IsRegularRing A] (n : ℕ)
      (P : Type) [AddCommGroup P] [Module (MvPolynomial (Fin n) A) P]
      [Module.Finite (MvPolynomial (Fin n) A) P]
      [Module.Projective (MvPolynomial (Fin n) A) P],
      ∃ (M : Type) (_ : AddCommGroup M) (_ : Module A M),
        Module.Finite A M ∧ Module.Projective A M ∧
        Nonempty (P ≃ₗ[MvPolynomial (Fin n) A] MvPolynomial (Fin n) A ⊗[A] M) := by
  sorry

end OMA.S_wp_bass_quillen_conjecture
