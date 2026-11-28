import FormalConjectures.Paper.SerreUniformity

/-!
# Reduction of Serre's uniformity conjecture over the rationals, explicit bound `C = 37`

The target is

  `∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], E.j ∉ cmJInvariants → ∀ p, p.Prime → 37 < p →
     HasFullTorsionAction E p`,

i.e. every non-CM elliptic curve over `ℚ` has surjective mod-`p` Galois representation for every
prime `p > 37` (the conjectured value `p_ℚ = 37` of Serre's question; see the introduction of
Lemos, *Serre's uniformity conjecture for elliptic curves with rational cyclic isogenies*,
arXiv:1702.01985).

The published case division of the problem is by maximal subgroups of `GL₂(𝔽_p)`: after Serre
(exceptional subgroups, *Propriétés galoisiennes des points d'ordre fini des courbes
elliptiques*, Invent. Math. 15 (1972)), Mazur (Borel subgroups: for a non-CM curve over `ℚ` the
possible prime degrees of rational isogenies are `2,3,5,7,11,13,17,37`, *Rational isogenies of
prime degree*, Invent. Math. 44 (1978)) and Bilu–Parent / Bilu–Parent–Rebolledo (normalisers of
split Cartan subgroups, *Rational points on X₀⁺(pʳ)*, 2013), the only remaining case for prime
`p > 37` is that the image is contained in the normaliser of a non-split Cartan subgroup; this is
summarised in the introduction of arXiv:1702.01985.

* `H1` is Lemos's theorem (arXiv:1702.01985, Theorem 1.1), restated in the geometric form of its
  hypothesis: a non-CM curve over `ℚ` that *admits a non-trivial cyclic `ℚ`-isogeny* — there is
  `n ≥ 2` and a Galois-stable subgroup of `E[n]` isomorphic to `ℤ/n`, the kernel of a cyclic
  `ℚ`-isogeny of degree `n` — has surjective mod-`p` representation for every prime `p > 37`.
  This is published.
* `H2` is the genuinely open part: the same conclusion for the non-CM curves that admit *no*
  non-trivial cyclic `ℚ`-isogeny.  Lemos writes of the remaining non-split Cartan case that it
  'seems, for the moment, out of reach'.

What this file proves unconditionally (no `sorry`, no new axiom, kernel-checked): `main`, the
elementary case split on whether the curve admits such an isogeny — `H1` covers the curves that
do, `H2` the curves that do not, and the two classes exhaust all curves.  It also records
`bound_37_implies_exists`: the explicit form `C = 37` implies the existence form
`serre_uniformity` of the same module.
-/

open SerreUniformity
open scoped Classical

namespace OMA.R_SerreUniformity_serre_uniformity_variants_bound_37_R1

/-- Lemos's theorem (arXiv:1702.01985, Theorem 1.1): a non-CM elliptic curve over `ℚ` that admits
a non-trivial cyclic `ℚ`-isogeny has surjective mod-`p` Galois representation for every prime
`p > 37`.  The hypothesis is spelled out geometrically: for some `n ≥ 2` there is a Galois-stable
subgroup of `E[n]` isomorphic to `ℤ/n`. -/
def H1 : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], E.j ∉ cmJInvariants →
    (∃ n : ℕ, 2 ≤ n ∧ ∃ T : AddSubgroup (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point,
      T ≤ AddSubgroup.torsionBy ((E.baseChange (AlgebraicClosure ℚ)).toAffine.Point) (n : ℤ) ∧
        Nonempty (T ≃+ ZMod n) ∧
          ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ P : T,
            WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom P.val ∈ T) →
      ∀ p : ℕ, p.Prime → 37 < p → HasFullTorsionAction E p

/-- The open core: the same conclusion for the non-CM elliptic curves over `ℚ` that admit no
non-trivial cyclic `ℚ`-isogeny.  This is exactly the case left open by Lemos's theorem; after
Mazur and Bilu–Parent–Rebolledo the remaining obstruction is an image inside the normaliser of a
non-split Cartan subgroup. -/
def H2 : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], E.j ∉ cmJInvariants →
    ¬(∃ n : ℕ, 2 ≤ n ∧ ∃ T : AddSubgroup (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point,
      T ≤ AddSubgroup.torsionBy ((E.baseChange (AlgebraicClosure ℚ)).toAffine.Point) (n : ℤ) ∧
        Nonempty (T ≃+ ZMod n) ∧
          ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ P : T,
            WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom P.val ∈ T) →
      ∀ p : ℕ, p.Prime → 37 < p → HasFullTorsionAction E p

/-- Every non-CM elliptic curve over `ℚ` either admits a non-trivial cyclic `ℚ`-isogeny or does
not, so `H1` and `H2` together give the target. -/
theorem main : H1 → H2 →
    type_of% @SerreUniformity.serre_uniformity.variants.bound_37 := by
  intro h1 h2 E hEll hj p hp h37
  haveI := hEll
  by_cases h : ∃ n : ℕ, 2 ≤ n ∧
      ∃ T : AddSubgroup (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point,
        T ≤ AddSubgroup.torsionBy ((E.baseChange (AlgebraicClosure ℚ)).toAffine.Point) (n : ℤ) ∧
          Nonempty (T ≃+ ZMod n) ∧
            ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ P : T,
              WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom P.val ∈ T
  · exact h1 E hj h p hp h37
  · exact h2 E hj h p hp h37

/-- The explicit form with `C = 37` implies the existence form of Serre's uniformity question over
`ℚ` stated in the same module. -/
lemma bound_37_implies_exists :
    type_of% @SerreUniformity.serre_uniformity.variants.bound_37 →
      type_of% @SerreUniformity.serre_uniformity := by
  intro h
  exact ⟨37, h⟩

end OMA.R_SerreUniformity_serre_uniformity_variants_bound_37_R1
