import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1
import Mathlib

/-!
Completing the ground field and an extension at primes lying over one another
preserves finite Galois extensions and identifies their rings of integers.
A global uniformizer at an unramified prime generates both completed maximal ideals.
-/
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1
open NumberField IsDedekindDomain IsLocalRing
open scoped Classical NumberField ValuativeRel WithZero

def H1 : Prop :=
  ∀ (D N : Type) [Field D] [NumberField D] [Field N] [NumberField N] [Algebra D N]
    [FiniteDimensional D N] [IsAbelianGalois D N],
  ∀ (v : HeightOneSpectrum (𝓞 D)) (t : HeightOneSpectrum (𝓞 N)), t.asIdeal.LiesOver v.asIdeal →
    let V := v.adicCompletion D
    let W := t.adicCompletion N
    ∀ f : V →+* W, Continuous f →
      (∀ c : D, f (algebraMap D V c) = algebraMap N W (algebraMap D N c)) →
      letI : Algebra V W := f.toAlgebra
      letI : ValuativeRel V := ValuativeRel.ofValuation (Valued.v : Valuation V ℤᵐ⁰)
      letI : ValuativeRel W := ValuativeRel.ofValuation (Valued.v : Valuation W ℤᵐ⁰)
      IsNonarchimedeanLocalField V ∧ IsNonarchimedeanLocalField W ∧
        FiniteDimensional V W ∧ IsGalois V W ∧
        Valuation.HasExtension (ValuativeRel.valuation V) (ValuativeRel.valuation W)

def H2 : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)],
    IsIntegralClosure 𝒪[L] 𝒪[K] L

def H3 : Prop :=
  ∀ (D N : Type) [Field D] [NumberField D] [Field N] [NumberField N] [Algebra D N]
    [FiniteDimensional D N] [IsAbelianGalois D N],
  ∀ (v : HeightOneSpectrum (𝓞 D)) (t : HeightOneSpectrum (𝓞 N)), t.asIdeal.LiesOver v.asIdeal →
    let V := v.adicCompletion D
    let W := t.adicCompletion N
    ∀ f : V →+* W, Continuous f →
      (∀ c : D, f (algebraMap D V c) = algebraMap N W (algebraMap D N c)) →
      letI : Algebra V W := f.toAlgebra
      letI : ValuativeRel V := ValuativeRel.ofValuation (Valued.v : Valuation V ℤᵐ⁰)
      letI : ValuativeRel W := ValuativeRel.ofValuation (Valued.v : Valuation W ℤᵐ⁰)
      ∀ [IsNonarchimedeanLocalField V] [IsNonarchimedeanLocalField W]
        [Valuation.HasExtension (ValuativeRel.valuation V) (ValuativeRel.valuation W)],
        t.asIdeal.ramificationIdx (𝓞 D) = 1 →
        (maximalIdeal 𝒪[W]).ramificationIdx 𝒪[V] = 1

theorem main : H1 → H2 → H3 → OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1.H2 := by
  intro fields integral ramification D N _ _ _ _ _ _ _ v t ht hr
  dsimp only
  intro f hf hc
  let V := v.adicCompletion D
  let W := t.adicCompletion N
  letI : Algebra V W := f.toAlgebra
  letI : ValuativeRel V := ValuativeRel.ofValuation (Valued.v : Valuation V ℤᵐ⁰)
  letI : ValuativeRel W := ValuativeRel.ofValuation (Valued.v : Valuation W ℤᵐ⁰)
  obtain ⟨hv,hw,hfd,hg,he⟩ := fields D N v t ht f hf hc
  letI : IsNonarchimedeanLocalField V := hv
  letI : IsNonarchimedeanLocalField W := hw
  letI : FiniteDimensional V W := hfd
  letI : IsGalois V W := hg
  letI : Valuation.HasExtension (ValuativeRel.valuation V) (ValuativeRel.valuation W) := he
  letI : IsIntegralClosure 𝒪[W] 𝒪[V] W := integral V W
  exact ⟨hv,hw,hfd,hg,he,inferInstance,IsIntegralClosure.finite 𝒪[V] V W 𝒪[W],
    @ramification D N _ _ _ _ _ _ _ v t ht f hf hc hv hw he hr⟩

end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1

