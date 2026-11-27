import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1
import Mathlib

/-!
A global integer unit gives a unit in the local valuation ring. The ramification
index of a prime determines that of the corresponding completed extension.
The norm on integer units of a finite unramified local extension is surjective.
-/
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1
open NumberField IsDedekindDomain IsLocalRing
open scoped Classical NumberField ValuativeRel WithZero

def H1 : Prop :=
  ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]],
    (maximalIdeal 𝒪[L]).ramificationIdx 𝒪[K] = 1 →
    ∀ u : 𝒪[K]ˣ, ∃ y : Lˣ, Algebra.norm K (y : L) = (u.val : K)

def H2 : Prop :=
  ∀ (D N : Type) [Field D] [NumberField D] [Field N] [NumberField N] [Algebra D N]
    [FiniteDimensional D N] [IsAbelianGalois D N],
  ∀ (v : HeightOneSpectrum (𝓞 D)) (t : HeightOneSpectrum (𝓞 N)),
    t.asIdeal.LiesOver v.asIdeal → t.asIdeal.ramificationIdx (𝓞 D) = 1 →
    let V := v.adicCompletion D
    let W := t.adicCompletion N
    ∀ f : V →+* W, Continuous f →
      (∀ c : D, f (algebraMap D V c) = algebraMap N W (algebraMap D N c)) →
      letI : Algebra V W := f.toAlgebra
      letI : ValuativeRel V := ValuativeRel.ofValuation (Valued.v : Valuation V ℤᵐ⁰)
      letI : ValuativeRel W := ValuativeRel.ofValuation (Valued.v : Valuation W ℤᵐ⁰)
      IsNonarchimedeanLocalField V ∧ IsNonarchimedeanLocalField W ∧
        FiniteDimensional V W ∧ IsGalois V W ∧
        ∃ e : Valuation.HasExtension (ValuativeRel.valuation V) (ValuativeRel.valuation W),
          letI := e
          IsIntegralClosure 𝒪[W] 𝒪[V] W ∧ Module.Finite 𝒪[V] 𝒪[W] ∧
            (maximalIdeal 𝒪[W]).ramificationIdx 𝒪[V] = 1

def H3 : Prop :=
  ∀ (D : Type) [Field D] [NumberField D] (v : HeightOneSpectrum (𝓞 D)) (u : (𝓞 D)ˣ),
    let V := v.adicCompletion D
    letI : ValuativeRel V := ValuativeRel.ofValuation (Valued.v : Valuation V ℤᵐ⁰)
    ∃ a : 𝒪[V]ˣ, (a.val : V) = algebraMap D V u.val.val

theorem main : H1 → H2 → H3 → OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1.H2 := by
  intro norms completed integral D N _ _ _ _ _ _ _ v t ht e
  dsimp only
  intro f hf hc u
  let V := v.adicCompletion D
  let W := t.adicCompletion N
  letI : Algebra V W := f.toAlgebra
  letI : ValuativeRel V := ValuativeRel.ofValuation (Valued.v : Valuation V ℤᵐ⁰)
  letI : ValuativeRel W := ValuativeRel.ofValuation (Valued.v : Valuation W ℤᵐ⁰)
  obtain ⟨hV,hW,hfd,hg,he,hc',hfin,hidx⟩ := completed D N v t ht e f hf hc
  obtain ⟨a, ha⟩ := integral D v u
  obtain ⟨y, hy⟩ := @norms V W _ _ _ hV _ _ _ _ hW _ hfd hg he hc' hfin hidx a
  exact ⟨y, hy.trans ha⟩

end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1

