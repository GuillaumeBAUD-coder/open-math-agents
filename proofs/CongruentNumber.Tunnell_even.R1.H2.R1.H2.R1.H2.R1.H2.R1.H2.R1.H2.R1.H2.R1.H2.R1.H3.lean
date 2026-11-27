import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1
import Mathlib

/-! A prime of ramification index one has a common uniformizer in the two completed valuation rings. -/
namespace TunnellUnramifiedCompletion
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero
open scoped Classical ValuativeRel

private theorem generator {D : Type} [Field D] [NumberField D] (v : HeightOneSpectrum (𝓞 D))
    [ValuativeRel (v.adicCompletion D)] [(Valued.v : Valuation (v.adicCompletion D) ℤᵐ⁰).Compatible]
    (x : 𝒪[v.adicCompletion D]) (hx : Valued.v (x : v.adicCompletion D) = exp (-1 : ℤ)) :
    Ideal.span {x} = maximalIdeal 𝒪[v.adicCompletion D] := by
  let K := v.adicCompletion D
  let e : 𝒪[K] ≃+* v.adicCompletionIntegers D := RingEquiv.restrict (RingEquiv.refl K) 𝒪[K]
    (v.adicCompletionIntegers D).toSubring (fun y => by
      change ValuativeRel.valuation K y ≤ 1 ↔ Valued.v y ≤ 1
      exact (Valuation.vle_one_iff (ValuativeRel.valuation K)).symm.trans (Valuation.vle_one_iff Valued.v))
  have hu : (Valued.v : Valuation K ℤᵐ⁰).IsUniformizer (e x) := by
    rw [Valuation.IsUniformizer.iff, Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective D)]
    exact hx
  apply e.idealComapOrderIso.symm.injective
  change (Ideal.span {x}).map e.toRingHom = (maximalIdeal _).map e.toRingHom
  rw [Ideal.map_span, Set.image_singleton]
  exact hu.is_generator.symm.trans (map_ringEquiv_maximalIdeal e).symm

theorem indices : OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1.H3 := by
  intro D N _ _ _ _ _ _ _ v t ht
  dsimp only
  intro f _ hc hK hL he hr
  let K := v.adicCompletion D
  let L := t.adicCompletion N
  letI : Algebra K L := f.toAlgebra
  letI : ValuativeRel K := ValuativeRel.ofValuation (Valued.v : Valuation K ℤᵐ⁰)
  letI : ValuativeRel L := ValuativeRel.ofValuation (Valued.v : Valuation L ℤᵐ⁰)
  letI : (Valued.v : Valuation K ℤᵐ⁰).Compatible := Valuation.Compatible.ofValuation _
  letI : (Valued.v : Valuation L ℤᵐ⁰).Compatible := Valuation.Compatible.ofValuation _
  letI : IsNonarchimedeanLocalField K := hK
  letI : IsNonarchimedeanLocalField L := hL
  letI : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L) := he

  letI : t.asIdeal.LiesOver v.asIdeal := ht
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer D
  have hv : Valued.v (algebraMap D K π) = exp (-1:ℤ) := (v.valuedAdicCompletion_eq_valuation' π).trans hπ
  have hle : algebraMap D K π ∈ 𝒪[K] := by
    change ValuativeRel.valuation K _ ≤ 1
    rw [← Valuation.vle_one_iff, Valuation.vle_one_iff (Valued.v : Valuation K ℤᵐ⁰), hv]
    exact (exp_le_exp.mpr (by decide : (-1:ℤ) ≤ 0)).trans_eq exp_zero
  let r : 𝒪[K] := ⟨algebraMap D K π, hle⟩
  let r' : 𝒪[L] := algebraMap 𝒪[K] 𝒪[L] r
  have htπ : t.valuation N (algebraMap D N π) = exp (-1:ℤ) := by
    have h := valuation_liesOver N v t π
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot, hr, pow_one, hπ] at h
    exact h.symm
  have hL : Valued.v (r' : L) = exp (-1:ℤ) := by
    change Valued.v (f (algebraMap D K π)) = _
    exact (congrArg (fun b : L => Valued.v b) (hc π)).trans ((t.valuedAdicCompletion_eq_valuation' (algebraMap D N π)).trans htπ)
  have sb := generator v r hv
  have st := generator t r' hL
  have mb : maximalIdeal 𝒪[K] ≠ ⊥ := by
    rw [← sb, ne_eq, Ideal.span_singleton_eq_bot]
    intro hr₀
    have hzero : algebraMap D K π = 0 := congrArg Subtype.val hr₀
    rw [hzero, map_zero] at hv
    exact exp_ne_zero hv.symm
  have mapped : (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] 𝒪[L]) = maximalIdeal 𝒪[L] := by
    rw [← sb, Ideal.map_span, Set.image_singleton]
    exact st
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx _ _ mb, ← mapped]
  exact Ideal.ramificationIdx'_map_self_eq_one (by rw [mapped]; exact Ideal.IsMaximal.ne_top inferInstance)
    (Ideal.map_ne_bot_of_ne_bot mb)

end TunnellUnramifiedCompletion

theorem OMA.solution : OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1.H3 := TunnellUnramifiedCompletion.indices
