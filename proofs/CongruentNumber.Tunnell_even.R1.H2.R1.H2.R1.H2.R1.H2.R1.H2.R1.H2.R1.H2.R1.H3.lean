import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1
import Mathlib

/-! A global integral unit maps to a unit of the valuation ring of every finite completion. -/
open NumberField IsDedekindDomain
open scoped Classical NumberField ValuativeRel WithZero

theorem OMA.solution : OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1.H3 := by
  intro D _ _ v u
  let K := v.adicCompletion D
  letI : ValuativeRel K := ValuativeRel.ofValuation (Valued.v : Valuation K ℤᵐ⁰)
  letI : (Valued.v : Valuation K ℤᵐ⁰).Compatible := Valuation.Compatible.ofValuation _
  let g := (algebraMap D K).comp (algebraMap (𝓞 D) D)
  have integral (x : 𝓞 D) : g x ∈ 𝒪[K] := by
    change ValuativeRel.valuation K (g x) ≤ 1
    rw [← Valuation.vle_one_iff, Valuation.vle_one_iff (Valued.v : Valuation K ℤᵐ⁰)]
    change Valued.v ((algebraMap D (v.adicCompletion D)) (x : D)) ≤ 1
    exact (v.valuedAdicCompletion_eq_valuation' (x : D)).le.trans (v.valuation_le_one x)
  let intoIntegers := g.codRestrict 𝒪[K] integral
  exact ⟨Units.map intoIntegers.toMonoidHom u, rfl⟩

