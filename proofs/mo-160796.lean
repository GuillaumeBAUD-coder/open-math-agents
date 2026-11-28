import OMAStatements.S_mo_160796
import Mathlib

/-!
MathOverflow 160796: induction on the generated Dynkin system, proving measurability together
with `μ U = ν U` (complements by `prob_compl_eq_one_sub`, disjoint unions by `measure_iUnion`).
This is the standard argument behind the answer of Bjørn Kjos-Hanssen.
-/

namespace OMA.P160796

open MeasureTheory Set OMA.S_mo_160796

theorem proof_aux : ∀ (α : Type) [MeasurableSpace α] (base : Set (Set α)),
    (∀ U ∈ base, MeasurableSet U) →
    ∀ μ ν : Measure α, ∀ [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
    (∀ U ∈ base, μ U = ν U) → ∀ U, GeneratedDynkin base U → μ U = ν U := by
  intro α _ base hb μ ν _ _ hμν U hU
  suffices MeasurableSet U ∧ μ U = ν U from this.2
  induction hU with
  | basic h => exact ⟨hb _ h, hμν _ h⟩
  | whole => exact ⟨MeasurableSet.univ, by simp⟩
  | complement _ ih =>
    exact ⟨ih.1.compl, by rw [prob_compl_eq_one_sub ih.1, prob_compl_eq_one_sub ih.1, ih.2]⟩
  | union hd _ ih =>
    refine ⟨MeasurableSet.iUnion fun i => (ih i).1, ?_⟩
    rw [measure_iUnion hd fun i => (ih i).1, measure_iUnion hd fun i => (ih i).1]
    exact tsum_congr fun i => (ih i).2

end OMA.P160796

theorem OMA.solution : type_of% @OMA.S_mo_160796.main := OMA.P160796.proof_aux
