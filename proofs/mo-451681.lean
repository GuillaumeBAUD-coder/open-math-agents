import OMAStatements.S_mo_451681
import Mathlib

open Set
open scoped Topology Manifold ContDiff

open OMA.S_mo_451681

private theorem image_of_open_is_borel {X Y : Type}
    [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hf : Continuous f) {U : Set X} (hU : IsOpen U) :
    MeasurableSet (f '' U) := by
  let _ : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hSigma : IsSigmaCompact (Set.univ : Set U) :=
    isSigmaCompact_univ_iff.mpr inferInstance
  obtain ⟨K,hK,hCover⟩ := hSigma
  have hF : Continuous (fun x : U => f x.val) := hf.comp continuous_subtype_val
  have he : (fun x : U => f x.val) '' (Set.univ : Set U) = f '' U := by
    ext y
    constructor
    · rintro ⟨x,_,rfl⟩
      exact ⟨x.val,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,Set.mem_univ _,rfl⟩
  rw [←he,←hCover,Set.image_iUnion]
  exact MeasurableSet.iUnion (fun n => ((hK n).image hF).isClosed.measurableSet)

theorem OMA.solution : type_of% @OMA.S_mo_451681.main := by
  intro E E' _ _ _ _ _ _ M N _ _ _ _ _ _ _ _ _ _ _ _ f hf U hU
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  exact image_of_open_is_borel hf.continuous hU
