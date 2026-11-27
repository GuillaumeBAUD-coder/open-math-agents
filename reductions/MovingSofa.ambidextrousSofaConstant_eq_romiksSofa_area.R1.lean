import FormalConjectures.Wikipedia.MovingSofa

-- Inspired by The-Anh Vu-Le's public optimality proof (Apache-2.0).
-- https://github.com/vltanh/lean4-ambidextrous-sofa/tree/0f24fe48b4ca
-- The published estimates concern compact sofas and real-valued volume.
-- We prove compactness for the pinned motion model by showing that every
-- point of a sofa passes through the overlap square at some time.

open MovingSofa MeasureTheory Set Topology
open scoped EuclideanGeometry unitInterval ENNReal

namespace OMA.R_MovingSofa_ambidextrousSofaConstant_eq_romiksSofa_area_R1

def H1 : Prop := ∀ S : Set ℝ², IsCompact S → IsAmbidextrousSofa S →
  volume.real S ≤ 1 + 4 * RomiksSofa.Y ^ 2 + Real.arctan RomiksSofa.Y

def H2 : Prop := ∃ S : Set ℝ², IsAmbidextrousSofa S ∧
  volume.real S = 1 + 4 * RomiksSofa.Y ^ 2 + Real.arctan RomiksSofa.Y

lemma horizontal_mem (p : ℝ²) : p ∈ horizontalHallway ↔
    p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 := by
  constructor
  · rintro ⟨x,y,h,rfl⟩
    exact h
  · intro h
    exact ⟨p 0,p 1,h,by ext i; fin_cases i <;> rfl⟩

lemma vertical_mem (p : ℝ²) : p ∈ verticalHallway ↔
    0 ≤ p 0 ∧ p 0 ≤ 1 ∧ p 1 ≤ 1 := by
  constructor
  · rintro ⟨x,y,h,rfl⟩
    exact h
  · intro h
    exact ⟨p 0,p 1,h,by ext i; fin_cases i <;> rfl⟩

lemma motion_compact {s : Set ℝ²} {m : I → E(2)} (h : IsMovingSofa s m) : IsCompact s := by
  let f (t : I) := (m t).toAffineIsometry.toContinuousAffineMap
  have hf : Continuous f := continuous_induced_dom.comp h.continuous
  let e := ContinuousAffineMap.decompLinearIsometryEquiv ℝ ℝ ℝ² ℝ²
  have hd := e.continuous.comp hf
  have traj (p : ℝ²) : Continuous (fun t => m t p) := by
    have hlin := ((ContinuousLinearMap.apply ℝ ℝ² p).continuous.comp hd.snd).add hd.fst
    exact hlin.congr (fun t => (congrFun (f t).decomp p).symm)
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn (traj 0).continuousOn
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨h.isClosed, isBounded_iff_forall_norm_le.mpr ⟨C + 2, ?_⟩⟩
  intro p hp
  let A := {t : I | m t p ∈ horizontalHallway}
  let B := {t : I | m t p ∈ verticalHallway}
  have coord (i : Fin 2) : Continuous (fun t => (m t p) i) :=
    (PiLp.continuous_apply 2 _ i).comp (traj p)
  have hA : IsClosed A := by
    simp only [A, horizontal_mem]
    exact (isClosed_le (coord 0) continuous_const).inter
      ((isClosed_le continuous_const (coord 1)).inter (isClosed_le (coord 1) continuous_const))
  have hB : IsClosed B := by
    simp only [B, vertical_mem]
    exact (isClosed_le continuous_const (coord 0)).inter
      ((isClosed_le (coord 0) continuous_const).inter (isClosed_le (coord 1) continuous_const))
  obtain ⟨t, -, htA, htB⟩ := isPreconnected_closed_iff.mp (isPreconnected_univ (α := I))
    A B hA hB (fun t _ => h.subset_hallway t ⟨p,hp,rfl⟩)
    ⟨0, trivial, show m 0 p ∈ horizontalHallway by rw [h.zero]; exact h.initial hp⟩
    ⟨1, trivial, h.final ⟨p,hp,rfl⟩⟩
  have h₀ := (vertical_mem _).mp htB
  have h₁ := (horizontal_mem _).mp htA
  have hm : ‖m t p‖ ≤ 2 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_le_iff]
    simp only [Real.norm_eq_abs, sq_abs]
    refine ⟨by norm_num, ?_⟩
    nlinarith [mul_nonneg h₀.1 (sub_nonneg.mpr h₀.2.1),
      mul_nonneg h₁.2.1 (sub_nonneg.mpr h₁.2.2), h₀.2.1, h₁.2.2]
  calc ‖p‖ = dist (m t p) (m t 0) := by rw [(m t).isometry.dist_eq, dist_zero_right]
       _ ≤ ‖m t p‖ + ‖m t 0‖ := dist_le_norm_add_norm _ _
       _ ≤ _ := by linarith [hC t (mem_univ t)]

lemma area_eq : RomiksSofa.area = 1 + 4 * RomiksSofa.Y ^ 2 + Real.arctan RomiksSofa.Y := by
  have hy : RomiksSofa.Y * (4 * RomiksSofa.Y ^ 2 + 3) = 1 :=
    RomiksSofa.existsUnique_Y.exists.choose_spec
  have hx : (1 + 4 * RomiksSofa.Y ^ 2) ^ 2 * ((1 + 4 * RomiksSofa.Y ^ 2) + 3) = 8 := by
    linear_combination 4 * (RomiksSofa.Y * (4 * RomiksSofa.Y ^ 2 + 3) + 1) * hy
  unfold RomiksSofa.area RomiksSofa.X
  rw [RomiksSofa.existsUnique_X.unique RomiksSofa.existsUnique_X.exists.choose_spec hx]

theorem main : H1 → H2 → type_of% @MovingSofa.ambidextrousSofaConstant_eq_romiksSofa_area := by
  intro upper ⟨S,hS,harea⟩
  rw [area_eq]
  apply le_antisymm
  · apply iSup₂_le
    intro T hT
    obtain ⟨m,hm⟩ := hT.1
    have compact := motion_compact hm
    have hvol := ENNReal.ofReal_le_ofReal (upper T compact hT)
    rwa [Measure.real, ENNReal.ofReal_toReal compact.measure_lt_top.ne] at hvol
  · rw [← harea]
    exact (ENNReal.ofReal_toReal_le).trans (le_iSup₂ (α := ℝ≥0∞) S hS)
end OMA.R_MovingSofa_ambidextrousSofaConstant_eq_romiksSofa_area_R1
