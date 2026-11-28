import OMAStatements.S_mo_426045

open OMA.S_mo_426045 Metric Set

variable {X : Type} [MetricSpace X]

private theorem tube_of_error {K : Set X} {s ε : ℝ} {f : X → ℝ} {x : X}
    (h : UniformError K ε f) (hx : f x ≤ s) : infDist x K < s+ε := by
  obtain ⟨δ,hδ,herr⟩ := h
  linarith [(abs_le.mp (herr x)).1]

private theorem tube_witness (K : Set X) {s ε : ℝ}
    (hs : 0 ≤ s) (he : 0 < ε) (x : X) (hx : infDist x K < s+ε) :
    ∃ f : X → ℝ, LipschitzWith 1 f ∧ (∀ y, 0 ≤ f y) ∧
      (∀ y ∈ K, f y = 0) ∧ UniformError K ε f ∧ f x ≤ s := by
  let δ := max 0 (infDist x K - s)
  have hδ : 0 ≤ δ := le_max_left _ _
  have hδε : δ < ε := max_lt he (by linarith)
  let f (y : X) := max (infDist y K - δ) 0
  have hLip : LipschitzWith 1 (fun y : X => infDist y K - δ) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using (lipschitz_infDist_pt K).dist_le_mul y z
  refine ⟨f, hLip.max_const 0, fun y => le_max_right _ _, ?_, ?_, ?_⟩
  · intro y hy
    simp only [f, infDist_zero_of_mem hy, zero_sub]
    exact max_eq_right (neg_nonpos.mpr hδ)
  · refine ⟨δ,hδε,fun y => abs_le.mpr ⟨?_,?_⟩⟩
    · have hh : infDist y K - δ ≤ f y := le_max_left _ _
      linarith
    · have hh : f y ≤ infDist y K := max_le (by linarith) infDist_nonneg
      linarith
  · exact max_le (by linarith [le_max_right 0 (infDist x K - s)]) hs

private theorem safe_criterion (K Y : Set X) {s ε : ℝ} (hs : 0 ≤ s) (he : 0 < ε) :
    Safe K Y s ε ↔ {x | infDist x K < s+ε} ⊆ Y := by
  constructor
  · intro h x hx
    obtain ⟨f,hLip,hpos,_,herr,hfx⟩ := tube_witness K hs he x hx
    exact h f hLip.continuous.lowerSemicontinuous hpos herr ⟨x,hfx⟩ hfx
  · intro h f _ _ herr _ x hx
    exact h (tube_of_error herr hx)

theorem OMA.solution : type_of% @OMA.S_mo_426045.main := by
  intro X _ K s ε hs he
  refine ⟨fun x => ⟨tube_witness K hs he x, ?_⟩, fun Y => safe_criterion K Y hs he, ?_⟩
  · rintro ⟨f,_,_,_,herr,hfx⟩
    exact tube_of_error herr hfx
  · intro Y r hr
    have hh : r/2+r/2 = r := by ring
    simpa only [hh] using safe_criterion K Y (by positivity : 0 ≤ r/2) (by positivity : 0 < r/2)