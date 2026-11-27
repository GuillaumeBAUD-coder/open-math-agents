import OMAReductions.R_Erdos1070_erdos_1070_variants_matolcsi_ruzsa_varga_zsamboki_R1

/-! # Subadditivity of `f`

Take an `a`-point set and a `b`-point set whose unit distance graphs have independence numbers
`f a` and `f b`. Translate the second one far away: no unit distance joins the two parts, so an
independent set of the union splits into an independent set of each part.
-/

namespace OMA1070

open Finset

/-- A set of points of `Y` with no two at distance `1` is at most as large as the independence
number of the unit distance graph on `Y`. -/
lemma indep_card_le (Y T : Finset (EuclideanSpace ℝ (Fin 2))) (hTY : T ⊆ Y)
    (hT : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → dist x y ≠ 1) :
    T.card ≤ (SimpleGraph.UnitDistancePlaneGraph (Y : Set (EuclideanSpace ℝ (Fin 2)))).indepNum := by
  classical
  let s : Finset (Y : Set (EuclideanSpace ℝ (Fin 2))) :=
    T.subtype (fun x => x ∈ (Y : Set (EuclideanSpace ℝ (Fin 2))))
  have hcard : s.card = T.card := by
    rw [Finset.card_subtype]
    congr 1
    apply Finset.filter_true_of_mem
    intro x hx
    exact Finset.mem_coe.2 (hTY hx)
  rw [← hcard]
  apply SimpleGraph.IsIndepSet.card_le_indepNum
  intro v hv w hw hne hadj
  have hv' : (v : EuclideanSpace ℝ (Fin 2)) ∈ T := Finset.mem_subtype.1 (Finset.mem_coe.1 hv)
  have hw' : (w : EuclideanSpace ℝ (Fin 2)) ∈ T := Finset.mem_subtype.1 (Finset.mem_coe.1 hw)
  have hne' : (v : EuclideanSpace ℝ (Fin 2)) ≠ w := fun h => hne (Subtype.ext h)
  exact hT _ hv' _ hw' hne' hadj

/-- Some `a`-point set attains `f a`. -/
lemma exists_config (a : ℕ) : ∃ X : Finset (EuclideanSpace ℝ (Fin 2)), X.card = a ∧
    (SimpleGraph.UnitDistancePlaneGraph (X : Set (EuclideanSpace ℝ (Fin 2)))).indepNum ≤ Erdos1070.f a := by
  by_contra hcon
  push_neg at hcon
  let φ : ℕ → EuclideanSpace ℝ (Fin 2) := fun t => !₂[(t : ℝ), 0]
  have hφ : Function.Injective φ := by
    intro a b h
    have := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h
    simp [φ] at this
    exact_mod_cast this
  have hcard0 : ((Finset.range a).image φ).card = a := by
    rw [Finset.card_image_of_injective _ hφ, Finset.card_range]
  have hbdd : BddAbove {m : ℕ | ∀ X : Finset (EuclideanSpace ℝ (Fin 2)), X.card = a →
      m ≤ (SimpleGraph.UnitDistancePlaneGraph (X : Set (EuclideanSpace ℝ (Fin 2)))).indepNum} :=
    ⟨_, fun m hm => hm _ hcard0⟩
  have hmem : Erdos1070.f a + 1 ∈ {m : ℕ | ∀ X : Finset (EuclideanSpace ℝ (Fin 2)), X.card = a →
      m ≤ (SimpleGraph.UnitDistancePlaneGraph (X : Set (EuclideanSpace ℝ (Fin 2)))).indepNum} :=
    fun X hX => hcon X hX
  have hle : Erdos1070.f a + 1 ≤ Erdos1070.f a := le_csSup hbdd hmem
  omega

theorem main (a b : ℕ) : Erdos1070.f (a + b) ≤ Erdos1070.f a + Erdos1070.f b := by
  classical
  obtain ⟨A, hA, hAf⟩ := exists_config a
  obtain ⟨B, hB, hBf⟩ := exists_config b
  set R : ℝ := ∑ x ∈ A, ‖x‖ + ∑ y ∈ B, ‖y‖ + 2 with hR
  have hRnn : 0 ≤ ∑ x ∈ A, ‖x‖ + ∑ y ∈ B, ‖y‖ :=
    add_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  let v : EuclideanSpace ℝ (Fin 2) := R • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
  have hv : ‖v‖ = R := by
    show ‖R • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ = R
    rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have hsep : ∀ x ∈ A, ∀ y ∈ B, 2 ≤ dist x (y + v) := by
    intro x hx y hy
    have h1 : ‖x‖ ≤ ∑ x ∈ A, ‖x‖ :=
      Finset.single_le_sum (f := fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖)
        (fun _ _ => norm_nonneg _) hx
    have h2 : ‖y‖ ≤ ∑ y ∈ B, ‖y‖ :=
      Finset.single_le_sum (f := fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖)
        (fun _ _ => norm_nonneg _) hy
    have h3 : ‖v‖ - ‖x - y‖ ≤ ‖v - (x - y)‖ := norm_sub_norm_le _ _
    have h4 : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
    have h5 : dist x (y + v) = ‖v - (x - y)‖ := by
      rw [dist_eq_norm, ← norm_neg]
      congr 1
      abel
    rw [h5]
    linarith
  set B' : Finset (EuclideanSpace ℝ (Fin 2)) := B.image (fun y => y + v) with hB'
  have hB'card : B'.card = b := by
    rw [hB', Finset.card_image_of_injective _ (add_left_injective v), hB]
  have hdisj : Disjoint A B' := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hxB
    have := hsep _ hxA y hy
    rw [dist_self] at this
    linarith
  set X : Finset (EuclideanSpace ℝ (Fin 2)) := A ∪ B' with hX
  have hXcard : X.card = a + b := by
    rw [hX, Finset.card_union_of_disjoint hdisj, hA, hB'card]
  have hf := Erdos1070.f_le X
  rw [hXcard] at hf
  refine hf.trans ?_
  obtain ⟨s, hs⟩ :=
    (SimpleGraph.UnitDistancePlaneGraph (X : Set (EuclideanSpace ℝ (Fin 2)))).exists_isNIndepSet_indepNum
  rw [← hs.card_eq]
  set sv : Finset (EuclideanSpace ℝ (Fin 2)) := s.image Subtype.val with hsv
  have hsvcard : sv.card = s.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hsvX : ∀ x ∈ sv, x ∈ X := by
    intro x hx
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_coe.1 w.property
  have hsvind : ∀ x ∈ sv, ∀ y ∈ sv, x ≠ y → dist x y ≠ 1 := by
    intro x hx y hy hne hd
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
    have hwz : w ≠ z := fun h => hne (by rw [h])
    exact hs.isIndepSet (Finset.mem_coe.2 hw) (Finset.mem_coe.2 hz) hwz hd
  set TA : Finset (EuclideanSpace ℝ (Fin 2)) := sv.filter (fun x => x ∈ A) with hTA
  set TB : Finset (EuclideanSpace ℝ (Fin 2)) := sv.filter (fun x => x ∈ B') with hTB
  have hsub : sv ⊆ TA ∪ TB := by
    intro x hx
    rcases Finset.mem_union.1 (hsvX x hx) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hx, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hx, h⟩)
  have hTAle : TA.card ≤ Erdos1070.f a := by
    refine le_trans (indep_card_le A TA ?_ ?_) hAf
    · intro x hx
      exact (Finset.mem_filter.1 hx).2
    · intro x hx y hy hne
      exact hsvind x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 hne
  have hTBle : TB.card ≤ Erdos1070.f b := by
    have hc : (TB.image (fun x => x - v)).card = TB.card :=
      Finset.card_image_of_injective _ (sub_left_injective (b := v))
    rw [← hc]
    refine le_trans (indep_card_le B (TB.image (fun x => x - v)) ?_ ?_) hBf
    · intro x hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hw).2
      simpa using hy
    · intro x hx y hy hne
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
      have hwz : w ≠ z := fun h => hne (by rw [h])
      rw [dist_sub_right]
      exact hsvind w (Finset.mem_filter.1 hw).1 z (Finset.mem_filter.1 hz).1 hwz
  calc s.card = sv.card := hsvcard.symm
    _ ≤ (TA ∪ TB).card := Finset.card_le_card hsub
    _ ≤ TA.card + TB.card := Finset.card_union_le _ _
    _ ≤ Erdos1070.f a + Erdos1070.f b := Nat.add_le_add hTAle hTBle

end OMA1070

theorem OMA.solution :
    OMA.R_Erdos1070_erdos_1070_variants_matolcsi_ruzsa_varga_zsamboki_R1.H2 := by
  intro a b
  exact OMA1070.main a b
