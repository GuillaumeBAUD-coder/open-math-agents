import OMAReductions.R_Erdos1070_erdos_1070_variants_matolcsi_ruzsa_varga_zsamboki_R1

-- Step Erdos1070.erdos_1070.variants.matolcsi_ruzsa_varga_zsamboki.R1.H2: hypothesis H2 of reduction Erdos1070.erdos_1070.variants.matolcsi_ruzsa_varga_zsamboki.R1
-- Credit: @smurali12
-- H2 := ∀ a b : ℕ, Erdos1070.f (a + b) ≤ Erdos1070.f a + Erdos1070.f b

open SimpleGraph
open scoped EuclideanGeometry

private lemma exists_witness (n : ℕ) :
    ∃ X : Finset ℝ², X.card = n ∧
      (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≤ Erdos1070.f n := by
  let S : Set ℕ := {m : ℕ | ∀ X : Finset ℝ², X.card = n →
    m ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum}
  let φ : ℕ → ℝ² := fun t => !₂[(t : ℝ), 0]
  have hφ : Function.Injective φ := by
    intro a b h
    have := congrArg (fun p : ℝ² => p 0) h
    simp [φ] at this
    exact_mod_cast this
  let X₀ : Finset ℝ² := (Finset.range n).image φ
  have hX₀ : X₀.card = n := by
    rw [Finset.card_image_of_injective _ hφ, Finset.card_range]
  have hbdd : BddAbove S := ⟨(UnitDistancePlaneGraph (X₀ : Set ℝ²)).indepNum, fun m hm => hm X₀ hX₀⟩
  by_contra! h
  have hmem : Erdos1070.f n + 1 ∈ S := fun X hX => Nat.succ_le_of_lt (h X hX)
  have hle : Erdos1070.f n + 1 ≤ Erdos1070.f n := le_csSup hbdd hmem
  omega

theorem OMA.solution : OMA.R_Erdos1070_erdos_1070_variants_matolcsi_ruzsa_varga_zsamboki_R1.H2 := by
  classical
  intro a b
  obtain ⟨X, hXcard, hXf⟩ := exists_witness a
  obtain ⟨Y, hYcard, hYf⟩ := exists_witness b
  let R : ℝ := 2 + (∑ x ∈ X, ‖x‖) + (∑ y ∈ Y, ‖y‖)
  have hR_nonneg : 0 ≤ R := by
    have h1 : 0 ≤ ∑ x ∈ X, ‖x‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have h2 : 0 ≤ ∑ y ∈ Y, ‖y‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  let v : ℝ² := !₂[R, 0]
  have hv_norm : ‖v‖ = R := by
    rw [EuclideanSpace.norm_eq]
    simp [v, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, Real.sqrt_sq hR_nonneg]
  let Y' : Finset ℝ² := Y.image (· + v)
  have hdist : ∀ x ∈ X, ∀ y ∈ Y, 2 ≤ dist x (y + v) := by
    intro x hx y hy
    have htri : ‖v‖ ≤ ‖x - (y + v)‖ + ‖x - y‖ := by
      calc
        ‖v‖ = ‖(x - y) - (x - (y + v))‖ := by congr 1; abel
        _ ≤ ‖x - y‖ + ‖x - (y + v)‖ := norm_sub_le _ _
        _ = ‖x - (y + v)‖ + ‖x - y‖ := add_comm _ _
    have hxy : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
    have hx_sum : ‖x‖ ≤ ∑ a ∈ X, ‖a‖ := Finset.single_le_sum (f := fun a => ‖a‖) (fun _ _ => norm_nonneg _) hx
    have hy_sum : ‖y‖ ≤ ∑ b ∈ Y, ‖b‖ := Finset.single_le_sum (f := fun b => ‖b‖) (fun _ _ => norm_nonneg _) hy
    rw [dist_eq_norm]
    linarith [hv_norm]
  have hdisj : Disjoint X Y' := by
    rw [Finset.disjoint_left]
    intro z hzX hzY'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hzY'
    have h2 := hdist _ hzX y hy
    rw [_root_.dist_self] at h2
    linarith
  have hY'card : Y'.card = b := by
    rw [Finset.card_image_of_injective Y (add_left_injective v), hYcard]
  have hUcard : (X ∪ Y').card = a + b := by
    rw [Finset.card_union_of_disjoint hdisj, hXcard, hY'card]
  let G := UnitDistancePlaneGraph ((X ∪ Y' : Finset ℝ²) : Set ℝ²)
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  have hI_indep : G.IsIndepSet (I : Set ((X ∪ Y' : Finset ℝ²) : Set ℝ²)) := hI.1
  have hI_card : I.card = G.indepNum := hI.2
  have hf_le : Erdos1070.f (a + b) ≤ I.card := by
    rw [hI_card, ← hUcard]
    exact Erdos1070.f_le (X ∪ Y')
  let I₁ := I.filter (fun p => p.1 ∈ X)
  let I₂ := I.filter (fun p => p.1 ∈ Y')
  have hI_split : I.card ≤ I₁.card + I₂.card := by
    have hsub : I ⊆ I₁ ∪ I₂ := by
      intro p hp
      have hpU : p.1 ∈ X ∪ Y' := p.2
      rcases Finset.mem_union.mp hpU with hpX | hpY'
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hpX⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hpY'⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le I₁ I₂)
  let e₁ : {p // p ∈ I₁} ↪ (X : Set ℝ²) :=
    ⟨fun p => ⟨p.1.1, Finset.mem_coe.mpr
       (Finset.mem_filter.mp (show p.1 ∈ I.filter (fun r => r.1 ∈ X) from p.2)).2⟩,
     fun p q h => Subtype.ext (Subtype.ext (congrArg (fun z : (X : Set ℝ²) => z.1) h))⟩
  let J₁ : Finset (X : Set ℝ²) := I₁.attach.map e₁
  have hJ₁_card : J₁.card = I₁.card := by
    rw [Finset.card_map, Finset.card_attach]
  have hJ₁_indep : (UnitDistancePlaneGraph (X : Set ℝ²)).IsIndepSet (J₁ : Set (X : Set ℝ²)) := by
    intro u hu w hw hne
    obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hu)
    obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hw)
    have hpq : p.1 ≠ q.1 := fun h => hne (congrArg e₁ (Subtype.ext h))
    have hpI : p.1 ∈ (I : Set ((X ∪ Y' : Finset ℝ²) : Set ℝ²)) :=
      Finset.mem_coe.mpr (Finset.mem_filter.mp (show p.1 ∈ I.filter (fun r => r.1 ∈ X) from p.2)).1
    have hqI : q.1 ∈ (I : Set ((X ∪ Y' : Finset ℝ²) : Set ℝ²)) :=
      Finset.mem_coe.mpr (Finset.mem_filter.mp (show q.1 ∈ I.filter (fun r => r.1 ∈ X) from q.2)).1
    exact hI_indep hpI hqI hpq
  have hI₁_le : I₁.card ≤ Erdos1070.f a := by
    rw [← hJ₁_card]
    exact hJ₁_indep.card_le_indepNum.trans hXf
  let e₂ : {p // p ∈ I₂} ↪ (Y : Set ℝ²) :=
    ⟨fun p => ⟨p.1.1 - v, Finset.mem_coe.mpr (by
       obtain ⟨y, hy, hy_eq⟩ := Finset.mem_image.mp
         (Finset.mem_filter.mp (show p.1 ∈ I.filter (fun r => r.1 ∈ Y') from p.2)).2
       have hsub : p.1.1 - v = y := by rw [← hy_eq, add_sub_cancel_right]
       exact hsub ▸ hy)⟩,
     fun p q h => Subtype.ext (Subtype.ext (by
       have h1 : p.1.1 - v = q.1.1 - v := congrArg (fun z : (Y : Set ℝ²) => z.1) h
       rw [← sub_add_cancel p.1.1 v, h1, sub_add_cancel]))⟩
  let J₂ : Finset (Y : Set ℝ²) := I₂.attach.map e₂
  have hJ₂_card : J₂.card = I₂.card := by
    rw [Finset.card_map, Finset.card_attach]
  have hJ₂_indep : (UnitDistancePlaneGraph (Y : Set ℝ²)).IsIndepSet (J₂ : Set (Y : Set ℝ²)) := by
    intro u hu w hw hne
    obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hu)
    obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hw)
    have hpq : p.1 ≠ q.1 := fun h => hne (congrArg e₂ (Subtype.ext h))
    have hpI : p.1 ∈ (I : Set ((X ∪ Y' : Finset ℝ²) : Set ℝ²)) :=
      Finset.mem_coe.mpr (Finset.mem_filter.mp (show p.1 ∈ I.filter (fun r => r.1 ∈ Y') from p.2)).1
    have hqI : q.1 ∈ (I : Set ((X ∪ Y' : Finset ℝ²) : Set ℝ²)) :=
      Finset.mem_coe.mpr (Finset.mem_filter.mp (show q.1 ∈ I.filter (fun r => r.1 ∈ Y') from q.2)).1
    have hadj := hI_indep hpI hqI hpq
    change Dist.dist (p.1.1 - v) (q.1.1 - v) ≠ 1
    rw [dist_sub_right]
    exact hadj
  have hI₂_le : I₂.card ≤ Erdos1070.f b := by
    rw [← hJ₂_card]
    exact hJ₂_indep.card_le_indepNum.trans hYf
  omega

