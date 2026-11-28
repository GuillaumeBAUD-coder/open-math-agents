import OMAReductions.R_LatinTableau_SimpleGraph_LatinTableauConjecture_R1

-- Step LatinTableau.SimpleGraph.LatinTableauConjecture.R1.H1: hypothesis H1 of reduction LatinTableau.SimpleGraph.LatinTableauConjecture.R1
-- Credit: @yhay81
-- H1 := ∀ (μ : YoungDiagram) (a b : ℕ), (∀ c : ℕ × ℕ, c ∈ μ ↔ c.1 < a ∧ c.2 < b) →     μ.toSimpleGraph.CDSColorable

private lemma eq_of_add_mod_eq {x y z t : ℕ} (hy : y < t) (hz : z < t)
    (h : (x + y) % t = (x + z) % t) : y = z := by
  have h1 : t * ((x + y) / t) + (x + y) % t = x + y := Nat.div_add_mod (x + y) t
  have h2 : t * ((x + z) / t) + (x + z) % t = x + z := Nat.div_add_mod (x + z) t
  rcases lt_trichotomy ((x + y) / t) ((x + z) / t) with hlt | heq | hgt
  · have hle : (x + y) / t + 1 ≤ (x + z) / t := hlt
    have : t * ((x + y) / t + 1) ≤ t * ((x + z) / t) := Nat.mul_le_mul_left t hle
    nlinarith
  · rw [heq, h] at h1
    omega
  · have hle : (x + z) / t + 1 ≤ (x + y) / t := hgt
    have : t * ((x + z) / t + 1) ≤ t * ((x + y) / t) := Nat.mul_le_mul_left t hle
    nlinarith

private lemma add_sub_mod_eq {i r t : ℕ} (hi : i < t) (hr : r < t) :
    (i + (r + t - i) % t) % t = r := by
  rw [Nat.add_mod_mod]
  have hsum : i + (r + t - i) = r + t := by omega
  rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hr]

private lemma rect_mem_bounds {μ : YoungDiagram} {a b : ℕ}
    (hμ : ∀ c : ℕ × ℕ, c ∈ μ ↔ c.1 < a ∧ c.2 < b) (c : μ.Cell) :
    c.val.1 < a ∧ c.val.2 < b :=
  (hμ c.val).mp c.prop

private def rectColoring (μ : YoungDiagram) (a b : ℕ)
    (hμ : ∀ c : ℕ × ℕ, c ∈ μ ↔ c.1 < a ∧ c.2 < b) :
    μ.toSimpleGraph.Coloring ℕ :=
  SimpleGraph.Coloring.mk (fun c => (c.val.1 + c.val.2) % max a b) <| by
    intro u v hadj hcol
    rw [YoungDiagram.toSimpleGraph, SimpleGraph.fromRel_adj] at hadj
    rcases hadj with ⟨hne, hrc | hrc⟩
    · rcases hrc with h1 | h2
      · have hu := rect_mem_bounds hμ u
        have hv := rect_mem_bounds hμ v
        rw [h1] at hcol
        have heq2 : u.val.2 = v.val.2 :=
          eq_of_add_mod_eq (lt_of_lt_of_le hu.2 (le_max_right a b))
            (lt_of_lt_of_le hv.2 (le_max_right a b)) hcol
        exact hne (Subtype.ext (Prod.ext h1 heq2))
      · have hu := rect_mem_bounds hμ u
        have hv := rect_mem_bounds hμ v
        rw [h2, Nat.add_comm u.val.1 v.val.2, Nat.add_comm v.val.1 v.val.2] at hcol
        have heq1 : u.val.1 = v.val.1 :=
          eq_of_add_mod_eq (lt_of_lt_of_le hu.1 (le_max_left a b))
            (lt_of_lt_of_le hv.1 (le_max_left a b)) hcol
        exact hne (Subtype.ext (Prod.ext heq1 h2))
    · rcases hrc with h1 | h2
      · have hu := rect_mem_bounds hμ u
        have hv := rect_mem_bounds hμ v
        rw [h1] at hcol
        have heq2 : u.val.2 = v.val.2 :=
          eq_of_add_mod_eq (lt_of_lt_of_le hu.2 (le_max_right a b))
            (lt_of_lt_of_le hv.2 (le_max_right a b)) hcol
        exact hne (Subtype.ext (Prod.ext h1.symm heq2))
      · have hu := rect_mem_bounds hμ u
        have hv := rect_mem_bounds hμ v
        rw [h2, Nat.add_comm u.val.1 u.val.2, Nat.add_comm v.val.1 u.val.2] at hcol
        have heq1 : u.val.1 = v.val.1 :=
          eq_of_add_mod_eq (lt_of_lt_of_le hu.1 (le_max_left a b))
            (lt_of_lt_of_le hv.1 (le_max_left a b)) hcol
        exact hne (Subtype.ext (Prod.ext heq1 h2.symm))

private lemma card_colorClass_rect (μ : YoungDiagram) (a b : ℕ)
    (hμ : ∀ c : ℕ × ℕ, c ∈ μ ↔ c.1 < a ∧ c.2 < b) (r : ℕ) :
    ((rectColoring μ a b hμ).colorClass r).ncard = if r < max a b then min a b else 0 := by
  by_cases hr : r < max a b
  · rw [if_pos hr, ← Nat.card_coe_set_eq]
    rcases le_total a b with hab | hba
    · have hmin : min a b = a := min_eq_left hab
      have hmax : max a b = b := max_eq_right hab
      rw [hmin]
      have hrb : r < b := hmax ▸ hr
      have hbpos : 0 < b := lt_of_le_of_lt (Nat.zero_le _) hrb
      let e : Fin a ≃ ↑((rectColoring μ a b hμ).colorClass r) :=
        { toFun := fun i =>
            ⟨⟨(i.val, (r + b - i.val) % b),
              (hμ _).mpr ⟨i.isLt, Nat.mod_lt _ hbpos⟩⟩, by
              change (i.val + (r + b - i.val) % b) % max a b = r
              rw [hmax]
              exact add_sub_mod_eq (lt_of_lt_of_le i.isLt hab) hrb⟩
          invFun := fun x => ⟨x.val.val.1, (rect_mem_bounds hμ x.val).1⟩
          left_inv := fun i => Fin.ext rfl
          right_inv := fun x => by
            apply Subtype.ext
            apply Subtype.ext
            apply Prod.ext
            · rfl
            · have hx := rect_mem_bounds hμ x.val
              have hcol : (x.val.val.1 + x.val.val.2) % b = r := by
                have hc : (x.val.val.1 + x.val.val.2) % max a b = r := x.prop
                rwa [hmax] at hc
              have hcol' : (x.val.val.1 + (r + b - x.val.val.1) % b) % b = r :=
                add_sub_mod_eq (lt_of_lt_of_le hx.1 hab) hrb
              exact eq_of_add_mod_eq (Nat.mod_lt _ hbpos) hx.2 (hcol'.trans hcol.symm) }
      rw [Nat.card_congr e.symm, Nat.card_fin]
    · have hmin : min a b = b := min_eq_right hba
      have hmax : max a b = a := max_eq_left hba
      rw [hmin]
      have hra : r < a := hmax ▸ hr
      have hapos : 0 < a := lt_of_le_of_lt (Nat.zero_le _) hra
      let e : Fin b ≃ ↑((rectColoring μ a b hμ).colorClass r) :=
        { toFun := fun j =>
            ⟨⟨((r + a - j.val) % a, j.val),
              (hμ _).mpr ⟨Nat.mod_lt _ hapos, j.isLt⟩⟩, by
              change ((r + a - j.val) % a + j.val) % max a b = r
              rw [hmax, Nat.add_comm]
              exact add_sub_mod_eq (lt_of_lt_of_le j.isLt hba) hra⟩
          invFun := fun x => ⟨x.val.val.2, (rect_mem_bounds hμ x.val).2⟩
          left_inv := fun j => Fin.ext rfl
          right_inv := fun x => by
            apply Subtype.ext
            apply Subtype.ext
            apply Prod.ext
            · have hx := rect_mem_bounds hμ x.val
              have hcol : (x.val.val.2 + x.val.val.1) % a = r := by
                have hc : (x.val.val.1 + x.val.val.2) % max a b = r := x.prop
                rw [hmax, Nat.add_comm] at hc
                exact hc
              have hcol' : (x.val.val.2 + (r + a - x.val.val.2) % a) % a = r :=
                add_sub_mod_eq (lt_of_lt_of_le hx.2 hba) hra
              exact eq_of_add_mod_eq (Nat.mod_lt _ hapos) hx.1 (hcol'.trans hcol.symm)
            · rfl }
      rw [Nat.card_congr e.symm, Nat.card_fin]
  · rw [if_neg hr]
    have hemp : (rectColoring μ a b hμ).colorClass r = ∅ := by
      ext c
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hc
      have hcol : (c.val.1 + c.val.2) % max a b = r := hc
      have hpos : 0 < max a b := lt_of_le_of_lt (Nat.zero_le _)
        (lt_of_lt_of_le (rect_mem_bounds hμ c).1 (le_max_left a b))
      have hlt : (c.val.1 + c.val.2) % max a b < max a b := Nat.mod_lt _ hpos
      rw [hcol] at hlt
      exact hr hlt
    rw [hemp, Set.ncard_empty]

private lemma sum_colorClass_rect (μ : YoungDiagram) (a b : ℕ)
    (hμ : ∀ c : ℕ × ℕ, c ∈ μ ↔ c.1 < a ∧ c.2 < b) (k : ℕ) :
    ∑ i < k, ((rectColoring μ a b hμ).colorClass i).ncard = min k (max a b) * min a b := by
  have hcongr : ∑ i ∈ Finset.Iio k, ((rectColoring μ a b hμ).colorClass i).ncard =
      ∑ i ∈ Finset.Iio k, if i < max a b then min a b else 0 :=
    Finset.sum_congr rfl fun i _ => card_colorClass_rect μ a b hμ i
  rw [hcongr, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  congr 1
  have hfilt : (Finset.Iio k).filter (· < max a b) = Finset.Iio (min k (max a b)) := by
    ext i
    simp [Finset.mem_filter, Finset.mem_Iio]
  rw [hfilt, Nat.card_Iio]

private lemma sum_colorClass_le_indepNumK {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (C : G.Coloring ℕ) (k : ℕ) :
    ∑ i < k, (C.colorClass i).ncard ≤ SimpleGraph.indepNumK G k := by
  let f : Fin k → Set α := fun i => C.colorClass i.val
  have hf : ∀ i, G.IsIndepSet (f i) := by
    intro i u hu v hv _ hadj
    exact C.valid hadj (hu.trans hv.symm)
  have hBdd : BddAbove {n | ∃ g : Fin k → Set α, (∀ i, G.IsIndepSet (g i)) ∧ (⋃ i, g i).ncard = n} := by
    refine ⟨Fintype.card α, ?_⟩
    rintro n ⟨g, _, rfl⟩
    rw [← Nat.card_coe_set_eq, ← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hcard : (⋃ i : Fin k, f i).ncard = ∑ i < k, (C.colorClass i).ncard := by
    have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin k)))
        (fun i : Fin k => (f i).toFinset) := by
      intro i _ j _ hij
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hxi hxj
      rw [Set.mem_toFinset] at hxi hxj
      exact hij (Fin.ext (hxi.symm.trans hxj))
    have hunion : (⋃ i : Fin k, f i).toFinset = Finset.univ.biUnion (fun i : Fin k => (f i).toFinset) := by
      ext x
      simp
    rw [Set.ncard_eq_toFinset_card', hunion, Finset.card_biUnion hdisj]
    have hsum : ∑ i : Fin k, (f i).toFinset.card = ∑ i : Fin k, (C.colorClass i.val).ncard :=
      Finset.sum_congr rfl fun i _ => (Set.ncard_eq_toFinset_card' (f i)).symm
    rw [hsum, Fin.sum_univ_eq_sum_range (fun i => (C.colorClass i).ncard) k, ← Nat.Iio_eq_range]
  exact le_csSup hBdd ⟨f, hf, hcard⟩

private lemma isIndepSet_ncard_le_min (μ : YoungDiagram) (a b : ℕ)
    (hμ : ∀ c : ℕ × ℕ, c ∈ μ ↔ c.1 < a ∧ c.2 < b) {I : Set μ.Cell}
    (hI : μ.toSimpleGraph.IsIndepSet I) :
    I.ncard ≤ min a b := by
  refine le_min ?_ ?_
  · rw [← Nat.card_coe_set_eq]
    let g : I → Fin a := fun c => ⟨c.val.val.1, (rect_mem_bounds hμ c.val).1⟩
    have hg : Function.Injective g := by
      intro u v huv
      by_contra hne
      have h1 : u.val.val.1 = v.val.val.1 := congrArg Fin.val huv
      have hne' : u.val ≠ v.val := fun h => hne (Subtype.ext h)
      have hadj : μ.toSimpleGraph.Adj u.val v.val := by
        rw [YoungDiagram.toSimpleGraph, SimpleGraph.fromRel_adj]
        exact ⟨hne', Or.inl (Or.inl h1)⟩
      exact hI u.prop v.prop hne' hadj
    have hle := Nat.card_le_card_of_injective g hg
    rwa [Nat.card_fin] at hle
  · rw [← Nat.card_coe_set_eq]
    let g : I → Fin b := fun c => ⟨c.val.val.2, (rect_mem_bounds hμ c.val).2⟩
    have hg : Function.Injective g := by
      intro u v huv
      by_contra hne
      have h2 : u.val.val.2 = v.val.val.2 := congrArg Fin.val huv
      have hne' : u.val ≠ v.val := fun h => hne (Subtype.ext h)
      have hadj : μ.toSimpleGraph.Adj u.val v.val := by
        rw [YoungDiagram.toSimpleGraph, SimpleGraph.fromRel_adj]
        exact ⟨hne', Or.inl (Or.inr h2)⟩
      exact hI u.prop v.prop hne' hadj
    have hle := Nat.card_le_card_of_injective g hg
    rwa [Nat.card_fin] at hle

private lemma card_cell_rect (μ : YoungDiagram) (a b : ℕ)
    (hμ : ∀ c : ℕ × ℕ, c ∈ μ ↔ c.1 < a ∧ c.2 < b) :
    Nat.card μ.Cell = a * b := by
  let e : μ.Cell ≃ Fin a × Fin b :=
    { toFun := fun c => (⟨c.val.1, (rect_mem_bounds hμ c).1⟩, ⟨c.val.2, (rect_mem_bounds hμ c).2⟩)
      invFun := fun p => ⟨(p.1.val, p.2.val), (hμ _).mpr ⟨p.1.isLt, p.2.isLt⟩⟩
      left_inv := fun c => Subtype.ext (Prod.ext rfl rfl)
      right_inv := fun p => Prod.ext (Fin.ext rfl) (Fin.ext rfl) }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_fin, Nat.card_fin]

private lemma indepNumK_le_rect (μ : YoungDiagram) (a b : ℕ)
    (hμ : ∀ c : ℕ × ℕ, c ∈ μ ↔ c.1 < a ∧ c.2 < b) (k : ℕ) :
    SimpleGraph.indepNumK μ.toSimpleGraph k ≤ min k (max a b) * min a b := by
  classical
  apply csSup_le
  · refine ⟨0, fun _ => ∅, fun _ _ hu => False.elim hu, ?_⟩
    simp
  · rintro n ⟨f, hf, rfl⟩
    have hmul_min : min k (max a b) * min a b = min (k * min a b) (max a b * min a b) := by
      rcases le_total k (max a b) with h | h
      · rw [min_eq_left h, min_eq_left (Nat.mul_le_mul_right _ h)]
      · rw [min_eq_right h, min_eq_right (Nat.mul_le_mul_right _ h)]
    have hmax_min : max a b * min a b = a * b := by
      rcases le_total a b with h | h
      · rw [max_eq_right h, min_eq_left h, Nat.mul_comm]
      · rw [max_eq_left h, min_eq_right h]
    rw [hmul_min, hmax_min]
    refine le_min ?_ ?_
    · have hunion : (⋃ i : Fin k, f i).toFinset = Finset.univ.biUnion (fun i : Fin k => (f i).toFinset) := by
        ext x
        simp
      rw [Set.ncard_eq_toFinset_card', hunion]
      calc (Finset.univ.biUnion (fun i : Fin k => (f i).toFinset)).card
          ≤ ∑ i : Fin k, (f i).toFinset.card := Finset.card_biUnion_le
        _ ≤ ∑ _i : Fin k, min a b := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [← Set.ncard_eq_toFinset_card']
            exact isIndepSet_ncard_le_min μ a b hμ (hf i)
        _ = k * min a b := by simp
    · rw [← Nat.card_coe_set_eq, ← card_cell_rect μ a b hμ]
      exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

theorem OMA.solution : OMA.R_LatinTableau_SimpleGraph_LatinTableauConjecture_R1.H1 := by
  intro μ a b hμ
  refine ⟨rectColoring μ a b hμ, fun k => le_antisymm ?_ ?_⟩
  · exact sum_colorClass_le_indepNumK μ.toSimpleGraph (rectColoring μ a b hμ) k
  · rw [sum_colorClass_rect μ a b hμ k]
    exact indepNumK_le_rect μ a b hμ k
