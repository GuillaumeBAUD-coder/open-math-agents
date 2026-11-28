import FormalConjectures.ErdosProblems.«1069»

/-! Rows and columns are the level sets of the two coordinate projections on the grid. -/

open EuclideanGeometry

private def coords (u : Fin 2 → ℝ) : ℝ² := WithLp.toLp 2 u

private noncomputable abbrev project (i : Fin 2) : ℝ² →ₗ[ℝ] ℝ := EuclideanSpace.projₗ i

private noncomputable def axis (i : Fin 2) (r : ℝ) : AffineSubspace ℝ ℝ² :=
  AffineSubspace.mk' (coords fun _ => r) (project i).ker

private lemma mem_axis (i : Fin 2) (r : ℝ) (p : ℝ²) : p ∈ axis i r ↔ p i = r := by
  rw [axis, AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, map_sub]
  exact sub_eq_zero

private lemma axis_line (i : Fin 2) (r : ℝ) : IsLine (axis i r) := by
  have surj : Function.Surjective (project i) := fun y => ⟨coords (fun _ => y), rfl⟩
  have rank := (project i).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr surj, finrank_top, Module.finrank_self,
    finrank_euclideanSpace, Fintype.card_fin] at rank
  unfold IsLine axis
  rw [AffineSubspace.direction_mk']
  omega

private lemma rev_ne (i : Fin 2) : i.rev ≠ i := by
  fin_cases i <;> decide

theorem OMA.solution : type_of% @Erdos1069.erdos_1069.variants.lattice := by
  classical
  intro m hm
  let point (u : Fin 2 → Fin m) := coords (fun i => ((u i).val : ℝ))
  have hinj : Function.Injective point := by
    intro u v huv
    funext i
    exact Fin.ext (Nat.cast_injective (congrArg (fun p : ℝ² => p i) huv))
  let grid := Finset.univ.image point
  refine ⟨grid, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj]
    simp
  let line (u : Fin 2 × Fin m) := axis u.1 u.2.val
  have linj : Function.Injective line := by
    rintro ⟨i, u⟩ ⟨j, v⟩ h
    have test (y : ℝ) : (if j = i then (u.val : ℝ) else y) = (v.val : ℝ) := by
      let p := coords (fun t => if t = i then (u.val : ℝ) else y)
      have hu : p ∈ line (i, u) := (mem_axis i _ p).mpr (by simp [p, coords])
      have hv : p ∈ line (j, v) := h ▸ hu
      exact (mem_axis j _ p).mp hv
    by_cases hji : j = i
    · subst j
      have hv := test 0
      rw [if_pos rfl] at hv
      exact Prod.ext rfl (Fin.ext (by exact_mod_cast hv))
    · have a := test 0
      have b := test 1
      simp [hji] at a b
      linarith
  have subset : Set.range line ⊆ Erdos1069.richLines grid m := by
    rintro _ ⟨⟨i, u⟩, rfl⟩
    refine ⟨axis_line _ _, ?_⟩
    let row (v : Fin m) (j : Fin 2) := if j = i then u else v
    have rinj : Function.Injective row := by
      intro v w h
      simpa [row, rev_ne] using congrFun h i.rev
    have included : Set.range (point ∘ row) ⊆ (grid : Set ℝ²) ∩ (line (i, u) : Set ℝ²) := by
      rintro _ ⟨v, rfl⟩
      exact ⟨Finset.mem_image.mpr ⟨row v, Finset.mem_univ _, rfl⟩,
        (mem_axis i _ _).mpr (by simp [point, row, coords, PiLp.toLp_apply])⟩
    have hc := Set.ncard_le_ncard included ((Finset.finite_toSet grid).inter_of_left _)
    rwa [Set.ncard_range_of_injective (hinj.comp rinj), Nat.card_eq_fintype_card,
      Fintype.card_fin] at hc
  have hc := Set.ncard_le_ncard subset (Erdos1069.richLines_finite grid hm)
  rwa [Set.ncard_range_of_injective linj, Nat.card_eq_fintype_card,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hc
