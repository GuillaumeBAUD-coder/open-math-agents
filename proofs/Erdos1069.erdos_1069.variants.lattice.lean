import FormalConjectures.ErdosProblems.«1069»

-- Problem: Erdős Problem 1069 — lattice
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1069.lean:75 (declaration Erdos1069.erdos_1069.variants.lattice)
-- Credit: @quantdev343 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open EuclideanGeometry

namespace OMALattice

noncomputable def pt (x y : ℝ) : ℝ² := !₂[x, y]

@[simp] lemma pt_zero (x y : ℝ) : pt x y 0 = x := rfl
@[simp] lemma pt_one (x y : ℝ) : pt x y 1 = y := rfl

lemma ext2 (p q : ℝ²) (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  ext i
  fin_cases i <;> assumption

noncomputable def V (x : ℝ) : AffineSubspace ℝ ℝ² :=
  AffineSubspace.mk' (pt x 0) (Submodule.span ℝ {pt 0 1})

noncomputable def H (y : ℝ) : AffineSubspace ℝ ℝ² :=
  AffineSubspace.mk' (pt 0 y) (Submodule.span ℝ {pt 1 0})

lemma mem_V (x : ℝ) (q : ℝ²) : q ∈ V x ↔ q 0 = x := by
  unfold V
  rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    apply sub_eq_zero.mp
    simpa using (congrArg (fun r : ℝ² => r 0) ha).symm
  · intro h
    refine ⟨q 1, ext2 _ _ ?_ ?_⟩ <;> simp [h]

lemma mem_H (y : ℝ) (q : ℝ²) : q ∈ H y ↔ q 1 = y := by
  unfold H
  rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    apply sub_eq_zero.mp
    simpa using (congrArg (fun r : ℝ² => r 1) ha).symm
  · intro h
    refine ⟨q 0, ext2 _ _ ?_ ?_⟩ <;> simp [h]

lemma pt_ne_zero_01 : pt 0 1 ≠ 0 := by
  intro h
  simpa using congrArg (fun r : ℝ² => r 1) h

lemma pt_ne_zero_10 : pt 1 0 ≠ 0 := by
  intro h
  simpa using congrArg (fun r : ℝ² => r 0) h

lemma isLine_V (x : ℝ) : IsLine (V x) := by
  unfold IsLine V
  rw [AffineSubspace.direction_mk']
  exact finrank_span_singleton pt_ne_zero_01

lemma isLine_H (y : ℝ) : IsLine (H y) := by
  unfold IsLine H
  rw [AffineSubspace.direction_mk']
  exact finrank_span_singleton pt_ne_zero_10

noncomputable def grid (m : ℕ) : Finset ℝ² :=
  (Finset.univ : Finset (Fin m × Fin m)).image fun ij => pt (ij.1 : ℕ) (ij.2 : ℕ)

lemma pt_inj {a b c d : ℝ} (h : pt a b = pt c d) : a = c ∧ b = d :=
  ⟨congrArg (fun r : ℝ² => r 0) h, congrArg (fun r : ℝ² => r 1) h⟩

lemma index_inj (m : ℕ) :
    Function.Injective (fun ij : Fin m × Fin m => pt (ij.1 : ℕ) (ij.2 : ℕ)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  obtain ⟨h1, h2⟩ := pt_inj h
  exact Prod.ext (Fin.ext (Nat.cast_inj.mp h1)) (Fin.ext (Nat.cast_inj.mp h2))

lemma grid_card (m : ℕ) : (grid m).card = m ^ 2 := by
  unfold grid
  rw [Finset.card_image_of_injective _ (index_inj m)]
  simp [sq]

-- Each coordinate slice contains an injectively indexed row or column of the grid.
lemma rich_slice (m : ℕ) (A : AffineSubspace ℝ ℝ²) (f : Fin m ↪ Fin m × Fin m)
    (hA : ∀ j, pt ((f j).1 : ℕ) ((f j).2 : ℕ) ∈ A) :
    m ≤ (((grid m : Finset ℝ²) : Set ℝ²) ∩ (A : Set ℝ²)).ncard := by
  let point (j : Fin m) := pt ((f j).1 : ℕ) ((f j).2 : ℕ)
  have included : Set.range point ⊆ ((grid m : Finset ℝ²) : Set ℝ²) ∩ (A : Set ℝ²) := by
    rintro _ ⟨j, rfl⟩
    refine ⟨?_, hA j⟩
    simp only [grid, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact ⟨f j, rfl⟩
  have injective : Function.Injective point := (index_inj m).comp f.injective
  calc m = (Set.range point).ncard := by
        rw [Set.ncard_range_of_injective injective, Nat.card_eq_fintype_card, Fintype.card_fin]
    _ ≤ _ := Set.ncard_le_ncard included ((Finset.finite_toSet _).inter_of_left _)

noncomputable def L (m : ℕ) : Fin m ⊕ Fin m → AffineSubspace ℝ ℝ²
  | Sum.inl i => V (i : ℕ)
  | Sum.inr j => H (j : ℕ)

lemma L_inj (m : ℕ) : Function.Injective (L m) := by
  rintro (a | a) (b | b) h <;> simp only [L] at h
  · have : pt (a : ℕ) 0 ∈ V (b : ℕ) := h ▸ (mem_V _ _).2 (by simp)
    rw [mem_V] at this
    simp only [pt_zero, Nat.cast_inj] at this
    rw [Fin.ext this]
  · exfalso
    have h1 : pt (a : ℕ) ((b : ℕ) + 1) ∈ H (b : ℕ) := h ▸ (mem_V _ _).2 (by simp)
    rw [mem_H] at h1
    simp at h1
  · exfalso
    have h1 : pt ((b : ℕ) + 1) (a : ℕ) ∈ V (b : ℕ) := h ▸ (mem_H _ _).2 (by simp)
    rw [mem_V] at h1
    simp at h1
  · have : pt 0 (a : ℕ) ∈ H (b : ℕ) := h ▸ (mem_H _ _).2 (by simp)
    rw [mem_H] at this
    simp only [pt_one, Nat.cast_inj] at this
    rw [Fin.ext this]

end OMALattice

open OMALattice

theorem OMA.solution : type_of% @Erdos1069.erdos_1069.variants.lattice := by
  intro m hm
  refine ⟨grid m, grid_card m, ?_⟩
  have hsub : Set.range (L m) ⊆ Erdos1069.richLines (grid m) m := by
    rintro _ ⟨(i | j), rfl⟩
    · refine ⟨isLine_V _, ?_⟩
      exact rich_slice m _ ⟨fun j => (i, j), fun _ _ h => congrArg Prod.snd h⟩
        (fun _ => (mem_V _ _).2 rfl)
    · refine ⟨isLine_H _, ?_⟩
      exact rich_slice m _ ⟨fun i => (i, j), fun _ _ h => congrArg Prod.fst h⟩
        (fun _ => (mem_H _ _).2 rfl)
  calc 2 * m = (Set.range (L m)).ncard := by
        rw [Set.ncard_range_of_injective (L_inj m), Nat.card_eq_fintype_card,
          Fintype.card_sum, Fintype.card_fin]
        ring
    _ ≤ _ := Set.ncard_le_ncard hsub (Erdos1069.richLines_finite _ hm)
