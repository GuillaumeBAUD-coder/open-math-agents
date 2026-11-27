import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1_H4_R1

-- Step PoincareConjecture.poincare_conjecture.variants.dimension_two.R1.H4.R1.H3: hypothesis H3 of reduction PoincareConjecture.poincare_conjecture.variants.dimension_two.R1.H4.R1
-- Credit: @luciusacarr
-- H3 := ∀ (k : ℕ) (w : List (Fin k × Bool)), 0 < k → w.length = 2 * k →     ¬ Subsingleton (PresentedGroup ({FreeGroup.mk w} : Set (FreeGroup (Fin k))))

lemma OMA.parity_prod {k : ℕ} (w : List (Fin k × Bool)) :
    (w.map fun x => cond x.2 (Multiplicative.ofAdd (1 : ZMod 2))
      (Multiplicative.ofAdd (1 : ZMod 2))⁻¹).prod = Multiplicative.ofAdd (w.length : ZMod 2) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [List.map_cons, List.prod_cons, ih, List.length_cons, Nat.cast_succ, add_comm,
      ofAdd_add]
    congr 1
    cases a.2 <;> rfl

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1_H4_R1.H3 := by
  intro k w hk hw hsub
  let g : Fin k → Multiplicative (ZMod 2) := fun _ => Multiplicative.ofAdd 1
  have hrel : ∀ r ∈ ({FreeGroup.mk w} : Set (FreeGroup (Fin k))), FreeGroup.lift g r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    rw [FreeGroup.lift_mk]
    refine (OMA.parity_prod w).trans ?_
    rw [hw, Nat.cast_mul]
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := rfl
    rw [h2, zero_mul, ofAdd_zero]
  have h := congrArg (PresentedGroup.toGroup hrel)
    (Subsingleton.elim (PresentedGroup.of (rels := {FreeGroup.mk w}) ⟨0, hk⟩) 1)
  rw [PresentedGroup.toGroup.of, map_one] at h
  exact absurd h (by decide)
